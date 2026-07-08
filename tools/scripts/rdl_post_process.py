# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Post-processing passes for RDL-derived SystemVerilog output files.

Consumed by ``reg_gen.py`` and applied to files produced by the various
peakrdl exporters (regblock RTL, UVM RAL, coverage scaffolds).  Each
pass targets a specific subset of those files - see the **Files** field
on each pass's section header.

Every pass belongs to one of three categories:

* **upstream workaround** - patches a specific quirk in a peakrdl
  exporter that keeps its output from being accepted by downstream
  Caliptra tools (Verilator, Cadence xmvlog, lint, synthesis).  Remove
  the pass when upstream fixes the underlying behaviour.
* **caliptra addition** - adds something Caliptra needs on top of the
  generator's output (e.g. an assertion, a parameter).  Remove the
  pass when Caliptra no longer needs the added artefact.
* **permanent** - not tied to any upstream bug or Caliptra-specific
  need; safe to keep indefinitely.

Passes and their categories:

* :func:`scrub_line_by_line` (upstream workarounds) - applied to the
  regblock RTL (``{module}.sv``, ``{module}_pkg.sv``).  Dispatches to
  the callables in :data:`FIXES`; each individual fix is independently
  removable.
* :func:`inject_hwif_assertion` (caliptra addition) - applied to the
  regblock RTL (``{module}.sv``).  Inserts a ``CALIPTRA_ASSERT_KNOWN``
  X-check on ``hwif_in`` immediately before ``endmodule``.  Uses
  :func:`pick_hwif_reset` as a helper to derive the disable-condition
  reset signal from the elaborated RDL; the two are removed together.
* :func:`append_addr_width_localparam` (caliptra addition) - applied
  to the regblock package (``{module}_pkg.sv``).  Appends
  ``{ADDRMAP}_ADDR_WIDTH`` before the closing ``endpackage``.
* :func:`strip_trailing_whitespace` (permanent) - applied to every
  generated file (``{module}.sv``, ``{module}_pkg.sv``,
  ``{stem}_uvm.sv``).

Each pass docstring includes a **Category** and **Removal** line so
the deletion criteria are visible without reading the module header.

The upstream-workaround passes currently target peakrdl-regblock 1.3.1;
bump this note when re-validating against a newer release.
"""

import os
import re
from math import floor, log
from typing import Callable, List, Union

from systemrdl.node import AddrmapNode, FieldNode, SignalNode

PathLike = Union[str, os.PathLike]


# ============================================================================
# Pass: strip_trailing_whitespace
# Category: permanent
# Files:    {module}.sv, {module}_pkg.sv, {stem}_uvm.sv
# Removal:  not applicable - not tied to any upstream bug or added artefact
#           If all templates result in no redundant whitespace being emitted
#           then this could be removed, but there is no harm to run it anyway.
# ============================================================================

def strip_trailing_whitespace(fname: PathLike) -> None:
    """Strip trailing whitespace from every line of *fname*, in place.

    **Category:** permanent.  **Removal:** not applicable.
    """
    with open(fname, 'r') as f:
        lines = f.readlines()
    stripped = [line.rstrip() + '\n' for line in lines]
    with open(fname, 'w') as f:
        f.writelines(stripped)


# ============================================================================
# Pass: scrub_line_by_line
# Category: upstream workarounds (peakrdl-regblock RTL output)
# Files:    {module}.sv, {module}_pkg.sv
# Removal:  drop individual entries from FIXES (and their fix_* functions)
#           as upstream lands each fix; delete the whole pass once FIXES is
#           empty.
#
# Every fix in FIXES is a pure per-line transform: it takes one source line
# and returns the (possibly rewritten) line.  Lines containing '=' are
# skipped (procedural assignments must not be touched - see
# fix_unpacked_array_dim).  Cross-line/whole-file passes live in their own
# sections below.
# ============================================================================

# Matches `struct` optionally followed by `unpacked`.
_STRUCT_RE = re.compile(r'\bstruct\b\s*(?:unpacked)?')

# Matches a constant unpacked dimension, e.g. `[2]`.
_UNPACKED_DIM_RE = re.compile(r'\[\d+\]')

# Peels:
#   (whitespace)(existing packed dims)(identifier)(already-rewritten unpacked dims)[N]
# and folds the trailing [N] into a packed [N-1:0] on the left of the identifier.
_UNPACKED_TO_PACKED_RE = re.compile(
    r'(\s*)(\[[\w-]+:0\])*(\s*\w+)\s*(\[\d+\])*\[(\d+)\]'
)

# Matches a bare `typedef enum` with no explicit base type.
_TYPEDEF_ENUM_RE = re.compile(r'\btypedef enum\b(?!\s+logic)')


def fix_unpacked_struct(line: str) -> str:
    """Force ``struct`` declarations to be packed.

    peakrdl-regblock emits bare ``struct { ... }`` declarations.  In
    SystemVerilog a bare ``struct`` is **unpacked by default**, which
    means it cannot be bit-sliced, used as a port, or assigned with
    bitwise operators - none of which Caliptra's downstream flows
    tolerate.  Rewrite both ``struct`` and the (rarer) explicit
    ``struct unpacked`` to ``struct packed``.

    **Category:** upstream workaround.
    **Removal:** when peakrdl-regblock emits ``struct packed`` directly
    (or exposes a knob to do so).  As of 1.3.1 this still fires
    thousands of times per regeneration, so the fix is load-bearing.
    """
    if _STRUCT_RE.search(line) is None:
        return line
    return _STRUCT_RE.sub(r'struct packed', line)


def fix_unpacked_array_dim(line: str) -> str:
    """Convert unpacked array dimensions on declarations to packed.

    peakrdl-regblock writes signal/struct declarations as e.g.::

        logic NAME[2];

    which is an *unpacked* array.  Caliptra's tools require these to
    be packed::

        logic [2-1:0]NAME;

    The regex peels any existing packed dimensions, the identifier,
    and any already-rewritten unpacked dimensions, then folds the
    trailing ``[N]`` into a packed ``[N-1:0]`` on the left of the
    identifier.  A loop handles multi-dimensional cases.

    **Declarations only.**  Procedural single-bit selects such as::

        readback_data_var[0] = field_storage.CTRL0.ENDIAN_SWAP.value;

    must *not* be rewritten - doing so produces malformed
    declarations with initialisers and trips xmvlog's ``VARIST``
    warning.  ``scrub_line_by_line`` skips lines containing ``=``
    to enforce this.

    Known limitation: arrays whose identifier and dimensions are on
    separate lines are not detected.

    **Category:** upstream workaround.
    **Removal:** when peakrdl-regblock emits packed dimensions
    directly (or exposes a knob to do so).
    """
    if _UNPACKED_DIM_RE.search(line) is None:
        return line
    while _UNPACKED_DIM_RE.search(line) is not None:
        line = _UNPACKED_TO_PACKED_RE.sub(r'\1[\5-1:0]\2\3\4', line)
    return line


def fix_typedef_enum_base(line: str) -> str:
    """Force ``typedef enum`` declarations to have a 32-bit ``logic`` base.

    peakrdl-regblock emits enum typedefs as::

        typedef enum { ... } foo_e;

    A bare SystemVerilog ``enum`` defaults to ``int`` (32-bit signed
    2-state), which loses X-propagation and mismatches the 4-state
    ``logic`` signals the enum values are assigned to in the generated
    block.  Rewrite to::

        typedef enum logic [31:0] { ... } foo_e;

    Idempotent: ``typedef enum logic ...`` lines are left alone via a
    negative lookahead in :data:`_TYPEDEF_ENUM_RE`.

    **Category:** upstream workaround.
    **Removal:** when peakrdl-regblock emits an explicit base type on
    enum typedefs (or exposes a knob to do so).
    """
    if _TYPEDEF_ENUM_RE.search(line) is None:
        return line
    return _TYPEDEF_ENUM_RE.sub('typedef enum logic [31:0]', line)


# Ordered list of per-line fixes.  Drop entries as upstream lands each fix;
# delete the whole scrub pass once this list is empty.
FIXES: List[Callable[[str], str]] = [
    fix_unpacked_struct,
    fix_unpacked_array_dim,
    fix_typedef_enum_base,
]


def scrub_line_by_line(fname: PathLike) -> None:
    """Apply every per-line peakrdl-regblock workaround to *fname* in place.

    Runs each callable in :data:`FIXES` against every *declaration*
    line (lines without an ``=`` operator); procedural assignments are
    passed through untouched - see :func:`fix_unpacked_array_dim`.

    **Category:** upstream workarounds.
    **Removal:** when :data:`FIXES` is empty.
    """
    with open(fname, 'r') as f:
        lines = f.readlines()

    out: List[str] = []
    for line in lines:
        if '=' not in line:
            for fix in FIXES:
                line = fix(line)
        out.append(line)

    with open(fname, 'w') as f:
        f.writelines(out)


# ============================================================================
# Pass: inject_hwif_assertion (+ pick_hwif_reset helper)
# Category: caliptra addition
# Files:    {module}.sv
# Removal:  when the CALIPTRA_ASSERT_KNOWN on hwif_in is no longer wanted
#           (or is produced by a custom peakrdl-regblock exporter template).
#           Remove pick_hwif_reset at the same time - it exists only to
#           supply the disable-condition argument.
#
# The disable-condition signal is recovered from the elaborated RDL model
# rather than text-scanning the generated SystemVerilog for `negedge`
# clauses: every reset in the RDL is declared as
# `signal {activelow; async;} <name>;` and fields reference it via
# `resetsignal = <name>;`.
# ============================================================================

# Signal-name fragments that identify a "hard" reset.  hard_reset_b,
# error_reset_b and cptra_pwrgood are used interchangeably across the
# generated blocks; any of them is preferred over a soft reset for
# the X-check assertion's disable condition.
_HARD_RESET_RE = re.compile(r'hard_reset|pwrgood|error_reset')

# Matches a top-level `endmodule` keyword.
_ENDMODULE_RE = re.compile(r'\bendmodule\b')


def pick_hwif_reset(node: AddrmapNode) -> str:
    """Return the reset signal name to use as the disable condition.

    Prefers a "hard" reset (see :data:`_HARD_RESET_RE`) - hmac,
    for example, declares both ``reset_b`` and ``error_reset_b``;
    peakrdl-regblock emits ``always_ff`` blocks for both, and we
    want the X-check disabled during the harder of the two.

    Strategy: collect the set of distinct signals referenced by
    every field's ``resetsignal`` property (via traversal of the
    addrmap's descendants), then pick the first hard reset by name
    pattern; fall back to any reset referenced if none are "hard".

    Falling back further to ``node.signals()`` would let an
    otherwise-unused signal declaration leak in - we deliberately
    only consider signals actually wired to a field.

    **Category:** caliptra addition (helper for
    :func:`inject_hwif_assertion`).
    **Removal:** with :func:`inject_hwif_assertion`.
    """
    referenced: list[str] = []
    for child in node.descendants():
        if isinstance(child, FieldNode):
            rs = child.get_property('resetsignal')
            if isinstance(rs, SignalNode) and rs.inst_name not in referenced:
                referenced.append(rs.inst_name)
    if not referenced:
        raise RuntimeError(
            f"addrmap {node.inst_name!r} has no fields with a resetsignal; "
            "cannot derive disable condition for CALIPTRA_ASSERT_KNOWN"
        )
    for name in referenced:
        if _HARD_RESET_RE.search(name):
            return name
    return referenced[0]


def inject_hwif_assertion(fname: PathLike, reset_name: str) -> None:
    """Insert a ``CALIPTRA_ASSERT_KNOWN`` on ``hwif_in`` before ``endmodule``.

    Rewrites *fname* in place, inserting immediately before the first
    ``endmodule`` line::

        `include "caliptra_prim_assert.sv"
        `CALIPTRA_ASSERT_KNOWN(ERR_HWIF_IN, hwif_in, clk, !hwif_in.<reset_name>)

    Resets enter the module through the ``hwif_in`` input struct, so
    the assertion must reference them via that hierarchical path - the
    bare RDL signal name is not a visible identifier inside the module.
    The ``caliptra_prim_assert.sv`` include is required for the macro to
    resolve during synthesis (#1181).

    Raises ``RuntimeError`` if *fname* has no ``endmodule``.

    **Category:** caliptra addition.
    **Removal:** when the X-check on ``hwif_in`` is no longer wanted,
    or when it is produced by a custom peakrdl-regblock exporter
    template.  Remove :func:`pick_hwif_reset` at the same time.
    """
    block = (
        '\n'
        '`include "caliptra_prim_assert.sv"\n'
        f'`CALIPTRA_ASSERT_KNOWN(ERR_HWIF_IN, hwif_in, clk, !hwif_in.{reset_name})\n'
        '\n'
    )
    with open(fname, 'r') as f:
        lines = f.readlines()
    out: List[str] = []
    injected = False
    for line in lines:
        if not injected and _ENDMODULE_RE.search(line) is not None:
            out.append(block)
            injected = True
        out.append(line)
    if not injected:
        raise RuntimeError(f"no `endmodule` found in {fname}")
    with open(fname, 'w') as f:
        f.writelines(out)


# ============================================================================
# Pass: append_addr_width_localparam
# Category: caliptra addition
# Files:    {module}_pkg.sv
# Removal:  when downstream Caliptra RTL no longer consumes
#           `{ADDRMAP}_ADDR_WIDTH` (or when the parameter is produced by a
#           custom peakrdl-regblock exporter template).
# ============================================================================

# Matches a top-level `endpackage` keyword.
_ENDPACKAGE_RE = re.compile(r'\bendpackage\b')


def append_addr_width_localparam(fname: PathLike, node: AddrmapNode) -> None:
    """Append an address-width localparam to a generated ``*_pkg.sv`` file.

    ``RegblockExporter`` emits ``{addrmap_name}_pkg.sv`` without any
    parameter capturing the total address-map size.  Downstream Caliptra
    RTL wants that width available as a compile-time constant, so we
    strip the trailing ``endpackage`` from the generated file and rewrite
    it as::

        <original body>
            localparam {ADDRMAP_NAME}_ADDR_WIDTH = 32'd<N>;

        endpackage

    where ``<N>`` is ``floor(log2(node.total_size)) + 1``.

    Raises ``RuntimeError`` if the file has no ``endpackage``.

    **Category:** caliptra addition.
    **Removal:** when the ``ADDR_WIDTH`` localparam is no longer
    consumed by downstream Caliptra RTL, or when it is produced by a
    custom peakrdl-regblock exporter template.
    """
    with open(fname, 'r') as f:
        lines = f.readlines()
    kept = [line for line in lines if _ENDPACKAGE_RE.search(line) is None]
    if len(kept) == len(lines):
        raise RuntimeError(f"no `endpackage` found in {fname}")
    addr_width = int(floor(log(node.total_size, 2)) + 1)
    tail = (
        f"\n    localparam {node.inst_name.upper()}_ADDR_WIDTH = 32'd{addr_width};"
        "\n\nendpackage"
    )
    with open(fname, 'w') as f:
        f.writelines(kept)
        f.write(tail)
