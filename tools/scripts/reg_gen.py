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

r"""Generate SystemVerilog register blocks and UVM RAL models from a SystemRDL source file.

For each RDL file this script produces:
  - ``{addrmap_name}.sv``       — synthesisable register block (via peakrdl-regblock)
  - ``{addrmap_name}_pkg.sv``   — SV package with register types and an address-width localparam
  - ``{rdl_file_stem}_uvm.sv``  — UVM RAL model (via peakrdl-uvm)

The script is project-agnostic: it does not read ``$CALIPTRA_ROOT`` or any
other environment variable, and it has no hard-coded knowledge of any
specific shared RDL.  Shared-definition files (e.g. ``kv_def.rdl``) are
supplied by the caller via ``--preload FILE`` (repeatable); each preload
is ``compile_file()``d into the same ``RDLCompiler`` before the target
RDL, populating the shared root scope with the types the target
references by name.  This follows the systemrdl-compiler idiom for
shared definitions - see
https://systemrdl-compiler.readthedocs.io/en/latest/dev_notes/multi_file_compilation.html
- which explicitly discourages ``\`include`` of shared-defs files
because textual re-inclusion re-declares the same types in the shared
namespace and errors out.  ``-I/--include-dir`` remains available for
intra-file ``\`include`` fragments (e.g. ``soc_ifc_reg_properties.rdl``).

RTL outputs ({addrmap_name}.sv, {addrmap_name}_pkg.sv) are written to
``--rtl-output`` (default: same directory as the RDL file).  The UVM RAL
model ({rdl_file_stem}_uvm.sv) is written to ``--dv-output`` (default: same
directory as the RDL file).  UVM/coverage Jinja2 template directories are
supplied via ``--uvm-template-dir`` / ``--cov-template-dir`` /
``--smp-template-dir``; they are only required when the corresponding
output type is being produced.

Usage::

    python reg_gen.py <path/to/foo_reg.rdl>
        [-I INCLUDE_DIR ...] [--param NAME=VALUE ...]
        [--rtl-output DIR] [--dv-output DIR]
        [--uvm-template-dir DIR] [--cov-template-dir DIR] [--smp-template-dir DIR]
        [--emit-rtl] [--emit-dv] [--cov]

The ``--cov`` flag additionally emits ``{rdl_file_stem}_covergroups.svh`` and
``{rdl_file_stem}_sample.svh`` to ``--dv-output`` as hand-edit starting points
for functional coverage.
"""

from systemrdl import RDLCompiler, RDLCompileError
from systemrdl.node import RootNode
from peakrdl_regblock import RegblockExporter
from peakrdl_uvm import UVMExporter
from peakrdl_regblock.udps import ALL_UDPS
from peakrdl_regblock.cpuif.passthrough import PassthroughCpuif
from pathlib import Path
from typing import Optional, Union
import sys
import rdl_post_process
import argparse


def parse_params(param_args: list[str]) -> dict[str, Union[bool, int]]:
    """Parse ``NAME=VALUE`` strings into a typed dictionary.

    Supports three value types, tested in order:

    - **Boolean**: ``'true'`` or ``'false'`` (case-insensitive) → ``bool``
    - **Hexadecimal**: ``'0x'``-prefixed strings → ``int``
    - **Decimal integer**: digit strings, optionally negative → ``int``

    Values that do not match any of the above patterns are silently
    ignored and excluded from the returned dictionary.

    Args:
        param_args: List of ``'NAME=VALUE'`` strings, typically from
            argparse with ``action='append'``.

    Returns:
        Dictionary mapping parameter names to their typed values.
        Exits with code 1 if a string lacks ``'='`` or contains an
        invalid hex literal.
    """
    parameters: dict[str, Union[bool, int]] = {}
    for param in param_args:
        if '=' not in param:
            print(f"Error: Invalid parameter format '{param}'. Use NAME=VALUE")
            sys.exit(1)
        name, value = param.split('=', 1)

        if value.lower() in ['true', 'false']:
            parameters[name] = value.lower() == 'true'
        elif value.startswith('0x'):
            try:
                parameters[name] = int(value, 16)
            except ValueError:
                print(f"Error: Invalid hex value '{value}'")
                sys.exit(1)
        elif value.isdigit() or (value.startswith('-') and value[1:].isdigit()):
            parameters[name] = int(value)

    return parameters


def compile_and_elaborate(
    rdlc: RDLCompiler,
    rdl_file: Path,
    parameters: dict[str, Union[bool, int]],
    include_dirs: list[Path],
    preload_files: list[Path],
) -> RootNode:
    r"""Compile the target SystemRDL file and return the elaborated root node.

    Cross-file type dependencies (e.g. the shared ``kv_def.rdl``) are
    resolved by *preloading*: each path in *preload_files* is
    ``compile_file()``d into the same ``RDLCompiler`` before the target
    file, populating the shared root scope with the types that the
    target file references by name.  This matches the systemrdl-compiler
    idiom for shared definitions - see
    https://systemrdl-compiler.readthedocs.io/en/latest/dev_notes/multi_file_compilation.html
    - which explicitly discourages ``\`include`` of shared-defs files
    because textual re-inclusion re-declares the same types in the
    shared namespace and errors out.

    *include_dirs* is still passed to the preprocessor for any
    intra-file ``\`include`` directives that pull in source fragments
    of a single addrmap (e.g. ``soc_ifc_reg_properties.rdl``); these
    remain fine because they only ever fire inside one compile unit.

    Args:
        rdlc: A configured ``RDLCompiler`` instance with all required
            UDPs already registered.
        rdl_file: Path to the target ``.rdl`` file to compile.
        parameters: Elaboration-time parameter overrides as produced
            by :func:`parse_params`.  Pass an empty dict for defaults.
        include_dirs: Directories added to the RDL preprocessor's
            include search path.  May be empty.
        preload_files: Shared-definition RDL files to compile before
            *rdl_file*.  May be empty.

    Returns:
        Elaborated root node of the register model.
        Exits with code 1 on any ``RDLCompileError``.
    """
    # Both compile_file and elaborate can raise RDLCompileError (syntax errors and semantic violations respectively).
    try:
        for preload in preload_files:
            rdlc.compile_file(preload, incl_search_paths=[str(d) for d in include_dirs])
        rdlc.compile_file(rdl_file, incl_search_paths=[str(d) for d in include_dirs])
        return rdlc.elaborate(parameters=parameters if parameters else None)
    except RDLCompileError:
        sys.exit(1)


def emit_rtl(root: RootNode, rtl_output_dir: Path) -> None:
    """Emit the synthesisable register-block RTL and post-process it.

    ``RegblockExporter`` writes ``{addrmap_name}.sv`` and
    ``{addrmap_name}_pkg.sv`` to *rtl_output_dir*, where *addrmap_name*
    is the elaborated addrmap's ``inst_name``.  Both files are then
    mutated in place by :mod:`rdl_post_process`:

      1. ``append_addr_width_localparam`` — Caliptra-specific pkg localparam.
      2. ``scrub_line_by_line``           — peakrdl-regblock quirks (unpacked
         structs/arrays etc.) needed for Verilator/xmvlog/lint compatibility.
      3. ``inject_hwif_assertion``        — Caliptra-specific X-check on hwif_in.
      4. ``strip_trailing_whitespace``    — defence-in-depth whitespace cleanup.

    TODO: replace (2) with a custom exporter template to avoid the scrub step.
    """
    exporter = RegblockExporter()
    exporter.export(
        root, rtl_output_dir,
        cpuif_cls=PassthroughCpuif,
        retime_read_response=False,
    )

    top = root.top
    rtl_sv = rtl_output_dir / f"{top.inst_name}.sv"
    rtl_pkg = rtl_output_dir / f"{top.inst_name}_pkg.sv"
    rdl_post_process.append_addr_width_localparam(rtl_pkg, top)
    rdl_post_process.scrub_line_by_line(rtl_sv)
    rdl_post_process.scrub_line_by_line(rtl_pkg)
    rdl_post_process.inject_hwif_assertion(
        rtl_sv, rdl_post_process.pick_hwif_reset(top)
    )
    rdl_post_process.strip_trailing_whitespace(rtl_sv)
    rdl_post_process.strip_trailing_whitespace(rtl_pkg)


def emit_uvm(
    root: RootNode,
    rdl_file: Path,
    dv_output_dir: Path,
    uvm_template_dir: Path,
) -> None:
    """Emit the UVM RAL model and post-process it.

    ``{rdl_file.stem}_uvm.sv`` is written to *dv_output_dir* using the
    Jinja2 templates at *uvm_template_dir*, then whitespace-scrubbed.
    """
    uvm_out = dv_output_dir / f"{rdl_file.stem}_uvm.sv"
    exporter = UVMExporter(user_template_dir=str(uvm_template_dir))
    exporter.export(root, str(uvm_out))
    rdl_post_process.strip_trailing_whitespace(uvm_out)


def emit_coverage(
    root: RootNode,
    rdl_file: Path,
    dv_output_dir: Path,
    cov_template_dir: Path,
    smp_template_dir: Path,
) -> None:
    """Emit covergroup and sample scaffolding files.

    ``{rdl_file.stem}_covergroups.svh`` and ``{rdl_file.stem}_sample.svh``
    are generated to *dv_output_dir* from *cov_template_dir* and
    *smp_template_dir* respectively.  These files are *starting points*
    that must be hand-edited after generation; they are not produced in
    the normal CI flow.
    """
    exporter = UVMExporter(user_template_dir=str(cov_template_dir))
    exporter.export(root, str(dv_output_dir / f"{rdl_file.stem}_covergroups.svh"))
    exporter = UVMExporter(user_template_dir=str(smp_template_dir))
    exporter.export(root, str(dv_output_dir / f"{rdl_file.stem}_sample.svh"))


def main() -> None:
    """Parse arguments, compile/elaborate the RDL sources, and export all artefacts."""
    parser = argparse.ArgumentParser(description='Generate SystemVerilog registers from RDL files')
    parser.add_argument('rdl_file', help='RDL input file')
    parser.add_argument('--include-dir', '-I', action='append', default=[], metavar='DIR',
                        help='Directory added to the RDL preprocessor include search path. '
                             'Can be given multiple times.')
    parser.add_argument('--preload', action='append', default=[], metavar='FILE',
                        help='Shared-definition RDL file to compile_file() before the '
                             'target RDL.  Types declared in a preload become available '
                             'to the target via the shared root scope.  Can be given '
                             'multiple times; preloads are compiled in the order given.')
    parser.add_argument('--cov', action='store_true', help='Generate coverage files')
    parser.add_argument('--param', '-p', action='append', default=[],
                        help='Set RDL parameter (format: NAME=VALUE). Can be used multiple times.')
    parser.add_argument('--rtl-output', default=None,
                        help='Output directory for synthesisable RTL files '
                             '({addrmap}.sv, {addrmap}_pkg.sv). '
                             'Defaults to the directory containing the RDL file.')
    parser.add_argument('--dv-output', default=None,
                        help='Output directory for DV files ({stem}_uvm.sv and coverage '
                             'scaffolding). Defaults to the directory containing the RDL file.')
    parser.add_argument('--uvm-template-dir', default=None, metavar='DIR',
                        help='Jinja2 template directory for the UVM RAL model. '
                             'Required when emitting DV outputs.')
    parser.add_argument('--cov-template-dir', default=None, metavar='DIR',
                        help='Jinja2 template directory for the covergroups scaffold. '
                             'Required when --cov is given.')
    parser.add_argument('--smp-template-dir', default=None, metavar='DIR',
                        help='Jinja2 template directory for the sample scaffold. '
                             'Required when --cov is given.')
    parser.add_argument('--emit-rtl', action='store_true',
                        help='Emit the synthesisable regblock RTL.')
    parser.add_argument('--emit-dv', action='store_true',
                        help='Emit the UVM RAL model (and coverage scaffolding, if --cov).')
    args = parser.parse_args()

    # No implicit outputs: the caller must ask for at least one artefact kind.
    # Keeping this explicit lets the orchestrating shell script express, per RDL,
    # exactly which outputs are wanted (some RDLs exist purely for DV purposes).
    if not args.emit_rtl and not args.emit_dv:
        print("Error: at least one of --emit-rtl / --emit-dv must be given.")
        sys.exit(1)

    rdl_file = Path(args.rdl_file)
    default_output_dir = rdl_file.resolve().parent
    rtl_output_dir = Path(args.rtl_output) if args.rtl_output else default_output_dir
    dv_output_dir = Path(args.dv_output) if args.dv_output else default_output_dir

    rtl_output_dir.mkdir(parents=True, exist_ok=True)
    dv_output_dir.mkdir(parents=True, exist_ok=True)

    include_dirs = [Path(d) for d in args.include_dir]
    preload_files = [Path(f) for f in args.preload]

    uvm_template_dir = Path(args.uvm_template_dir) if args.uvm_template_dir else None
    cov_template_dir = Path(args.cov_template_dir) if args.cov_template_dir else None
    smp_template_dir = Path(args.smp_template_dir) if args.smp_template_dir else None

    if args.emit_dv and uvm_template_dir is None:
        print("Error: --uvm-template-dir is required when emitting DV outputs.")
        sys.exit(1)
    if args.cov and not args.emit_dv:
        print("Error: --cov requires --emit-dv (coverage scaffolding is a DV artefact).")
        sys.exit(1)
    if args.cov and (cov_template_dir is None or smp_template_dir is None):
        print("Error: --cov requires both --cov-template-dir and --smp-template-dir.")
        sys.exit(1)

    parameters = parse_params(args.param)

    rdlc = RDLCompiler()
    for udp in ALL_UDPS:
        rdlc.register_udp(udp)

    root = compile_and_elaborate(rdlc, rdl_file, parameters, include_dirs, preload_files)

    if args.emit_rtl:
        emit_rtl(root, rtl_output_dir)
    if args.emit_dv:
        assert uvm_template_dir is not None  # enforced by validation above
        emit_uvm(root, rdl_file, dv_output_dir, uvm_template_dir)
        if args.cov:
            assert cov_template_dir is not None and smp_template_dir is not None
            emit_coverage(root, rdl_file, dv_output_dir,
                          cov_template_dir, smp_template_dir)


if __name__ == '__main__':
    main()
