#!/usr/bin/env python3
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
"""
Generate Fermat-inversion microcode for ecc_pm_sequencer.sv.

Computes z^(m-2) mod m via uniform 3-bit fixed-window left-to-right
exponentiation by squaring. Per window: 3 squarings + 1 multiply by
precompute[digit]. The first squaring of window 0 is encoded as
PRE0*PRE0 to serve as the implicit a_inv := 1 initialization.

Windows with digit=0 still emit a multiply by PRE0 (= 1) so the
sequence is fully uniform (constant-time, SCA-clean).

This script reproduces the existing P-384 INV/INVq sections in
ecc_pm_sequencer.sv exactly, and emits new P-256 chains in the same
style.
"""

import sys

# ---- Curve moduli ----
P384 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFF0000000000000000FFFFFFFF
Q384 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973
P256 = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
Q256 = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551


def emit_chain(exponent, base_label, mod_suffix, mod_name, pad_to=None):
    """
    Emit microcode lines for z^exponent mod m using 3-bit fixed window.

    base_label:  "INV_S" or "INVq_S"
    mod_suffix:  "p" or "q"  (used in uop names like UOP_DO_MUL_p)
    mod_name:    "p" or "q"  (used in comments like "% p")
    pad_to:      if set, append UOP_NOP entries to reach this total length

    Returns (list_of_lines, total_addr_count).
    """
    lines = []
    addr = 0

    do_mul = f"UOP_DO_MUL_{mod_suffix}"
    st_mul = f"UOP_ST_MUL_{mod_suffix}"
    do_add = f"UOP_DO_ADD_{mod_suffix}"
    st_add = f"UOP_ST_ADD_{mod_suffix}"

    def fmt_addr(a):
        return f"{base_label}     " if a == 0 else f"{base_label}+{a:<4d}"

    def emit(uop, opa, opb, comment=""):
        nonlocal addr
        prefix = fmt_addr(addr)
        body = f"{{{uop:14s},   {opa:18s}, {opb:18s}}}"
        line = f"                    {prefix}: douta <= {body};"
        if comment:
            line += f"    // {comment}"
        lines.append(line)
        addr += 1

    # ---- Phase 1: build precompute table z^0..z^7 ----
    one_mont = "UOP_OPR_CONST_ONE_MONT" if mod_suffix == "p" \
               else f"UOP_OPR_CONST_ONE_{mod_suffix}_MONT"
    emit(do_add, "UOP_OPR_CONST_ZERO", one_mont,
         f"precompute[0] = {one_mont} % {mod_name}")
    emit(st_add, "UOP_OPR_INV_PRE0", "UOP_OPR_DONTCARE")
    for i in range(1, 8):
        emit(do_mul, "UOP_OPR_INV_IN", f"UOP_OPR_INV_PRE{i-1}",
             f"precompute[{i}] = fp_mult(Z, precompute[{i-1}], {mod_name})")
        emit(st_mul, "UOP_OPR_DONTCARE", f"UOP_OPR_INV_PRE{i}")

    # ---- Phase 2: main loop, 3-bit windows MSB-first ----
    nbits = exponent.bit_length()
    n_windows = (nbits + 2) // 3
    total_bits = n_windows * 3   # may add leading-zero padding (0,1,2)

    for w in range(n_windows):
        # Bits covered by this window in the padded exponent (MSB-first).
        top = total_bits - 3 * w - 1     # high bit position
        bot = total_bits - 3 * (w + 1)   # low bit position
        digit = 0
        for b in range(top, bot - 1, -1):
            bit = (exponent >> b) & 1 if 0 <= b < nbits else 0
            digit = (digit << 1) | bit

        is_last_window = (w == n_windows - 1)

        # Three squarings (window-position shift).
        if w == 0:
            # Init: a_inv := PRE0 * PRE0 = 1 * 1 = 1 (substitutes for the
            # first squaring of the first window).
            emit(do_mul, "UOP_OPR_INV_PRE0", "UOP_OPR_INV_PRE0",
                 f"a_inv = fp_mult(precompute[0], precompute[0], {mod_name})")
            emit(st_mul, "UOP_OPR_DONTCARE", "UOP_OPR_A_INV")
            sq_remaining = 2
        else:
            sq_remaining = 3
        for _ in range(sq_remaining):
            emit(do_mul, "UOP_OPR_A_INV", "UOP_OPR_A_INV",
                 f"a_inv = fp_mult(a_inv, a_inv, {mod_name})")
            emit(st_mul, "UOP_OPR_DONTCARE", "UOP_OPR_A_INV")

        # Final multiply by precompute[digit].
        # Last window stores the result to INV_OUT, not A_INV.
        if is_last_window:
            emit(do_mul, "UOP_OPR_A_INV", f"UOP_OPR_INV_PRE{digit}",
                 f"INV_OUT = fp_mult(a_inv, precompute[{digit}], {mod_name})")
            emit(st_mul, "UOP_OPR_DONTCARE", "UOP_OPR_INV_OUT")
        else:
            emit(do_mul, "UOP_OPR_A_INV", f"UOP_OPR_INV_PRE{digit}",
                 f"a_inv = fp_mult(a_inv, precompute[{digit}], {mod_name})")
            emit(st_mul, "UOP_OPR_DONTCARE", "UOP_OPR_A_INV")

    # Optional NOP padding to a fixed section length.
    if pad_to is not None:
        while addr < pad_to:
            emit("UOP_NOP", "UOP_OPR_DONTCARE", "UOP_OPR_DONTCARE")

    return lines, addr


# --------------------------------------------------------------------
# Functional self-check: simulate the chain and verify it computes
# z^(m-2) mod m for a sample z.
# --------------------------------------------------------------------
def simulate_chain(z, exponent, modulus):
    """Run the same 3-bit window algorithm as the emitter, in Python."""
    pre = [pow(z, i, modulus) for i in range(8)]
    nbits = exponent.bit_length()
    n_windows = (nbits + 2) // 3
    total_bits = n_windows * 3

    a = 1  # implicit init
    for w in range(n_windows):
        top = total_bits - 3 * w - 1
        bot = total_bits - 3 * (w + 1)
        digit = 0
        for b in range(top, bot - 1, -1):
            bit = (exponent >> b) & 1 if 0 <= b < nbits else 0
            digit = (digit << 1) | bit
        # 3 squarings
        for _ in range(3):
            a = (a * a) % modulus
        # multiply by z^digit
        a = (a * pre[digit]) % modulus
    return a


def self_check(mod, name):
    z = 0x1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF
    z = z % mod
    expected = pow(z, mod - 2, mod)
    computed = simulate_chain(z, mod - 2, mod)
    ok = expected == computed
    # Also verify (z * z^-1) mod m == 1
    inv_ok = (z * computed) % mod == 1
    print(f"  {name}: chain matches pow(z, m-2, m): {ok}; (z*inv) mod m == 1: {inv_ok}")
    return ok and inv_ok


def emit_chain_to_str(exponent, base_label, mod_suffix, mod_name):
    lines, n = emit_chain(exponent, base_label, mod_suffix, mod_name)
    return "\n".join(lines), n


import re

LINE_RE = re.compile(
    r"^\s*(INV_S|INVq_S)\s*(?:\+\s*(\d+))?\s*:\s*"
    r"douta\s*<=\s*\{\s*([A-Za-z0-9_]+)\s*,\s*([A-Za-z0-9_]+)\s*,\s*([A-Za-z0-9_]+)\s*\}\s*;",
    re.MULTILINE,
)


def parse_rtl_section(path, base_label, expected_count):
    """Parse the existing sequencer's INV/INVq section into list of (uop,opa,opb) tuples."""
    with open(path) as f:
        text = f.read()
    tuples = {}
    for m in LINE_RE.finditer(text):
        lbl = m.group(1)
        if lbl != base_label:
            continue
        addr = int(m.group(2)) if m.group(2) else 0
        tuples[addr] = (m.group(3), m.group(4), m.group(5))
    return [tuples[i] for i in range(expected_count)]


def emit_tuples(exponent, base_label, mod_suffix, mod_name, pad_to=None):
    """Same as emit_chain but returns tuples instead of strings."""
    lines, _ = emit_chain(exponent, base_label, mod_suffix, mod_name, pad_to=pad_to)
    out = []
    for line in lines:
        m = LINE_RE.search(line)
        assert m, f"bad line: {line}"
        out.append((m.group(3), m.group(4), m.group(5)))
    return out


def verify_against_rtl(rtl_path):
    """Compare emitter output against existing P-384 ROM."""
    ok = True
    for label, mod, suffix, name, count in [
        ("INV_S",  P384, "p", "p", 1040),
        ("INVq_S", Q384, "q", "q", 1044),
    ]:
        rtl = parse_rtl_section(rtl_path, label, count)
        gen = emit_tuples(mod - 2, label, suffix, name, pad_to=count)
        if len(rtl) != len(gen):
            print(f"  {label}: LENGTH MISMATCH rtl={len(rtl)} gen={len(gen)}")
            ok = False
            continue
        diffs = [(i, r, g) for i, (r, g) in enumerate(zip(rtl, gen)) if r != g]
        if diffs:
            print(f"  {label}: {len(diffs)} MISMATCHES (first 10):")
            for i, r, g in diffs[:10]:
                print(f"    addr={i:4d}  rtl={r}  gen={g}")
            ok = False
        else:
            print(f"  {label}: MATCH ({count} entries)")
    return ok


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "verify":
        rtl_path = sys.argv[2] if len(sys.argv) > 2 else \
            "../rtl/ecc_pm_sequencer.sv"
        print(f"Verifying emitter against {rtl_path}")
        ok = verify_against_rtl(rtl_path)
        sys.exit(0 if ok else 1)

    if len(sys.argv) > 1 and sys.argv[1] == "selfcheck":
        print("Self-check (math): does emitted algorithm compute z^(m-2) mod m?")
        ok = True
        ok &= self_check(P384, "P-384 prime")
        ok &= self_check(Q384, "P-384 group order")
        ok &= self_check(P256, "P-256 prime")
        ok &= self_check(Q256, "P-256 group order")
        sys.exit(0 if ok else 1)

    if len(sys.argv) < 2:
        print("usage: gen_inversion_chain.py {p384|q384|p256|q256|selfcheck}")
        sys.exit(2)

    cmd = sys.argv[1]
    if cmd == "p384":
        s, n = emit_chain_to_str(P384 - 2, "INV_S",  "p", "p")
    elif cmd == "q384":
        s, n = emit_chain_to_str(Q384 - 2, "INVq_S", "q", "q")
    elif cmd == "p256":
        s, n = emit_chain_to_str(P256 - 2, "INV_S",  "p", "p")
    elif cmd == "q256":
        s, n = emit_chain_to_str(Q256 - 2, "INVq_S", "q", "q")
    else:
        print("unknown:", cmd)
        sys.exit(2)
    print(s)
    print(f"// total addresses: {n}", file=sys.stderr)
