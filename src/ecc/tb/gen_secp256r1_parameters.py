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
Generate Caliptra ECC engine Montgomery constants for secp256r1 (P-256).

The Caliptra ECC datapath is sized for the widest supported curve
(REG_SIZE = 384) and the Montgomery multiplier uses a radix-2^MULT_RADIX
serial accumulator with MULT_RADIX = 48. Per ecc_params_pkg.sv:

    FULL_REG_SIZE = (ceil(REG_SIZE / MULT_RADIX) + 1) * MULT_RADIX
                  = (ceil(384 / 48) + 1) * 48
                  = (8 + 1) * 48 = 9 * 48 = 432

so the implicit Montgomery R is **R = 2^432** for ALL curves running on
this engine, regardless of the curve's natural width (256 or 384).
Montgomery µ is taken modulo 2^MULT_RADIX = 2^48.

The script prints constants in the exact SystemVerilog parameter form
used in src/ecc/rtl/ecc_params_pkg.sv (lines ~113..127). They should
match byte-for-byte when REG_SIZE=384, MULT_RADIX=48.
"""

# --- secp256r1 (NIST P-256) parameters ---
p  = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
n  = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
b  = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
Gx = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
Gy = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
a  = p - 3

# --- Caliptra ECC engine sizing (must match ecc_params_pkg.sv) ---
REG_SIZE      = 384            # datapath width (sized for widest curve)
MULT_RADIX    = 48             # Montgomery multiplier digit width
FULL_REG_SIZE = ((REG_SIZE + MULT_RADIX - 1) // MULT_RADIX + 1) * MULT_RADIX  # = 432

R       = 1 << FULL_REG_SIZE   # Montgomery R = 2^432 (NOT 2^REG_SIZE!)
R_radix = 1 << MULT_RADIX      # 2^48 (modulus for µ)

assert FULL_REG_SIZE == 432, f"unexpected FULL_REG_SIZE={FULL_REG_SIZE}"

# --- Prime field (mod p) Montgomery params ---
ONE_p_MONT = R % p
R2_p_MONT  = (R * R) % p
E_a_MONT   = (a  * R) % p
E_b_MONT   = (b  * R) % p
E_3b_MONT  = (3 * b * R) % p
G_X_MONT   = (Gx * R) % p
G_Y_MONT   = (Gy * R) % p
PRIME_mu   = (-pow(p, -1, R_radix)) % R_radix

# --- Group-order field (mod n) Montgomery params ---
ONE_q_MONT     = R % n
R2_q_MONT      = (R * R) % n
GROUP_ORDER_mu = (-pow(n, -1, R_radix)) % R_radix

params = {
    "PRIME_P256":          (p,              REG_SIZE),
    "GROUP_ORDER_P256":    (n,              REG_SIZE),
    "E_a_MONT_P256":       (E_a_MONT,       REG_SIZE),
    "E_b_MONT_P256":       (E_b_MONT,       REG_SIZE),
    "E_3b_MONT_P256":      (E_3b_MONT,      REG_SIZE),
    "ONE_p_MONT_P256":     (ONE_p_MONT,     REG_SIZE),
    "R2_p_MONT_P256":      (R2_p_MONT,      REG_SIZE),
    "G_X_MONT_P256":       (G_X_MONT,       REG_SIZE),
    "G_Y_MONT_P256":       (G_Y_MONT,       REG_SIZE),
    "PRIME_mu_P256":       (PRIME_mu,       MULT_RADIX),
    "ONE_q_MONT_P256":     (ONE_q_MONT,     REG_SIZE),
    "R2_q_MONT_P256":      (R2_q_MONT,      REG_SIZE),
    "GROUP_ORDER_mu_P256": (GROUP_ORDER_mu, MULT_RADIX),
}

# Print in SystemVerilog parameter form. Hex width follows the data width
# (256 nibbles for natural P-256 values; the 384-bit slots in the pkg
# zero-extend the high 128 bits in the RTL via a concat).
for name, (val, bits) in params.items():
    natural_bits = 256 if bits == REG_SIZE else bits
    hex_width = natural_bits // 4
    print(f"  parameter {name:22s} = {natural_bits}'h{val:0{hex_width}X};")