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
Generator for Montgomery multiplier test vectors at REG_SIZE=384, RADIX=48,
covering both P-384 (NIST R=2^384) and P-256 (engine R=2^384) operation.

Output format (matches existing ecc_montgomerymultiplier_tb.read_test_vectors):
  one test vector = 6 lines:
    line 0: a            (REG_SIZE/4 hex chars)
    line 1: b            (REG_SIZE/4 hex chars)
    line 2: n            (REG_SIZE/4 hex chars)
    line 3: n_prime      (WORD_WIDTH/4 hex chars)
    line 4: product      (REG_SIZE/4 hex chars)
    line 5: index        (decimal, used as separator only)

File name convention: mm_test_vectors_<N>_key_<REG_SIZE>_word_<WORD_WIDTH>.hex
"""

import os
import random
import sys

REG_SIZE     = 384
WORD_WIDTH   = 48
R            = 1 << REG_SIZE          # Montgomery R baked into the multiplier
RAND_PER_MOD = 30                     # random a*b per modulus
SEED         = 0xC4117004

# --- NIST P-384 ---
p384 = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff
q384 = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973

# --- NIST P-256 ---
p256 = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
q256 = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551


def neg_modinv(n, mod):
    return (-pow(n, -1, mod)) % mod


def montmul(a, b, n, n_prime, word_w=WORD_WIDTH, reg_size=REG_SIZE):
    """Reference Montgomery product: a*b*R^-1 mod n, where R = 2^reg_size."""
    word_mask = (1 << word_w) - 1
    iters     = reg_size // word_w
    assert reg_size % word_w == 0, "REG_SIZE must be a multiple of WORD_WIDTH"
    t = a * b
    for _ in range(iters):
        m = ((t & word_mask) * n_prime) & word_mask
        t = (t + m * n) >> word_w
    if t >= n:
        t -= n
    return t


def fmt_reg(v):
    return f"{v & ((1 << REG_SIZE) - 1):0{REG_SIZE // 4}x}"


def fmt_word(v):
    return f"{v & ((1 << WORD_WIDTH) - 1):0{WORD_WIDTH // 4}x}"


def rand_lt(n, rng):
    bits = n.bit_length()
    while True:
        v = rng.getrandbits(bits)
        if v < n:
            return v


def make_block(label, n, rng):
    """Generate a list of (a, b, n, n_prime, product) tuples for modulus n."""
    n_prime = neg_modinv(n, 1 << WORD_WIDTH)
    R_mod_n = R % n
    R2_mod_n = (R * R) % n
    ONE_mont = R_mod_n
    block = []

    # Directed: ONE*ONE = ONE
    block.append((ONE_mont, ONE_mont, n, n_prime, montmul(ONE_mont, ONE_mont, n, n_prime)))
    # Directed: R2 * 1 = R mod n  (raw 1 -> Mont form)
    block.append((R2_mod_n, 1, n, n_prime, montmul(R2_mod_n, 1, n, n_prime)))
    # Directed: R2 * ONE = R2 * R * R^-1 = R2
    # Actually: montmul(R2, ONE) = R2 * R * R^-1 = R2. Verify symbolically: yes.
    block.append((R2_mod_n, ONE_mont, n, n_prime, montmul(R2_mod_n, ONE_mont, n, n_prime)))
    # Directed: 0 * anything = 0
    block.append((0, ONE_mont, n, n_prime, 0))
    # Directed: (n-1)*(n-1) -- near-overflow operand stress
    nm1 = n - 1
    block.append((nm1, nm1, n, n_prime, montmul(nm1, nm1, n, n_prime)))

    # Random
    for _ in range(RAND_PER_MOD):
        a = rand_lt(n, rng)
        b = rand_lt(n, rng)
        block.append((a, b, n, n_prime, montmul(a, b, n, n_prime)))

    return label, block


def write_vectors(path, all_vectors):
    with open(path, "w") as f:
        for idx, (a, b, n, n_prime, prod) in enumerate(all_vectors):
            f.write(fmt_reg(a)     + "\n")
            f.write(fmt_reg(b)     + "\n")
            f.write(fmt_reg(n)     + "\n")
            f.write(fmt_word(n_prime) + "\n")
            f.write(fmt_reg(prod)  + "\n")
            f.write(f"{idx}\n")


def main():
    rng = random.Random(SEED)
    all_vectors = []
    for label, n in [("P384/p", p384), ("P384/q", q384),
                     ("P256/p", p256), ("P256/q", q256)]:
        _, block = make_block(label, n, rng)
        all_vectors.extend(block)
        print(f"{label:8s}: {len(block):4d} vectors", file=sys.stderr)

    n_total = len(all_vectors)
    out_dir = os.path.dirname(os.path.abspath(__file__))
    out = os.path.join(out_dir, "test_vectors",
                       f"mm_test_vectors_{n_total}_key_{REG_SIZE}_word_{WORD_WIDTH}.hex")
    write_vectors(out, all_vectors)
    print(f"Wrote {n_total} vectors to {out}", file=sys.stderr)
    print(n_total)  # stdout: total count


if __name__ == "__main__":
    main()
