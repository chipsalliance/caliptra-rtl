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
#
# ---------------------------------------------------------------------------
# gen_test_vectors.py
#
# Test-vector generator for the SHA3-384 entropy combiner (entropy_combiner.sv).
#
# In combine mode the combiner concatenates the two 384-bit entropy_src seeds
# (ES0 then ES1) into a single 768-bit SHA3-384 message and returns the 384-bit
# digest to CSRNG:
#
#     digest = SHA3-384( ES0 || ES1 )
#
# Byte/endianness model (must match the RTL exactly):
#   * The combiner feeds the SHA3 core 64-bit words: ES0[63:0], ES0[127:64], ...
#     ES0[383:320], then ES1[63:0] ... ES1[383:320].
#   * The Keccak core absorbs msg_data_i[7:0] as the first (lowest) message byte
#     (see ot_sha3pad.sv). Hence each 64-bit word is little-endian in byte order,
#     i.e. the whole 384-bit seed maps to its little-endian byte string.
#   * The digest is read back as sha3_state[0][383:0]; state lane byte 0 is the
#     first output byte, so the 384-bit value is the little-endian view of the
#     SHA3-384 digest bytes.
#
# Therefore:
#     msg   = ES0.to_bytes(48,'little') + ES1.to_bytes(48,'little')
#     dg    = hashlib.sha3_384(msg).digest()        # 48 bytes
#     value = int.from_bytes(dg, 'little')           # 384-bit value on es_bits
#
# Output format (one test per line, all 96-hex-char / 384-bit big values):
#     <ES0> <ES1> <EXPECTED_DIGEST>
# consumed by entropy_combiner_tb.sv via $fscanf("%h %h %h").
# ---------------------------------------------------------------------------

import hashlib
import random
import sys

SEED_BITS = 384
SEED_BYTES = SEED_BITS // 8          # 48
SEED_MASK = (1 << SEED_BITS) - 1


def combine(es0: int, es1: int) -> int:
    """Reference model for one combine operation: SHA3-384(ES0 || ES1)."""
    msg = es0.to_bytes(SEED_BYTES, "little") + es1.to_bytes(SEED_BYTES, "little")
    dg = hashlib.sha3_384(msg).digest()
    return int.from_bytes(dg, "little")


def hx(value: int) -> str:
    """Format a 384-bit value as a fixed-width 96-char hex string."""
    return format(value & SEED_MASK, "096x")


def build_vectors(seed: int):
    random.seed(seed)
    vectors = []

    # Deterministic corner cases.
    vectors.append((0, 0))
    vectors.append((SEED_MASK, SEED_MASK))
    vectors.append((0, SEED_MASK))
    vectors.append((SEED_MASK, 0))
    vectors.append((1, 0))
    vectors.append((0, 1))
    # Recognizable byte-ramp patterns to catch word/byte-ordering bugs.
    vectors.append((int.from_bytes(bytes(range(48)), "little"),
                    int.from_bytes(bytes(range(48, 96)), "little")))
    vectors.append((int.from_bytes(bytes(range(48)), "big"),
                    int.from_bytes(bytes(range(48, 96)), "big")))

    # Randomized vectors.
    for _ in range(24):
        vectors.append((random.getrandbits(SEED_BITS),
                        random.getrandbits(SEED_BITS)))

    return vectors


def main():
    out_path = sys.argv[1] if len(sys.argv) > 1 else "entropy_combiner_test_vectors.hex"
    seed = int(sys.argv[2], 0) if len(sys.argv) > 2 else 0xC0FFEE

    vectors = build_vectors(seed)
    with open(out_path, "w") as f:
        for es0, es1 in vectors:
            f.write(f"{hx(es0)} {hx(es1)} {hx(combine(es0, es1))}\n")

    print(f"Wrote {len(vectors)} vectors to {out_path}")
    # Self-check: NIST FIPS-202 SHA3-384("") known-answer, sanity for hashlib.
    empty = hashlib.sha3_384(b"").hexdigest()
    assert empty.startswith("0c63a75b845e4f7d"), empty
    print("hashlib SHA3-384 self-check OK")


if __name__ == "__main__":
    main()
