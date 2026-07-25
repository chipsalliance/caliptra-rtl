# SPDX-License-Identifier: Apache-2.0

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

# http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# HMAC-DRBG-SHA256 reference model.  Mirrors `hmac_drbg_ref.py` (which uses
# SHA-384) but with the hash function fixed to SHA-256 and all widths
# narrowed to 256 bits.  Same INIT/NEXT semantics as the Caliptra RTL.

import hmac
import hashlib
import os

# secp256r1 (P-256) group order n -- used for rejection sampling in
# hmac_drbg_sha256.sv.  Match this constant to the RTL `HMAC_DRBG_PRIME`.
# Note: despite the legacy variable name, this is the P-256 *group order n*
# (FIPS 186-5 D.1.2.3), NOT the field prime p. It bounds DRBG output to
# [1, n-1] for use as the ECDSA secret scalar k.
GROUP_ORDER_P256 = int("FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551", 16)
HMAC_DRBG_PRIME  = GROUP_ORDER_P256


class HMAC_DRBG_SHA256:
    def __init__(self, entropy, nonce=b"", personalization=b""):
        """
        Instantiate HMAC-DRBG (SHA-256 variant) with entropy, nonce and
        optional personalization string (Caliptra leaves it empty).
        """
        self.hash_function = hashlib.sha256
        self.seed_length = self.hash_function().digest_size  # 32 bytes
        self.K = b"\x00" * self.seed_length
        self.V = b"\x01" * self.seed_length
        seed_material = entropy + nonce + personalization
        self.update(seed_material)

    def _hmac(self, key, data):
        return hmac.new(key, data, self.hash_function).digest()

    def update(self, seed_material=b""):
        self.K = self._hmac(self.K, self.V + b"\x00" + seed_material)
        self.V = self._hmac(self.K, self.V)
        if seed_material:
            self.K = self._hmac(self.K, self.V + b"\x01" + seed_material)
            self.V = self._hmac(self.K, self.V)

    def reseed(self, additional_entropy):
        self.update(additional_entropy)

    def generate(self, num_bytes, additional_input=b""):
        if additional_input:
            self.update(additional_input)
        output = b""
        while len(output) < num_bytes:
            self.V = self._hmac(self.K, self.V)
            output += self.V
        self.update(additional_input)
        return output[:num_bytes]


def caliptra_test(COUNT, entropy, nonce, expected0, expected1=b"", expected2=b""):
    """Mirror the Caliptra INIT/NEXT API exactly (no personalization,
    no additional input)."""
    returnedbits_len_inbyte = int(256 / 8)
    drbg = HMAC_DRBG_SHA256(entropy, nonce)
    random_bytes = drbg.generate(returnedbits_len_inbyte)
    result = (random_bytes == expected0)
    print("Caliptra INIT test number", COUNT, "=", result)
    if expected1:
        random_bytes = drbg.generate(returnedbits_len_inbyte)
        result = (random_bytes == expected1)
        print("Caliptra NEXT test number", COUNT, "=", result)
        if expected2:
            random_bytes = drbg.generate(returnedbits_len_inbyte)
            result = (random_bytes == expected2)
            print("Caliptra NEXT test number", COUNT, "=", result)
    return result


def gen_caliptra_kats():
    """
    Pre-computed self-consistent test vectors used by the SystemVerilog
    testbench.  The expected outputs are produced by running this same
    HMAC_DRBG_SHA256 class against the inputs below.  Update the
    `expected` constants in `hmac_drbg_sha256_tb.sv` whenever any of the
    seed material is changed here.
    """
    cases = [
        # (entropy_hex, nonce_hex)
        ("0000000000000000000000000000000000000000000000000000000000000000",
         "0000000000000000000000000000000000000000000000000000000000000000"),
        ("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
         "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"),
        ("f71ee80f1d123dc3f70eaa1fb3272714858ea555bc496bf39adb107b192bf0bc",
         "de2b2a66ee13797c69438a9bf6f8514c0a8abefd3e5533e1119ae88e8d641771"),
        ("6b9d3dad2e1b8c1c05b19875b6659f4de23c3b667bf297ba9aa47740787137d8",
         "9a9083505bc92276aec4be312696ef7bf3bf603f4bbd381196a029f340585312"),
    ]
    print("\nCaliptra-style HMAC-DRBG-SHA256 KATs:")
    for idx, (e_hex, n_hex) in enumerate(cases):
        entropy = bytes.fromhex(e_hex)
        nonce   = bytes.fromhex(n_hex)
        drbg = HMAC_DRBG_SHA256(entropy, nonce)
        b0 = drbg.generate(32).hex()
        b1 = drbg.generate(32).hex()
        b2 = drbg.generate(32).hex()
        print(f"COUNT={idx}")
        print(f"  entropy = {e_hex}")
        print(f"  nonce   = {n_hex}")
        print(f"  INIT    = {b0}")
        print(f"  NEXT1   = {b1}")
        print(f"  NEXT2   = {b2}")


def gen_expected_outputs():
    """Used by the randomized TB: read entropy/nonce from `tb_inputs.hex`
    and write per-round (rejection-sampled) outputs to
    `hmac_drbg_sha256_test_vector.hex`."""
    with open("tb_inputs.hex", "r") as f:
        lines = f.readlines()

    num_rounds = int(lines[0].strip())
    entropy = bytes.fromhex(lines[1].strip())
    nonce = bytes.fromhex(lines[2].strip())

    returnedbits_len_inbyte = 256 // 8
    drbg = HMAC_DRBG_SHA256(entropy, nonce)
    outputs = []

    for _ in range(num_rounds):
        while True:
            output = drbg.generate(returnedbits_len_inbyte)
            if 0 < int.from_bytes(output, 'big') < HMAC_DRBG_PRIME:
                outputs.append(output.hex())
                break

    with open("hmac_drbg_sha256_test_vector.hex", "w") as f:
        f.write(f"{num_rounds:1X}\n")
        f.write(f"{entropy.hex()}\n")
        f.write(f"{nonce.hex()}\n")
        for output in outputs:
            f.write(f"{output}\n")


if __name__ == "__main__":
    if os.path.exists("tb_inputs.hex"):
        print("REF MODEL: Found tb_inputs.hex. Generating the expected outputs...")
        gen_expected_outputs()
    else:
        print("REF MODEL: No tb_inputs.hex found.  Printing fixed KATs for the TB.")
        gen_caliptra_kats()
