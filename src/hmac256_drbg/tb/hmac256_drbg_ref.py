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

import hmac
import hashlib
import os

# NIST P-256 curve order n (used as the rejection threshold when the DRBG
# feeds a per-message ECDSA-P256 nonce per RFC 6979).
HMAC_DRBG_PRIME = int("FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551", 16)


class HMAC_DRBG:
    def __init__(self, entropy, nonce=b"", personalization=b""):
        self.hash_function = hashlib.sha256
        self.seed_length   = self.hash_function().digest_size
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


def gen_expected_outputs():
    # Read testbench inputs written by hmac256_drbg_tb.sv.
    with open("tb_inputs.hex", "r") as f:
        lines = f.readlines()

    num_rounds = int(lines[0].strip())
    entropy    = bytes.fromhex(lines[1].strip())
    nonce      = bytes.fromhex(lines[2].strip())

    returnedbits_len_inbyte = 256 // 8
    drbg = HMAC_DRBG(entropy, nonce)
    outputs = []

    for _ in range(num_rounds):
        while True:
            output = drbg.generate(returnedbits_len_inbyte)
            if 0 < int.from_bytes(output, "big") < HMAC_DRBG_PRIME:
                outputs.append(output.hex())
                break

    with open("hmac256_drbg_test_vector.hex", "w") as f:
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
        print("REF MODEL: No tb_inputs.hex found. Nothing to do.")
