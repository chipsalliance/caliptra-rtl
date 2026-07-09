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
Convert the raw output of the mbedtls non-det ECC vector tool
(11 hex lines + 1 blank separator per TC) into the 12-line-per-TC
format `ecc_top_tb::read_test_vectors` consumes:

    line 0:  hashed_msg
    line 1:  privkey
    line 2:  pubkey.x
    line 3:  pubkey.y
    line 4:  seed
    line 5:  nonce
    line 6:  R
    line 7:  S
    line 8:  IV
    line 9:  privkeyB           (for P-256: overwritten with the k value
                                 produced by an HMAC-DRBG-SHA256 reseed
                                 from (seed, nonce); used by
                                 ecc_nondet_sign_p256_bypass_test which
                                 SV-forces hmac_drbg_result_p256 = k
                                 because the P-256 DRBG block is not yet
                                 instantiated. For P-384: overwritten
                                 with the k value produced by an
                                 HMAC-DRBG-SHA384 reseed from (seed,
                                 nonce); enables direct bit-exact KAT
                                 R,S compare when the UVM BFM forces
                                 hmac_drbg_result_p384 = k, bypassing
                                 the RTL's SIGN_NONCE_ST whitening
                                 stage.)
    line 10: DH_sharedkey       (unused for SIGN; passed through unchanged)
    line 11: TC counter         (replaces the mbedtls blank-line separator)

Usage:
    gen_nondet_kat.py <raw.hex> <kat_out.hex>
"""
import hashlib
import hmac
import sys


# Group order for secp256r1; used by the P-256 k-injection path.
N_P256 = int("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551", 16)

# Group order for secp384r1; used by the P-384 k-injection path.
N_P384 = int("ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf"
             "581a0db248b0a77aecec196accc52973", 16)


class _HmacDrbgSha256:
    """Bit-exact mirror of src/hmac_drbg/rtl/hmac_drbg.sv parameterized
    on SHA-256: V_init = 01..01, K_init = 00..00, NIST SP 800-90A."""
    def __init__(self, entropy, nonce):
        self.K = b"\x00" * 32
        self.V = b"\x01" * 32
        self._update(entropy + nonce)

    def _hmac(self, k, m):
        return hmac.new(k, m, hashlib.sha256).digest()

    def _update(self, m=b""):
        self.K = self._hmac(self.K, self.V + b"\x00" + m)
        self.V = self._hmac(self.K, self.V)
        if m:
            self.K = self._hmac(self.K, self.V + b"\x01" + m)
            self.V = self._hmac(self.K, self.V)

    def generate(self, nbytes):
        out = b""
        while len(out) < nbytes:
            self.V = self._hmac(self.K, self.V)
            out += self.V
        self._update(b"")
        return out[:nbytes]


class _HmacDrbgSha384:
    """SHA-384 variant of the DRBG mirror above; matches mbedtls's
    mbedtls_hmac_drbg_random when seeded with (seed || nonce). Used
    to pre-compute k for P-384 nondet TCs so ecc_random_test can
    force hmac_drbg_result_p384 and bit-exact match KAT R,S."""
    def __init__(self, entropy, nonce):
        self.K = b"\x00" * 48
        self.V = b"\x01" * 48
        self._update(entropy + nonce)

    def _hmac(self, k, m):
        return hmac.new(k, m, hashlib.sha384).digest()

    def _update(self, m=b""):
        self.K = self._hmac(self.K, self.V + b"\x00" + m)
        self.V = self._hmac(self.K, self.V)
        if m:
            self.K = self._hmac(self.K, self.V + b"\x01" + m)
            self.V = self._hmac(self.K, self.V)

    def generate(self, nbytes):
        out = b""
        while len(out) < nbytes:
            self.V = self._hmac(self.K, self.V)
            out += self.V
        self._update(b"")
        return out[:nbytes]


def _k_p256(seed_hex, nonce_hex):
    """Re-run the HW reject loop until k in [1, n_p256 - 1]."""
    drbg = _HmacDrbgSha256(bytes.fromhex(seed_hex), bytes.fromhex(nonce_hex))
    while True:
        k = int.from_bytes(drbg.generate(32), "big")
        if 0 < k < N_P256:
            return f"{k:064x}".upper()


def _k_p384(seed_hex, nonce_hex):
    """Re-run the HW reject loop until k in [1, n_p384 - 1]."""
    drbg = _HmacDrbgSha384(bytes.fromhex(seed_hex), bytes.fromhex(nonce_hex))
    while True:
        k = int.from_bytes(drbg.generate(48), "big")
        if 0 < k < N_P384:
            return f"{k:096x}".upper()


def convert(src, dst):
    with open(src) as f:
        raw = [l.rstrip("\n") for l in f]
    out, buf = [], []
    tc = 0
    for line in raw:
        s = line.strip()
        if s == "":
            if len(buf) != 11:
                raise ValueError(
                    f"{src}: blank separator at unexpected position "
                    f"({len(buf)} hex lines buffered, TC={tc})")
            if len(buf[0]) == 64:
                buf[9] = _k_p256(buf[4], buf[5])
            elif len(buf[0]) == 96:
                buf[9] = _k_p384(buf[4], buf[5])
            out.extend(buf)
            out.append(f"{tc:012x}")
            tc += 1
            buf = []
            continue
        buf.append(s)
    if buf:
        if len(buf) != 11:
            raise ValueError(
                f"{src}: trailing partial TC with {len(buf)} hex lines")
        if len(buf[0]) == 64:
            buf[9] = _k_p256(buf[4], buf[5])
        elif len(buf[0]) == 96:
            buf[9] = _k_p384(buf[4], buf[5])
        out.extend(buf)
        out.append(f"{tc:012x}")
        tc += 1
    with open(dst, "w") as f:
        f.write("\n".join(out) + "\n")
    print(f"{src} -> {dst}: {tc} TCs")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(2)
    convert(sys.argv[1], sys.argv[2])
