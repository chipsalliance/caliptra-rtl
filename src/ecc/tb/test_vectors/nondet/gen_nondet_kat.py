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
Bulk converter: raw mbedtls non-det ECC vector dump (11 hex lines + 1
blank separator per TC) -> 12-line-per-TC KAT hex file consumed by
`ecc_top_tb::read_test_vectors`.

Output layout per TC:
    line 0:  hashed_msg
    line 1:  privkey
    line 2:  pubkey.x
    line 3:  pubkey.y
    line 4:  seed
    line 5:  nonce
    line 6:  R                  (recomputed = ECDSA(msg, priv, k))
    line 7:  S                  (recomputed = ECDSA(msg, priv, k))
    line 8:  IV                 (unchanged; unused for nondet SIGN)
    line 9:  privkeyB           (overwritten with k drawn from
                                 HMAC-DRBG-SHA{256,384}(seed, nonce))
    line 10: DH_sharedkey       (passed through from raw mbedtls dump;
                                 nondet SIGN tests don't consume it)
    line 11: TC counter         (replaces blank separator)

Rationale: the RTL nondet SIGN DRBG entropy depends on a free-running
clock counter (see ecc_hmac_drbg_interface.sv, sca_entropy =
IV ^ lfsr_seed ^ counter_nonce), so no offline oracle can predict k.
The bypass tests instead SV-force hmac_drbg_result_p{256,384} = k;
that same k is placed here in the privkeyB slot, and (R,S) recomputed
via ECDSA-with-explicit-k so the bit-exact compare is meaningful.

All EC / DRBG primitives are re-used from `make_nondet_kat.py` in the
same directory (single source of truth; mirrors RTL bit-exactly).

Usage:
    gen_nondet_kat.py <raw.hex> <kat_out.hex>
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from make_nondet_kat import _pick_curve_and_hash, _draw_k, _ecdsa_sign  # noqa: E402


def _process_tc(buf):
    """Recompute (R, S) with k from HMAC-DRBG(seed, nonce) and return
    the 11 output lines with privkeyB=k, R/S recomputed. DH_sharedkey
    (line 10) is passed through unchanged from the raw mbedtls dump
    since nondet SIGN tests don't consume it."""
    curve, hash_fn, hash_len = _pick_curve_and_hash(len(buf[0]))
    hex_w = curve["nbytes"] * 2

    msg_int = int(buf[0], 16)
    priv    = int(buf[1], 16)
    seed_hex, nonce_hex = buf[4], buf[5]

    k    = _draw_k(seed_hex, nonce_hex, curve, hash_fn, hash_len)
    R, S = _ecdsa_sign(curve, priv, msg_int, k)

    return [
        buf[0], buf[1], buf[2], buf[3], buf[4], buf[5],
        f"{R:0{hex_w}x}".upper(),
        f"{S:0{hex_w}x}".upper(),
        buf[8],
        f"{k:0{hex_w}x}".upper(),
        buf[10],
    ]


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
            out.extend(_process_tc(buf))
            out.append(f"{tc:012x}")
            tc += 1
            buf = []
            continue
        buf.append(s)
    if buf:
        if len(buf) != 11:
            raise ValueError(
                f"{src}: trailing partial TC with {len(buf)} hex lines")
        out.extend(_process_tc(buf))
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
