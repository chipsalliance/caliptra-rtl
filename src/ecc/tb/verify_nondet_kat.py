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
# verify_nondet_kat.py
#
# Independent ECDSA-verify pass over the non-deterministic KAT files
# produced by ecc_secp{256,384}r1.c (built with -DNON_DET).  Uses the
# `cryptography` library so we are not "patched mbedtls verifying its
# own output".
#
# Usage:
#   python3 verify_nondet_kat.py \
#       test_vectors/nondet/secp256_nondet_testvector_all.hex
#   python3 verify_nondet_kat.py \
#       test_vectors/nondet/secp384_nondet_testvector_all.hex
#
# Exits 0 on all-pass, 1 on any failure.  Curve is auto-detected from
# the hex-line width (64 chars -> P-256, 96 chars -> P-384).

import sys

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec, utils


CURVES = {
    64: (ec.SECP256R1(), hashes.SHA256(), 32),
    96: (ec.SECP384R1(), hashes.SHA384(), 48),
}


def _parse_tcs(path, hex_widths):
    """Yield lists of 11 hex strings.  Accepts either the raw C-tool
    format (11 data lines + 1 blank separator per TC) or the
    post-processed gen_*_kat.py format (12 data lines per TC with the
    12th being a hex TC counter)."""
    with open(path) as f:
        raw = f.read().splitlines()
    tc, buf = [], []
    for line in raw:
        s = line.strip()
        if not s:
            if len(buf) == 11:
                yield buf
                buf = []
            elif buf:
                raise ValueError(
                    f"{path}: blank separator at unexpected position "
                    f"({len(buf)} data lines buffered)")
            continue
        # If this is the 12th line of a TC (post-processed counter),
        # flush the 11 hex lines and treat counter as separator.
        if len(buf) == 11:
            try:
                int(s, 16)
                # 12th non-blank is a hex string the same width as the
                # others -> looks like a 12-line-per-TC vector format.
                if len(s) == len(buf[0]):
                    raise ValueError(
                        f"{path}: got 12 hex lines per TC; expected "
                        "11 data + 1 separator")
            except ValueError:
                pass
            yield buf
            buf = []
            continue
        if len(s) not in hex_widths:
            raise ValueError(f"{path}: bad hex width {len(s)} (line={s!r})")
        buf.append(s)
    if len(buf) == 11:
        yield buf
    elif buf:
        raise ValueError(
            f"{path}: trailing partial TC with {len(buf)} data lines")


def main(path):
    tcs = list(_parse_tcs(path, hex_widths=set(CURVES.keys())))
    if not tcs:
        print(f"{path}: empty"); return 1
    width = len(tcs[0][0])
    if width not in CURVES:
        print(f"{path}: unexpected hex width {width}"); return 1
    curve, hashfn, w_bytes = CURVES[width]

    fails = 0
    for tc_idx, lines in enumerate(tcs):
        h, d, px, py, seed, nonce, r, s = (
            int(lines[i], 16) for i in range(8))
        pub = ec.EllipticCurvePublicNumbers(px, py, curve).public_key()
        sig = utils.encode_dss_signature(r, s)
        try:
            pub.verify(sig,
                       h.to_bytes(w_bytes, "big"),
                       ec.ECDSA(utils.Prehashed(hashfn)))
            print(f"TC{tc_idx:3d}: OK")
        except InvalidSignature:
            print(f"TC{tc_idx:3d}: FAIL")
            fails += 1

    print(f"\n{path}: {len(tcs) - fails}/{len(tcs)} TCs verified "
          f"({curve.name}, hash={hashfn.name})")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("usage: verify_nondet_kat.py <kat.hex>")
        sys.exit(2)
    sys.exit(main(sys.argv[1]))
