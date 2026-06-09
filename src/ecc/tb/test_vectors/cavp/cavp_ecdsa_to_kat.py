#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""
Convert a NIST CAVP 186-4 ECDSA SigGen .rsp section (single
[curve,sha] block) into the 12-line-per-TC format consumed by
`ecc_top_tb::read_test_vectors`.

Maps each CAVP record:
    Msg = <hex>          # message (pre-hash)
    d   = <hex>          # private key
    Qx  = <hex>          # public key x
    Qy  = <hex>          # public key y
    k   = <hex>          # nonce used in CAVP
    R   = <hex>
    S   = <hex>

into:
    line  0  hashed_msg     = SHA-{256,384}(Msg)
    line  1  privkey        = d
    line  2  pubkey.x       = Qx
    line  3  pubkey.y       = Qy
    line  4  seed           = 0           (unused; det SIGN does not read it)
    line  5  nonce          = 0           (unused; det SIGN does not read it)
    line  6  R              = R
    line  7  S              = S
    line  8  IV             = 0           (no blinding, force = identity)
    line  9  privkeyB       = k           (force-injected as DRBG output by
                                           ecc_cavp_sign_p{256,384}_test)
    line 10  DH_sharedkey   = 0
    line 11  TC counter

Det SIGN runs the deterministic ECDSA micro-program; the TB forces
`hmac_drbg_result_p{256,384} = k` and zeroes the blinding entropy so
(R, S) become bit-exact functions of (k, d, hashed_msg) and must equal
the CAVP-provided (R, S).

Usage:
    cavp_ecdsa_to_kat.py <SigGen_PXXX_SHAYYY.rsp> <out.hex>
"""

import hashlib
import re
import sys
from pathlib import Path


CURVES = {
    "[P-256,SHA-256]": (hashlib.sha256, 64),
    "[P-384,SHA-384]": (hashlib.sha384, 96),
}


def _pad(value_int, hex_width):
    """Zero-pad to fixed hex width (uppercase to match existing KATs)."""
    return f"{value_int:0{hex_width}X}"


def convert(src, dst):
    text = Path(src).read_text()
    tag = None
    for t in CURVES:
        if t in text:
            tag = t
            break
    if tag is None:
        sys.exit(f"{src}: no recognized [curve,sha] section header "
                 f"({list(CURVES)})")
    hashfn, hex_w = CURVES[tag]
    zero = "0" * hex_w

    rec_re = re.compile(
        r"Msg\s*=\s*([0-9a-fA-F]+)\s*\n"
        r"(?:d\s*=\s*([0-9a-fA-F]+)\s*\n)"
        r"(?:Qx\s*=\s*([0-9a-fA-F]+)\s*\n)"
        r"(?:Qy\s*=\s*([0-9a-fA-F]+)\s*\n)"
        r"(?:k\s*=\s*([0-9a-fA-F]+)\s*\n)"
        r"(?:R\s*=\s*([0-9a-fA-F]+)\s*\n)"
        r"(?:S\s*=\s*([0-9a-fA-F]+))")
    records = rec_re.findall(text)
    if not records:
        sys.exit(f"{src}: no SigGen records parsed")

    out = []
    for tc, (msg_h, d_h, qx_h, qy_h, k_h, r_h, s_h) in enumerate(records):
        h = hashfn(bytes.fromhex(msg_h)).hexdigest().upper()
        out.append(_pad(int(h, 16), hex_w))         # 0  hashed_msg
        out.append(_pad(int(d_h, 16),  hex_w))      # 1  privkey
        out.append(_pad(int(qx_h, 16), hex_w))      # 2  pubkey.x
        out.append(_pad(int(qy_h, 16), hex_w))      # 3  pubkey.y
        out.append(zero)                            # 4  seed
        out.append(zero)                            # 5  nonce
        out.append(_pad(int(r_h, 16),  hex_w))      # 6  R
        out.append(_pad(int(s_h, 16),  hex_w))      # 7  S
        out.append(zero)                            # 8  IV
        out.append(_pad(int(k_h, 16),  hex_w))      # 9  privkeyB = k
        out.append(zero)                            # 10 DH_sharedkey
        out.append(f"{tc:0{hex_w}x}")               # 11 TC counter

    Path(dst).write_text("\n".join(out) + "\n")
    print(f"{src} -> {dst}: {len(records)} TCs ({tag}, hex_width={hex_w})")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(2)
    convert(sys.argv[1], sys.argv[2])
