#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
#
# Single-TC nondet KAT generator: reads an 11-line det KAT (as emitted
# by ecc_secp{256,384}r1.exe), draws k = HMAC-DRBG-SHA{256,384}(seed,
# nonce), and writes a 12-line nondet KAT with (R,S) recomputed via
# ECDSA-with-explicit-k. Curve auto-detected by hex-line width (64 ->
# P-256, 96 -> P-384).
#
# Two consumers today:
#   1. Offline bulk regen: imported by gen_nondet_kat.py (same dir),
#      which loops this over an _all.hex multi-TC dump to produce
#      secp{256,384}_nondet_kat.hex for block-TB (ecc_top_tb).
#   2. UVM per-txn regen: invoked as a script by ECC_in_driver_bfm on
#      the kupadhyayula-uvm-ecc branch so every random seed generates
#      distinct nondet KAT inputs.
#
# The block-TB tests themselves consume the pre-generated *_kat.hex
# files -- they do NOT call this script at sim time. But keep this
# file committed so gen_nondet_kat.py works when someone needs to
# regenerate the KATs.
#
# Pure-Python ECDSA + HMAC-DRBG mirrors bit-exactly the RTL DRBG
# (src/hmac_drbg/rtl/hmac_drbg.sv, NIST SP 800-90A).
#
# Usage:
#   make_nondet_kat.py <det_single_tc.hex> <nondet_out.hex>

import hashlib
import hmac
import sys


# ----- Curve parameters -----------------------------------------------------
# secp256r1 (NIST P-256)
_P256 = dict(
    p =int("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff", 16),
    a =int("ffffffff00000001000000000000000000000000fffffffffffffffffffffffc", 16),
    b =int("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b", 16),
    Gx=int("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296", 16),
    Gy=int("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5", 16),
    n =int("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551", 16),
    nbytes=32,
)
# secp384r1 (NIST P-384)
_P384 = dict(
    p =int("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"
           "ffffffff0000000000000000ffffffff", 16),
    a =int("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"
           "ffffffff0000000000000000fffffffc", 16),
    b =int("b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875a"
           "c656398d8a2ed19d2a85c8edd3ec2aef", 16),
    Gx=int("aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a38"
           "5502f25dbf55296c3a545e3872760ab7", 16),
    Gy=int("3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c0"
           "0a60b1ce1d7e819d7a431d7c90ea0e5f", 16),
    n =int("ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf"
           "581a0db248b0a77aecec196accc52973", 16),
    nbytes=48,
)


# ----- HMAC-DRBG (mirror of src/hmac_drbg/rtl/hmac_drbg.sv) -----------------
class _HmacDrbg:
    def __init__(self, entropy, nonce, hash_fn, hash_len):
        self._hash = hash_fn
        self.K = b"\x00" * hash_len
        self.V = b"\x01" * hash_len
        self._update(entropy + nonce)

    def _hmac(self, k, m):
        return hmac.new(k, m, self._hash).digest()

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


# ----- Elliptic curve arithmetic (Jacobian coords) --------------------------
def _inv_mod(a, m):
    """Modular inverse via extended Euclidean algorithm.
    Avoids the pow(a, -1, m) form to sidestep any older-Python
    interop issues; a and m are always positive by construction."""
    a %= m
    if a == 0:
        raise ZeroDivisionError("inverse of 0 mod m")
    lo, hi = a, m
    x_lo, x_hi = 1, 0
    while lo > 1:
        q = hi // lo
        hi, lo = lo, hi - q * lo
        x_hi, x_lo = x_lo, x_hi - q * x_lo
    return x_lo % m


def _point_add(P, Q, p, a):
    if P is None: return Q
    if Q is None: return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2:
        if (y1 + y2) % p == 0:
            return None
        # Point doubling
        lam = (3 * x1 * x1 + a) * _inv_mod(2 * y1, p) % p
    else:
        lam = (y2 - y1) * _inv_mod((x2 - x1) % p, p) % p
    x3 = (lam * lam - x1 - x2) % p
    y3 = (lam * (x1 - x3) - y1) % p
    return (x3, y3)


def _point_mul(k, P, p, a):
    R = None
    Q = P
    while k > 0:
        if k & 1:
            R = _point_add(R, Q, p, a)
        Q = _point_add(Q, Q, p, a)
        k >>= 1
    return R


# ----- ECDSA-with-explicit-k ------------------------------------------------
def _ecdsa_sign(curve, priv, msg_int, k):
    """Return (R, S) = ECDSA(msg, priv, k) on the given curve.
    Standard formula: r = (k*G).x mod n; s = k^-1 * (h + r*d) mod n.
    Matches RTL SIGN dataflow when hmac_drbg_result is SV-forced = k."""
    p, a, n, Gx, Gy = curve["p"], curve["a"], curve["n"], curve["Gx"], curve["Gy"]
    kR = _point_mul(k, (Gx, Gy), p, a)
    r = kR[0] % n
    h = msg_int % n
    s = (_inv_mod(k, n) * (h + r * priv)) % n
    return r, s


# ----- Top-level converter --------------------------------------------------
def _pick_curve_and_hash(hex_len):
    """Pick curve params + hash + DRBG output size from a KAT hex-line width.
    P-256 hashed_msg is 64 hex chars, P-384 is 96."""
    if hex_len == 64:
        return _P256, hashlib.sha256, 32
    if hex_len == 96:
        return _P384, hashlib.sha384, 48
    raise ValueError(f"unrecognized KAT hex-line width: {hex_len}")


def _draw_k(seed_hex, nonce_hex, curve, hash_fn, hash_len):
    """Draw k from HMAC-DRBG(seed, nonce) with the RTL's reject loop
    (k must be in [1, n-1])."""
    drbg = _HmacDrbg(bytes.fromhex(seed_hex), bytes.fromhex(nonce_hex),
                    hash_fn, hash_len)
    while True:
        k = int.from_bytes(drbg.generate(curve["nbytes"]), "big")
        if 0 < k < curve["n"]:
            return k


def convert(det_hex_path, nondet_hex_path):
    """Read an 11-line single-TC det KAT and emit a 12-line nondet KAT."""
    with open(det_hex_path) as f:
        lines = [l.strip() for l in f if l.strip()]
    if len(lines) != 11:
        raise ValueError(f"{det_hex_path}: expected 11 hex lines, got {len(lines)}")

    curve, hash_fn, hash_len = _pick_curve_and_hash(len(lines[0]))
    msg_int  = int(lines[0], 16)
    priv     = int(lines[1], 16)
    # lines[2], lines[3] = pubkey.x, pubkey.y  (unchanged)
    seed_hex, nonce_hex = lines[4], lines[5]
    # lines[6], lines[7] = det R, det S  (discarded; recomputed below)
    # lines[8]           = IV            (unchanged, unused for nondet)
    # lines[9]           = det privkeyB  (overwritten with our k)
    # lines[10]          = DH_sharedkey  (zeroed since nondet SIGN doesn't use it)

    k = _draw_k(seed_hex, nonce_hex, curve, hash_fn, hash_len)
    R, S = _ecdsa_sign(curve, priv, msg_int, k)

    hex_w = len(lines[0])   # 64 (P-256) or 96 (P-384)
    k_hex = f"{k:0{hex_w}x}".upper()
    r_hex = f"{R:0{hex_w}x}".upper()
    s_hex = f"{S:0{hex_w}x}".upper()

    out = [
        lines[0],          # hashed_msg
        lines[1],          # privkey
        lines[2],          # pubkey.x
        lines[3],          # pubkey.y
        lines[4],          # seed
        lines[5],          # nonce
        r_hex,             # R (nondet)
        s_hex,             # S (nondet)
        lines[8],          # IV
        k_hex,             # privkeyB slot: SV-force target
        "0" * hex_w,       # DH_sharedkey: zeroed
        "0" * 12,          # TC counter pad
    ]
    with open(nondet_hex_path, "w") as f:
        f.write("\n".join(out) + "\n")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(2)
    convert(sys.argv[1], sys.argv[2])
