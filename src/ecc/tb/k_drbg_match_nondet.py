#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
#
# k_drbg_match_nondet.py
#
# Bit-exact cross-check between the non-deterministic KAT vectors
# emitted by ecc_secp{256,384}r1.c (-DNON_DET) and the RTL HMAC-DRBG
# block at src/hmac_drbg/rtl/hmac_drbg.sv.
#
# For each TC the script:
#   1. Recovers k from the signature:   k = s^-1 * (h + r*d) mod n
#   2. Re-runs an HMAC-DRBG with        entropy = seed_buf,
#                                       nonce   = nonce_buf
#      (Option B seeding) using the same V/K init, hash function,
#      and reject-loop semantics (k==0 || k>=n) as the RTL block.
#   3. Asserts that the first non-rejected REG_SIZE-bit output equals
#      the sig-recovered k.
#
# All-True ==> the C tool produces (r,s) from exactly the k the RTL
# HMAC-DRBG block will produce for the same (seed, nonce).  This is
# the merge-gate check for the non-det KAT set.
#
# Usage:
#   python3 k_drbg_match_nondet.py \
#       test_vectors/nondet/secp256_nondet_testvector_all.hex
#   python3 k_drbg_match_nondet.py \
#       test_vectors/nondet/secp384_nondet_testvector_all.hex
#
# A second mode self-tests the same HMAC_DRBG class against NIST CAVP
# DRBGVS vectors, proving the model is bit-exact with the NIST KAT
# before it is trusted as a golden reference for the RTL block:
#
#   python3 k_drbg_match_nondet.py --cavp-drbg \
#       test_vectors/cavp/drbg/HMAC_DRBG_SHA256_no_reseed.rsp
#   python3 k_drbg_match_nondet.py --cavp-drbg \
#       test_vectors/cavp/drbg/HMAC_DRBG_SHA384_no_reseed.rsp
#
# The CAVP records used are PredictionResistance=False, no
# personalization string, no additional input -- the exact instantiate
# + double-generate profile that matches the RTL HMAC-DRBG block.
#
# Exits 0 on all-match, 1 on any mismatch.

import hashlib
import hmac
import re
import sys


# Group orders n
N_P256 = int("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551", 16)
N_P384 = int("ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf"
             "581a0db248b0a77aecec196accc52973", 16)


CURVES = {
    # hex_width: (name, n, hashfn, reg_bytes)
    64: ("p256", N_P256, hashlib.sha256, 32),
    96: ("p384", N_P384, hashlib.sha384, 48),
}


class HMAC_DRBG:
    """Bit-exact mirror of src/hmac_drbg/rtl/hmac_drbg.sv:
       V_init = 01..01, K_init = 00..00, NIST SP 800-90A HMAC-DRBG."""
    def __init__(self, entropy, nonce, hashfn):
        self.hashfn = hashfn
        d = hashfn().digest_size
        self.K = b"\x00" * d
        self.V = b"\x01" * d
        self._update(entropy + nonce)

    def _hmac(self, k, m):
        return hmac.new(k, m, self.hashfn).digest()

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


def k_expected(seed_int, nonce_int, n, hashfn, reg_bytes):
    """Re-runs the HW reject loop until k in [1, n-1]."""
    drbg = HMAC_DRBG(seed_int.to_bytes(reg_bytes, "big"),
                     nonce_int.to_bytes(reg_bytes, "big"),
                     hashfn)
    while True:
        k = int.from_bytes(drbg.generate(reg_bytes), "big")
        if 0 < k < n:
            return k


def _parse_tcs(path, hex_widths):
    """Yield lists of 11 hex strings.  Accepts either the raw C-tool
    format (11 data lines + 1 blank separator per TC) or the
    post-processed gen_*_kat.py format (12 data lines per TC with the
    12th being a decimal TC counter)."""
    with open(path) as f:
        raw = f.read().splitlines()
    buf = []
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
        if len(buf) == 11:
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
    tcs = list(_parse_tcs(path, hex_widths=set(2 * b for _, _, _, b in CURVES.values())))
    if not tcs:
        print(f"{path}: empty"); return 1
    width = len(tcs[0][0])
    if width not in CURVES:
        print(f"{path}: unexpected hex width {width}"); return 1
    name, n, hashfn, reg_bytes = CURVES[width]

    fails = 0
    for tc_idx, lines in enumerate(tcs):
        h, d, _, _, seed, nonce, r, s = (
            int(lines[i], 16) for i in range(8))
        k_from_sig = (pow(s, -1, n) * (h + r * d)) % n
        k_from_drbg = k_expected(seed, nonce, n, hashfn, reg_bytes)
        ok = (k_from_sig == k_from_drbg)
        marker = "OK" if ok else "FAIL"
        print(f"TC{tc_idx:3d}: {marker}  "
              f"k_sig=0x{k_from_sig:0{reg_bytes*2}x}  "
              f"k_drbg=0x{k_from_drbg:0{reg_bytes*2}x}")
        if not ok:
            fails += 1

    print(f"\n{path}: {len(tcs) - fails}/{len(tcs)} TCs matched RTL DRBG "
          f"({name}, hash={hashfn().name})")
    return 0 if fails == 0 else 1


def cavp_drbg_selftest(path):
    """Verify the HMAC_DRBG class above is bit-exact with NIST CAVP
    DRBGVS HMAC_DRBG.rsp records (no PR, no perso, no addin).

    Per SP 800-90A and CAVP harness rules, each record performs
    Instantiate(entropy, nonce, perso) followed by two Generate calls
    of ReturnedBitsLen bits each; the *second* generate output is
    `ReturnedBits`. The two empty `AdditionalInput =` lines per record
    confirm the no-addin profile."""
    sha_map = {"SHA-256": hashlib.sha256, "SHA-384": hashlib.sha384}

    with open(path) as f:
        text = f.read()

    sha_tag = None
    for tag in sha_map:
        if f"[{tag}]" in text:
            if sha_tag is not None:
                print(f"{path}: multiple [SHA-*] sections, expected one"); return 1
            sha_tag = tag
    if sha_tag is None:
        print(f"{path}: no recognized [SHA-*] section header"); return 1
    hashfn = sha_map[sha_tag]

    m = re.search(r"\[ReturnedBitsLen\s*=\s*(\d+)\]", text)
    if not m:
        print(f"{path}: missing [ReturnedBitsLen = N]"); return 1
    rb_bytes = int(m.group(1)) // 8

    rec_re = re.compile(
        r"COUNT\s*=\s*(\d+)\s*\n"
        r"EntropyInput\s*=\s*([0-9a-fA-F]*)\s*\n"
        r"Nonce\s*=\s*([0-9a-fA-F]*)\s*\n"
        r"PersonalizationString\s*=\s*([0-9a-fA-F]*)\s*\n"
        r"AdditionalInput\s*=\s*([0-9a-fA-F]*)\s*\n"
        r"(?:EntropyInputPR\s*=\s*[0-9a-fA-F]*\s*\n)?"
        r"AdditionalInput\s*=\s*([0-9a-fA-F]*)\s*\n"
        r"(?:EntropyInputPR\s*=\s*[0-9a-fA-F]*\s*\n)?"
        r"ReturnedBits\s*=\s*([0-9a-fA-F]+)")
    records = rec_re.findall(text)
    if not records:
        print(f"{path}: no records parsed"); return 1

    fails = 0
    for count, ent_h, nonce_h, perso_h, addin1_h, addin2_h, rb_h in records:
        if perso_h or addin1_h or addin2_h:
            print(f"COUNT={count}: SKIP (perso/addin not empty, "
                  f"outside the no-addin profile)")
            continue
        drbg = HMAC_DRBG(bytes.fromhex(ent_h), bytes.fromhex(nonce_h), hashfn)
        _ = drbg.generate(rb_bytes)
        got = drbg.generate(rb_bytes).hex()
        want = rb_h.lower()
        ok = (got == want)
        marker = "OK" if ok else "FAIL"
        print(f"COUNT={int(count):3d}: {marker}")
        if not ok:
            print(f"   want = {want}")
            print(f"   got  = {got}")
            fails += 1

    matched = len(records) - fails
    print(f"\n{path}: {matched}/{len(records)} CAVP DRBGVS records matched "
          f"({sha_tag}, ReturnedBitsLen={rb_bytes*8})")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--cavp-drbg":
        sys.exit(cavp_drbg_selftest(sys.argv[2]))
    if len(sys.argv) != 2:
        print("usage: k_drbg_match_nondet.py <kat.hex>")
        print("       k_drbg_match_nondet.py --cavp-drbg <HMAC_DRBG.rsp>")
        sys.exit(2)
    sys.exit(main(sys.argv[1]))
