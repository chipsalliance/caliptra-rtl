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
Reproducible CAVP subset extractor.

Pulls NIST CAVP archives, verifies SHA-256, extracts only the
configurations relevant to the Caliptra ECC core, and writes filtered
.rsp files under src/ecc/tb/test_vectors/cavp/.

Source archives (NIST, public domain):
  ECDSA  : https://csrc.nist.gov/CSRC/media/Projects/
           Cryptographic-Algorithm-Validation-Program/documents/dss/
           186-4ecdsatestvectors.zip
  DRBGVS : https://csrc.nist.gov/CSRC/media/Projects/
           Cryptographic-Algorithm-Validation-Program/documents/drbg/
           drbgtestvectors.zip

Vendored subsets (~few hundred KB total):
  ecdsa/SigGen_P256_SHA256.rsp     (P-256 SigGen, SHA-256 only)
  ecdsa/SigGen_P384_SHA384.rsp     (P-384 SigGen, SHA-384 only)
  drbg/HMAC_DRBG_SHA256_no_reseed.rsp  (SHA-256, no PR, no perso, no addin)
  drbg/HMAC_DRBG_SHA384_no_reseed.rsp  (SHA-384, no PR, no perso, no addin)

Usage:
    cavp_filter.py <ecdsa_zip> <drbg_zip>

The vendored .rsp files are intentionally checked in so the regression
is self-contained and does not require network at sim time. Re-run this
script to refresh after a NIST update; SHA-256 of source archives is
asserted to detect upstream drift.
"""

import hashlib
import io
import re
import sys
import zipfile
from pathlib import Path


HERE = Path(__file__).resolve().parent

EXPECTED_SHA = {
    "186-4ecdsatestvectors.zip":
        "fe47cc92b4cee418236125c9ffbcd9bb01c8c34e74a4ba195d954bcb72824752",
    "drbgtestvectors.zip":
        "5f7e5658ebd5b4e6785a7b12fa32333511d2acc2f2d9c5ae1ffa16b699377769",
}


def _sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _assert_sha(path):
    name = Path(path).name
    want = EXPECTED_SHA.get(name)
    got = _sha256(path)
    if want is None:
        print(f"WARN: no pinned SHA-256 for {name}, got {got}")
    elif want != got:
        sys.exit(f"FATAL: {name} SHA-256 mismatch\n  expected {want}\n  got      {got}")
    else:
        print(f"OK   {name} sha256={got[:16]}...")


def filter_ecdsa_siggen(zip_path, curve_tag, dst):
    """Extract one [curve_tag] section (e.g. '[P-256,SHA-256]') from
    SigGen.txt (the .req file containing d and k) into a stand-alone
    .rsp. We use .txt rather than .rsp because the .rsp publishes only
    Msg/Qx/Qy/R/S -- d and k are required to force-bypass the DRBG
    output for an end-to-end RTL KAT."""
    with zipfile.ZipFile(zip_path) as z:
        raw = z.read("186-4ecdsatestvectors/SigGen.txt").decode("ascii", "replace")
    lines = raw.splitlines()
    out, in_section, n_tcs = [], False, 0
    for line in lines:
        s = line.strip()
        if s.startswith("[") and s.endswith("]") and "," in s:
            in_section = (s == curve_tag)
            if in_section:
                out.append(line)
            continue
        if in_section:
            out.append(line)
            if s.startswith("Msg ="):
                n_tcs += 1
    header = [
        "# Filtered subset of NIST CAVP 186-4ECDSA SigGen.txt (.req)",
        f"# Source: 186-4ecdsatestvectors.zip (sha256={EXPECTED_SHA['186-4ecdsatestvectors.zip'][:16]}...)",
        f"# Section: {curve_tag}",
        f"# TCs: {n_tcs}",
        "",
    ]
    Path(dst).write_text("\n".join(header + out) + "\n")
    print(f"  wrote {dst}  ({n_tcs} TCs, {curve_tag})")


def filter_hmac_drbg(zip_path, sha_tag, dst):
    """Extract HMAC_DRBG.rsp (no_reseed) records with [SHA-X],
    PredictionResistance=False, PersonalizationStringLen=0,
    AdditionalInputLen=0. Drops every other [SHA-*] config and the
    PR/perso/addin-enabled blocks."""
    with zipfile.ZipFile(zip_path) as outer:
        inner = outer.read("drbgvectors_no_reseed.zip")
    with zipfile.ZipFile(io.BytesIO(inner)) as z:
        raw = z.read("HMAC_DRBG.rsp").decode("ascii", "replace")

    blocks = re.split(r"(?=^\[SHA-)", raw, flags=re.MULTILINE)
    keep_blocks = []
    for blk in blocks:
        head = blk.splitlines()[:8]
        head_s = "\n".join(head)
        if not head_s.startswith(f"[{sha_tag}]"):
            continue
        if "[PredictionResistance = False]" not in head_s:
            continue
        if "[PersonalizationStringLen = 0]" not in head_s:
            continue
        if "[AdditionalInputLen = 0]" not in head_s:
            continue
        keep_blocks.append(blk)

    if not keep_blocks:
        sys.exit(f"FATAL: no matching DRBG block for [{sha_tag}] no-PR no-perso no-addin")

    n_tcs = sum(blk.count("COUNT = ") for blk in keep_blocks)
    header = [
        "# Filtered subset of NIST CAVP DRBGVS HMAC_DRBG.rsp (drbgvectors_no_reseed)",
        f"# Source: drbgtestvectors.zip (sha256={EXPECTED_SHA['drbgtestvectors.zip'][:16]}...)",
        f"# Section: [{sha_tag}] PredictionResistance=False, perso=0, addin=0",
        f"# TCs: {n_tcs}",
        "",
    ]
    Path(dst).write_text("\n".join(header) + "\n" + "".join(keep_blocks))
    print(f"  wrote {dst}  ({n_tcs} TCs, [{sha_tag}] no-PR no-perso no-addin)")


def main(ecdsa_zip, drbg_zip):
    _assert_sha(ecdsa_zip)
    _assert_sha(drbg_zip)

    (HERE / "ecdsa").mkdir(exist_ok=True)
    (HERE / "drbg").mkdir(exist_ok=True)

    filter_ecdsa_siggen(ecdsa_zip, "[P-256,SHA-256]",
                        HERE / "ecdsa" / "SigGen_P256_SHA256.rsp")
    filter_ecdsa_siggen(ecdsa_zip, "[P-384,SHA-384]",
                        HERE / "ecdsa" / "SigGen_P384_SHA384.rsp")

    filter_hmac_drbg(drbg_zip, "SHA-256",
                     HERE / "drbg" / "HMAC_DRBG_SHA256_no_reseed.rsp")
    filter_hmac_drbg(drbg_zip, "SHA-384",
                     HERE / "drbg" / "HMAC_DRBG_SHA384_no_reseed.rsp")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(2)
    main(sys.argv[1], sys.argv[2])
