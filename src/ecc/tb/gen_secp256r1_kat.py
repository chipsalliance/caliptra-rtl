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
Generate a multi-TC P-256 KAT hex file for `ecc_top_tb` by running the
existing `ecc_secp256r1.exe` mbedtls test-vector generator N times and
post-processing its `secp256_testvector_all.hex` output into the
12-line-per-TC format the TB's `read_test_vectors` task expects.

The exe writes 11 data lines per invocation followed by a blank line:

  msg, privkey, pubkeyX, pubkeyY, seed, nonce, R, S, IV, privkeyB,
  DH_sharedkey, <blank>

`read_test_vectors` parses 12 lines per TC; line index 11 must be a
non-blank token (matches the P-384 `ecc_drbg_mbedtls.hex` convention
where a decimal TC counter is placed there). This script replaces each
blank separator with the running TC counter.

Two modes:
  - **force-bypass** (default): overloads line 9 (privkeyB) with
    k = s^-1 * (h + r*priv) mod n so the TB's drbg_bypass_force task
    can drive hmac_drbg_result_p256 = k.
  - **--real-drbg**: leaves line 9 untouched. Use when the RTL P-256
    HMAC-DRBG-SHA256 wrapper is driving k itself (no TB force). The
    C tool already seeds its DRBG with the same (seed, nonce) the RTL
    KEYGEN consumes and the same (privkey, hashed_msg) the RTL SIGN_ST
    det path consumes, so the emitted privkey + (R, S) match what
    the wrapper produces bit-exactly.

Usage:
    gen_secp256r1_kat.py -n 10 -o test_vectors/secp256_kat.hex
    gen_secp256r1_kat.py -n 50 --real-drbg \\
        -o test_vectors/secp256_realdrbg_kat.hex
"""

import argparse
import os
import subprocess
import sys
import tempfile

EXE_DEFAULT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "ecc_secp256r1.exe")


def run_exe_n_times(exe: str, n: int, workdir: str) -> str:
    src = os.path.join(workdir, "secp256_testvector_all.hex")
    if os.path.exists(src):
        os.remove(src)
    for _ in range(n):
        rc = subprocess.run([exe], cwd=workdir, check=False).returncode
        if rc != 0:
            raise RuntimeError(f"{exe} exited with rc={rc}")
    return src


def reformat(src_path: str, dst_path: str, real_drbg: bool = False) -> int:
    # P-256 group order n
    N_P256 = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

    with open(src_path, "r") as fh:
        raw = fh.read().splitlines()

    out, tc, line_in_tc = [], 0, 0
    tc_lines: list[str] = []
    for line in raw:
        if line_in_tc < 11:
            if not line.strip():
                raise RuntimeError(
                    f"unexpected blank data line at TC {tc} idx {line_in_tc}"
                )
            tc_lines.append(line)
            line_in_tc += 1
        else:
            if line.strip():
                raise RuntimeError(
                    f"expected blank separator at TC {tc} got {line!r}"
                )
            if not real_drbg:
                # Force-bypass mode: overload line 9 (privkeyB, unused for
                # P-256 SIGN tests) with k = (h + r*priv) * s^-1 mod n_p256,
                # so the SIGN-bypass TB task can force
                # hmac_drbg_result_p256 = k for a deterministic KAT match.
                # ECDH on P-256 is not part of this validation flow.
                h    = int(tc_lines[0], 16)
                priv = int(tc_lines[1], 16)
                r    = int(tc_lines[6], 16)
                s    = int(tc_lines[7], 16)
                s_inv = pow(s, -1, N_P256)
                k = (s_inv * (h + r * priv)) % N_P256
                tc_lines[9] = f"{k:064X}"
            # Real-DRBG mode: leave tc_lines[9] (privkeyB) untouched. The
            # RTL HMAC-DRBG-SHA256 wrapper derives privkey from
            # (seed, nonce) and k from (privkey, hashed_msg) on its own;
            # no k injection needed. The C tool emits a privkey that
            # matches what the RTL DRBG produces (seeded identically).

            out.extend(tc_lines)
            out.append(f"{tc}")
            tc_lines = []
            line_in_tc = 0
            tc += 1

    if line_in_tc != 0:
        raise RuntimeError(
            f"trailing partial TC: {line_in_tc} data lines without separator"
        )

    os.makedirs(os.path.dirname(dst_path) or ".", exist_ok=True)
    with open(dst_path, "w") as fh:
        fh.write("\n".join(out) + "\n")
    return tc


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("-n", "--num", type=int, default=10,
                    help="number of TCs to generate (default: 10)")
    ap.add_argument("-o", "--output", required=True,
                    help="output hex file path")
    ap.add_argument("--exe", default=EXE_DEFAULT,
                    help=f"path to ecc_secp256r1.exe (default: {EXE_DEFAULT})")
    ap.add_argument("--real-drbg", action="store_true",
                    help="Real-DRBG mode: emit privkeyB (line 9) as-is from "
                         "the C tool (no k injection). Use when the RTL "
                         "P-256 HMAC-DRBG wrapper drives k itself (no TB "
                         "force-bypass). Default is force-bypass mode "
                         "with k = s^-1 * (h + r*priv) mod n injected.")
    args = ap.parse_args()

    if not os.path.isfile(args.exe) or not os.access(args.exe, os.X_OK):
        print(f"ERROR: exe not found / not executable: {args.exe}",
              file=sys.stderr)
        return 1

    with tempfile.TemporaryDirectory(prefix="p256_kat_") as tmp:
        src = run_exe_n_times(args.exe, args.num, tmp)
        n_tc = reformat(src, args.output, real_drbg=args.real_drbg)

    mode = "real-DRBG" if args.real_drbg else "force-bypass"
    print(f"Wrote {n_tc} P-256 KAT vectors ({mode}) to {args.output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
