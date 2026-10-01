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
# ----------------------------------------------------------------------------
# ASCII check for C test-suite source.
#
# The testbench mailbox that tests use to drive stimulus (TB command injection
# in caliptra_top_tb_services.sv) ALSO carries console output: a byte written to
# STDOUT is printed only when it is an ASCII character in the range 8'h06:8'h7E;
# anything outside that range is decoded as a TB command. So a non-ASCII byte in
# a VPRINTF string (e.g. an EM dash, 0xE2 0x80 0x94) aliases as a command.
#
# To remove that whole class of bug this check requires EVERY byte of the scoped
# test source files to lie in [0x06, 0x7E]. Note that the common whitespace
# control bytes TAB (0x09), LF (0x0A) and CR (0x0D) are already inside that
# range, so ordinary format strings are unaffected.
# ----------------------------------------------------------------------------

import argparse
import os
import sys

# Allowed inclusive byte range, matching the tb_services console decode window.
MIN_BYTE = 0x06
MAX_BYTE = 0x7E

# Default scope: all C test-suite sources.
DEFAULT_ROOTS = ["src/integration/test_suites"]
SCANNED_EXTS = (".c", ".h")

# Known Unicode offenders -> ASCII replacement, used by --fix and for hints.
# (These are the characters LLM-generated test code tends to introduce.)
REPLACEMENTS = {
    "\u2014": "--",  # EM DASH
    "\u2013": "-",   # EN DASH
    "\u2212": "-",   # MINUS SIGN
    "\u2192": "->",  # RIGHTWARDS ARROW
    "\u2190": "<-",  # LEFTWARDS ARROW
    "\u21d2": "=>",  # RIGHTWARDS DOUBLE ARROW
    "\u00d7": "x",   # MULTIPLICATION SIGN
    "\u2208": "in",  # ELEMENT OF
    "\u2018": "'",   # LEFT SINGLE QUOTE
    "\u2019": "'",   # RIGHT SINGLE QUOTE
    "\u201c": '"',   # LEFT DOUBLE QUOTE
    "\u201d": '"',   # RIGHT DOUBLE QUOTE
    "\u2026": "...",  # HORIZONTAL ELLIPSIS
    "\u2264": "<=",  # LESS-THAN OR EQUAL
    "\u2265": ">=",  # GREATER-THAN OR EQUAL
    "\u2260": "!=",  # NOT EQUAL
    "\u2022": "*",   # BULLET
    "\u00a0": " ",   # NO-BREAK SPACE
}


def iter_files(paths):
    for p in paths:
        if os.path.isfile(p):
            if p.endswith(SCANNED_EXTS):
                yield p
        else:
            for d, _, fs in os.walk(p):
                for f in fs:
                    if f.endswith(SCANNED_EXTS):
                        yield os.path.join(d, f)


def char_desc(byte_value, decoded):
    name = ""
    if decoded is not None:
        try:
            import unicodedata
            name = unicodedata.name(decoded)
        except (ValueError, ImportError):
            name = "?"
    return f"0x{byte_value:02X}" + (f" ('{decoded}' {name})" if decoded else "")


def scan_file(path):
    """Return a list of (lineno, col, byte, decoded_char) violations."""
    data = open(path, "rb").read()
    # Best-effort decode so we can name the offending character in the report.
    try:
        text = data.decode("utf-8")
        use_text = True
    except UnicodeDecodeError:
        use_text = False

    violations = []
    if use_text:
        for lineno, line in enumerate(text.split("\n"), 1):
            for col, ch in enumerate(line, 1):
                o = ord(ch)
                if o < MIN_BYTE or o > MAX_BYTE:
                    violations.append((lineno, col, o, ch))
    else:
        lineno, col = 1, 1
        for b in data:
            if b == 0x0A:
                lineno, col = lineno + 1, 1
                continue
            if b < MIN_BYTE or b > MAX_BYTE:
                violations.append((lineno, col, b, None))
            col += 1
    return violations


def fix_file(path):
    """Apply known replacements. Return True if the file was modified."""
    try:
        text = open(path, "rb").read().decode("utf-8")
    except UnicodeDecodeError:
        return False
    new = text
    for bad, good in REPLACEMENTS.items():
        new = new.replace(bad, good)
    if new != text:
        open(path, "w", encoding="utf-8").write(new)
        return True
    return False


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("paths", nargs="*", default=DEFAULT_ROOTS,
                    help="Files or directories to scan (default: C test suites).")
    ap.add_argument("--fix", action="store_true",
                    help="Auto-replace known non-ASCII offenders in place.")
    args = ap.parse_args()
    paths = args.paths or DEFAULT_ROOTS

    files = sorted(set(iter_files(paths)))

    if args.fix:
        fixed = [f for f in files if fix_file(f)]
        print(f"[check_ascii] --fix modified {len(fixed)} file(s).")
        for f in fixed:
            print(f"  fixed: {f}")

    total = 0
    offenders = 0
    for f in files:
        v = scan_file(f)
        if v:
            offenders += 1
            total += len(v)
            for (lineno, col, b, ch) in v:
                hint = ""
                if ch in REPLACEMENTS:
                    hint = f"  -> replace with '{REPLACEMENTS[ch]}'"
                print(f"{f}:{lineno}:{col}: non-ASCII byte {char_desc(b, ch)}{hint}")

    if total:
        print("", file=sys.stderr)
        print(f"[check_ascii] FAIL: {total} out-of-range byte(s) in {offenders} file(s); "
              f"only [0x{MIN_BYTE:02X}, 0x{MAX_BYTE:02X}] allowed (tb_services console range).",
              file=sys.stderr)
        print("[check_ascii] Run 'python3 .github/scripts/check_ascii.py --fix' to auto-correct common cases.",
              file=sys.stderr)
        return 1

    print(f"[check_ascii] OK: {len(files)} file(s) scanned, all bytes in "
          f"[0x{MIN_BYTE:02X}, 0x{MAX_BYTE:02X}].")
    return 0


if __name__ == "__main__":
    sys.exit(main())
