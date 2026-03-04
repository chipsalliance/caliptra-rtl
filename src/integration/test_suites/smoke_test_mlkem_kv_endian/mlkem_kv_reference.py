#/usr/local/bin/python3
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
#!/usr/bin/env python3
"""
ML-KEM-1024 KV Endianness — Automated Reference Vector Generator

Full E2E flow computed in pure Python:
  1. HMAC-512(key, msg) → 64-byte tag → seed_d (first 32) || seed_z (last 32)
  2. ML-KEM-1024 keygen  (from seed_d || seed_z)
  3. ML-KEM-1024 encaps  (with mlkem_msg) → shared key
  4. ML-KEM-1024 decaps  → verify shared key round-trips
  5. AES-256-ECB encrypt (shared key as key, known plaintext)
  6. Verify all outputs against expected values

Requirements:
  - Python >= 3.10  (use python3.12 on this system)
  - kyber-py        (pip install kyber-py, or clone to /tmp/kyber-py)
  - cryptography    (pip install cryptography)

Usage:
  python3.12 mlkem_kv_reference.py              # run with default vectors
  python3.12 mlkem_kv_reference.py --update-c    # also emit C defines
"""

import sys
import struct
import hmac
import hashlib

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

# Import kyber-py (try installed, then /tmp clone)
try:
    from kyber_py.ml_kem import ML_KEM_1024
except ImportError:
    sys.path.insert(0, "/tmp/kyber-py/src")
    from kyber_py.ml_kem import ML_KEM_1024

# =====================================================================
# TEST VECTORS — Edit this section to update inputs and expected outputs
# =====================================================================

# HMAC-512 inputs (tag → seed_d || seed_z for ML-KEM)
HMAC_KEY    = "00" * 64   # 64 bytes of 0x00
HMAC_MSG    = "0b" * 64   # 64 bytes of 0x0b

# ML-KEM-1024 encaps message (32 bytes)
MLKEM_MSG   = "b0104bc6bf6074ca38e31533dc84bb45f739783133f70918efde949fb0d51ddc"

# AES plaintext (hex string, must be multiple of 16 bytes)
PLAINTEXT   = "a5" * 64   # 64 bytes of 0xa5

# Expected values (set to None to skip verification and just compute)
EXPECTED_HMAC_TAG   = ("5c314dbb03ad6ade28e553c48f3d56e2"
                       "5684696373b7200c945c50dbc76ed0e5"
                       "7a9b2f510fe4fdf8e0329268fe10d3d1"
                       "75abc56eb547ebec8ac23033ef81cff8")
EXPECTED_SHARED_KEY = None  # compute fresh — depends on seed byte order
EXPECTED_CIPHERTEXT = None  # compute fresh — depends on shared key

# =====================================================================


def hex_to_c_dwords(hex_str, name, per_line=4):
    """Format a hex string as a C DWORD array #define."""
    dwords = struct.unpack(f'>{len(hex_str) // 8}I', bytes.fromhex(hex_str))
    lines = [f'#define {name} {{ \\']
    for i in range(0, len(dwords), per_line):
        chunk = dwords[i:i + per_line]
        vals = ', '.join(f'0x{d:08X}' for d in chunk)
        sep = ',' if i + per_line < len(dwords) else ' '
        lines.append(f'    {vals}{sep} \\')
    lines.append('}')
    return '\n'.join(lines)


def hex_to_c_string(hex_str, name, chunk_size=32):
    """Format a hex string as a C string literal #define."""
    chunks = [hex_str[i:i + chunk_size] for i in range(0, len(hex_str), chunk_size)]
    lines = [f'#define {name} \\']
    for i, chunk in enumerate(chunks):
        end = '' if i == len(chunks) - 1 else ' \\'
        lines.append(f'    "{chunk}"{end}')
    return '\n'.join(lines)


def run_hmac512(key_hex, msg_hex):
    """Run HMAC-SHA512, return 64-byte tag."""
    key = bytes.fromhex(key_hex)
    msg = bytes.fromhex(msg_hex)
    return hmac.new(key, msg, hashlib.sha512).digest()


def run_mlkem(seed_d, seed_z, msg_hex):
    """Run ML-KEM-1024 keygen + encaps + decaps, return shared key bytes."""
    m = bytes.fromhex(msg_hex)
    ek, dk = ML_KEM_1024.key_derive(seed_d + seed_z)
    K_enc, ct = ML_KEM_1024._encaps_internal(ek, m)
    K_dec = ML_KEM_1024.decaps(dk, ct)
    assert K_enc == K_dec, "encaps/decaps shared key mismatch!"
    return K_enc


def run_aes_ecb(key_bytes, plaintext_hex):
    """Run AES-256-ECB encryption, return ciphertext bytes."""
    pt = bytes.fromhex(plaintext_hex)
    cipher = Cipher(algorithms.AES(key_bytes), modes.ECB())
    enc = cipher.encryptor()
    return enc.update(pt) + enc.finalize()


def check(label, actual_hex, expected_hex):
    """Verify actual vs expected. Returns True if ok or no expected."""
    if expected_hex is None:
        print(f'  {label} = {actual_hex}  (no expected — computed fresh)')
        return True
    if actual_hex == expected_hex:
        print(f'  {label} = {actual_hex}  ✓')
        return True
    print(f'  {label} MISMATCH ✗')
    print(f'    got:      {actual_hex}')
    print(f'    expected: {expected_hex}')
    return False


def main():
    print('=' * 72)
    print(' HMAC-512 → ML-KEM-1024 → AES-256-ECB  Reference Vector Generator')
    print('=' * 72)
    print()
    print('Inputs:')
    print(f'  hmac_key  = {HMAC_KEY[:32]}... ({len(HMAC_KEY) // 2} bytes)')
    print(f'  hmac_msg  = {HMAC_MSG[:32]}... ({len(HMAC_MSG) // 2} bytes)')
    print(f'  mlkem_msg = {MLKEM_MSG}')
    print(f'  plaintext = {PLAINTEXT[:32]}... ({len(PLAINTEXT) // 2} bytes)')
    print()

    ok = True

    # --- Step 1: HMAC-512 → seed_d || seed_z ---
    print('Step 1: HMAC-512(key, msg) → seed_d || seed_z ...')
    tag = run_hmac512(HMAC_KEY, HMAC_MSG)
    tag_hex = tag.hex()
    ok &= check('hmac_tag', tag_hex, EXPECTED_HMAC_TAG)

    # Both ML-DSA and ML-KEM cores see seeds as full byte reversal of the
    # HMAC tag bytes.  This is because:
    #   KV path: DWORD reversal in RTL + LE byte read = full byte reversal
    #   FW path: must match by writing BSWAP32(TAG[N-1-i]) to SEED[i]
    # Confirmed by ML-DSA model matching only with reversed seed.
    seed_d = tag[:32][::-1]   # full byte reversal of first 32 bytes
    seed_z = tag[32:][::-1]   # full byte reversal of last 32 bytes
    print(f'  seed_d = {seed_d.hex()}  (full byte reversal)')
    print(f'  seed_z = {seed_z.hex()}  (full byte reversal)')
    print()

    # --- Step 2: ML-KEM-1024 ---
    print('Step 2: ML-KEM-1024 keygen + encaps + decaps ...')
    shared_key = run_mlkem(seed_d, seed_z, MLKEM_MSG)
    sk_hex = shared_key.hex()
    ok &= check('shared_key', sk_hex, EXPECTED_SHARED_KEY)
    # Show shared key as LE DWORDs (matching C register reads)
    sk_dwords = struct.unpack('<8I', shared_key)
    print(f'  shared_key (LE DWORDs): {", ".join(f"0x{d:08X}" for d in sk_dwords)}')
    print()

    # --- Step 3: AES-256-ECB ---
    # The ML-KEM shared key goes through the same full byte reversal
    # as the seed path when written to KV and read by AES:
    #   RTL: mlkem_sharedkey_data[d] = shared_key[7-d] (DWORD reversal)
    #   kv_write_client SWAP_DWORDS=0: KV[d] = data[d] = shared_key[7-d]
    #   AES KV read: aes_key[d][b] = KV_data[3-b] (byte swap per DWORD)
    #   Combined: AES sees full byte reversal of shared_key bytes
    aes_key = shared_key[::-1]
    print(f'Step 3: AES-256-ECB encrypt (shared key byte-reversed as AES key) ...')
    print(f'  aes_key = {aes_key.hex()}')
    ct = run_aes_ecb(aes_key, PLAINTEXT)
    ct_hex = ct.hex()
    ok &= check('ciphertext', ct_hex, EXPECTED_CIPHERTEXT)
    print()

    # --- C code generation ---
    if '--update-c' in sys.argv:
        print('-' * 72)
        print('C defines for smoke_test_mlkem_kv_endian.c:')
        print('-' * 72)
        print()
        print(hex_to_c_dwords(HMAC_KEY, 'HMAC_KEY', per_line=8))
        print()
        print(hex_to_c_dwords(HMAC_MSG, 'HMAC_DATA', per_line=8))
        print()
        print(hex_to_c_string(tag_hex, 'EXPECTED_HMAC_TAG'))
        print()
        print(hex_to_c_dwords(seed_d.hex(), 'SEED_D'))
        print()
        print(hex_to_c_dwords(seed_z.hex(), 'SEED_Z'))
        print()
        print(hex_to_c_dwords(MLKEM_MSG, 'MLKEM_MSG'))
        print()
        print(hex_to_c_string(PLAINTEXT, 'AES_PLAINTEXT'))
        print()
        print(hex_to_c_string(sk_hex, 'EXPECTED_SHARED_KEY'))
        print()
        print(hex_to_c_string(ct_hex, 'EXPECTED_CIPHERTEXT'))
        print()

    # --- Summary ---
    if ok:
        print('ALL CHECKS PASSED ✓')
    else:
        print('SOME CHECKS FAILED ✗')
        sys.exit(1)


if __name__ == '__main__':
    main()
