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
# ---------------------------------------------------------------------------
# csrng_drbg_model.py
#
# Reference model for the caliptra/OpenTitan CSRNG CTR_DRBG (AES-256, no
# derivation function), used to predict the genbits CSRNG produces when it is
# seeded from the entropy interface (i.e. from the entropy combiner).
#
# Self-checks against the KATs baked into src/csrng/tb/csrng_tb.sv:
#   * run_entropy_source_seed_test: instantiate(entropy seed) + generate 128b
#       seed    = 0x33F63B65...B7DE947
#       genbits = 0x15eb2a44 310851dd ba1365ab 4c7322f4
#
# Pure-Python AES-256 (stdlib only) so no external crypto package is needed.
# ---------------------------------------------------------------------------

# ------------------------- AES-256 (ECB, encrypt) --------------------------
_SBOX = []
_RCON = []


def _init_aes_tables():
    global _SBOX, _RCON
    p = 1
    q = 1
    sbox = [0] * 256
    # Generate S-box using the standard GF(2^8) construction.
    sbox[0] = 0x63
    while True:
        # p = p * 3
        p = p ^ ((p << 1) & 0xFF) ^ (0x1B if (p & 0x80) else 0)
        # q = q / 3 (q = q * 0xf6)
        q ^= (q << 1) & 0xFF
        q ^= (q << 2) & 0xFF
        q ^= (q << 4) & 0xFF
        q ^= 0x09 if (q & 0x80) else 0
        q &= 0xFF
        xformed = q ^ ((q << 1) | (q >> 7)) ^ ((q << 2) | (q >> 6)) \
            ^ ((q << 3) | (q >> 5)) ^ ((q << 4) | (q >> 4))
        sbox[p] = (xformed ^ 0x63) & 0xFF
        if p == 1:
            break
    _SBOX = sbox
    rcon = [0x8D]
    c = 1
    for _ in range(1, 16):
        rcon.append(c)
        c = ((c << 1) ^ (0x11B if (c & 0x80) else 0)) & 0xFF
    _RCON = rcon


_init_aes_tables()


def _xtime(a):
    return ((a << 1) ^ 0x1B) & 0xFF if (a & 0x80) else (a << 1)


def _mul(a, b):
    res = 0
    for _ in range(8):
        if b & 1:
            res ^= a
        b >>= 1
        a = _xtime(a)
    return res & 0xFF


def _key_expansion_256(key_bytes):
    # 32-byte key -> 60 words (Nb*(Nr+1) = 4*15) of 4 bytes.
    Nk = 8
    Nr = 14
    w = [list(key_bytes[4 * i:4 * i + 4]) for i in range(Nk)]
    for i in range(Nk, 4 * (Nr + 1)):
        temp = list(w[i - 1])
        if i % Nk == 0:
            temp = temp[1:] + temp[:1]  # RotWord
            temp = [_SBOX[b] for b in temp]  # SubWord
            temp[0] ^= _RCON[i // Nk]
        elif i % Nk == 4:
            temp = [_SBOX[b] for b in temp]
        w.append([w[i - Nk][j] ^ temp[j] for j in range(4)])
    return w


def _add_round_key(state, w, rnd):
    for c in range(4):
        for r in range(4):
            state[r][c] ^= w[rnd * 4 + c][r]


def _sub_bytes(state):
    for r in range(4):
        for c in range(4):
            state[r][c] = _SBOX[state[r][c]]


def _shift_rows(state):
    for r in range(1, 4):
        state[r] = state[r][r:] + state[r][:r]


def _mix_columns(state):
    for c in range(4):
        a = [state[r][c] for r in range(4)]
        state[0][c] = _mul(a[0], 2) ^ _mul(a[1], 3) ^ a[2] ^ a[3]
        state[1][c] = a[0] ^ _mul(a[1], 2) ^ _mul(a[2], 3) ^ a[3]
        state[2][c] = a[0] ^ a[1] ^ _mul(a[2], 2) ^ _mul(a[3], 3)
        state[3][c] = _mul(a[0], 3) ^ a[1] ^ a[2] ^ _mul(a[3], 2)


def aes256_encrypt_block(key_bytes, block_bytes):
    """AES-256 ECB encrypt of one 16-byte block. Big-endian byte order."""
    Nr = 14
    w = _key_expansion_256(key_bytes)
    state = [[block_bytes[r + 4 * c] for c in range(4)] for r in range(4)]
    _add_round_key(state, w, 0)
    for rnd in range(1, Nr):
        _sub_bytes(state)
        _shift_rows(state)
        _mix_columns(state)
        _add_round_key(state, w, rnd)
    _sub_bytes(state)
    _shift_rows(state)
    _add_round_key(state, w, Nr)
    return bytes(state[r + 4 * c] if False else state[r][c]
                 for c in range(4) for r in range(4))


# --------------------------- CTR_DRBG (AES-256) ----------------------------
KEYLEN = 256
BLOCKLEN = 128
SEEDLEN = 384
CTRLEN = BLOCKLEN  # full-width counter


class CtrDrbg:
    """AES-256 CTR_DRBG without a derivation function (SP 800-90A)."""

    def __init__(self):
        self.key = bytes(KEYLEN // 8)
        self.v = bytes(BLOCKLEN // 8)

    def _inc_v(self):
        val = (int.from_bytes(self.v, 'big') + 1) & ((1 << BLOCKLEN) - 1)
        self.v = val.to_bytes(BLOCKLEN // 8, 'big')

    def _update(self, provided_data):
        temp = b''
        while len(temp) < SEEDLEN // 8:
            self._inc_v()
            temp += aes256_encrypt_block(self.key, self.v)
        temp = temp[:SEEDLEN // 8]
        pd = provided_data if provided_data else bytes(SEEDLEN // 8)
        temp = bytes(a ^ b for a, b in zip(temp, pd))
        self.key = temp[:KEYLEN // 8]
        self.v = temp[KEYLEN // 8:SEEDLEN // 8]

    def instantiate(self, entropy_input, personalization=b''):
        seed_material = entropy_input
        if personalization:
            seed_material = bytes(a ^ b for a, b in
                                  zip(entropy_input, personalization))
        self.key = bytes(KEYLEN // 8)
        self.v = bytes(BLOCKLEN // 8)
        self._update(seed_material)

    def generate(self, num_bits, additional_input=b''):
        if additional_input:
            self._update(additional_input)
        temp = b''
        while len(temp) < num_bits // 8:
            self._inc_v()
            temp += aes256_encrypt_block(self.key, self.v)
        returned = temp[:num_bits // 8]
        self._update(additional_input if additional_input else None)
        return returned


def csrng_generate(seed_int, num_bits):
    """Instantiate CSRNG from a 384-bit entropy seed, then generate num_bits.
    Returns the genbits as a big integer (MSB first)."""
    drbg = CtrDrbg()
    drbg.instantiate(seed_int.to_bytes(SEEDLEN // 8, 'big'))
    out = drbg.generate(num_bits)
    return int.from_bytes(out, 'big')


def csrng_genbits_words(seed_int, num_bits):
    """Genbits as the sequence of 32-bit words in CSRNG GENBITS read order.

    Each 128-bit block is read least-significant-word first (word[0] =
    genbits_bus[31:0]); successive blocks follow in generation order.
    """
    drbg = CtrDrbg()
    drbg.instantiate(seed_int.to_bytes(SEEDLEN // 8, 'big'))
    out = drbg.generate(num_bits)
    words = []
    for blk in range(num_bits // 128):
        block = out[blk * 16:blk * 16 + 16]
        bval = int.from_bytes(block, 'big')
        for i in range(4):  # LSW first
            words.append((bval >> (32 * i)) & 0xFFFFFFFF)
    return words


# -------- Composition with the entropy combiner (SHA3-384 of ES0||ES1) ------
def combiner_digest(es0_int, es1_int):
    """Entropy-combiner output = SHA3-384(ES0 || ES1), matching the combiner
    RTL byte order (each 384-bit seed is little-endian on the wire)."""
    import hashlib
    msg = es0_int.to_bytes(48, 'little') + es1_int.to_bytes(48, 'little')
    return int.from_bytes(hashlib.sha3_384(msg).digest(), 'little')


def chain_genbits_words(es0_int, es1_int, num_bits):
    """Full chain: two entropy_src raw seeds -> combiner -> CSRNG genbits."""
    return csrng_genbits_words(combiner_digest(es0_int, es1_int), num_bits)


# ------------------------------- self-test ---------------------------------
def _aes_kat():
    # FIPS-197 AES-256 known-answer test.
    key = bytes(range(0x00, 0x20))
    pt = bytes([0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
                0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF])
    ct = aes256_encrypt_block(key, pt).hex()
    assert ct == '8ea2b7ca516745bfeafc49904b496089', ct
    print('AES-256 FIPS-197 KAT OK')


def _csrng_entropy_kat():
    seed = 0x33F63B65F57AD68765693560E743CC5010518E4BF4ECBEBA71DC56AAA08B394311731D9DF763FC5D27E4ED3E4B7DE947
    exp_words = [0x15eb2a44, 0x310851dd, 0xba1365ab, 0x4c7322f4]
    got_words = csrng_genbits_words(seed, 128)
    print('CSRNG entropy-seed KAT (128b generate):')
    print('  seed =', format(seed, '096x'))
    print('  exp  =', ' '.join(f'{w:08x}' for w in exp_words))
    print('  got  =', ' '.join(f'{w:08x}' for w in got_words))
    return got_words == exp_words


def _csrng_smoke_kat():
    # run_smoke_test: instantiate with in-band 384b seed, generate 512b.
    seed_words = [0x73BEC010, 0x9262474c, 0x16a30f76, 0x531b51de,
                  0x2ee494e5, 0xdfec9db3, 0xcb7a879d, 0x5600419c,
                  0xca79b0b0, 0xdda33b5c, 0xa468649e, 0xdf5d73fa]
    # The 12 command words map LSW-first into the 384-bit seed (first CMD_REQ
    # word written is the least-significant 32 bits).
    seed = 0
    for w in reversed(seed_words):
        seed = (seed << 32) | w
    exp = [0x378FCA1E, 0xcf763d08, 0x17166e90, 0x0b165308,
           0x359fbe3e, 0xa69B1Bf1, 0x14117211, 0xc01a0839,
           0x58d7e45d, 0xc5e00eb8, 0xce7ab38f, 0x6e48e546,
           0x49de93f9, 0x88A65Ec7, 0xc58a553e, 0x5d6e1012]
    got = csrng_genbits_words(seed, 512)
    ok = got == exp
    print('CSRNG in-band-seed KAT (512b generate):', 'PASS' if ok else 'DIFF')
    if not ok:
        print('  exp =', ' '.join(f'{w:08x}' for w in exp))
        print('  got =', ' '.join(f'{w:08x}' for w in got))
    return ok


def _print_chain_expected():
    # IS0 / IS1 used by entropy_combiner_es_integration_tb.
    IS0 = 0x33f63b65f57ad68765693560e743cc5010518e4bf4ecbeba71dc56aaa08b394311731d9df763fc5d27e4ed3e4b7de947
    IS1 = 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e9587f9e1a34b2d0c7658493a1fbe6d2c0a
    dg = combiner_digest(IS0, IS1)
    words = chain_genbits_words(IS0, IS1, 128)
    print('Chain ES0/ES1 -> combiner -> CSRNG (128b generate):')
    print('  combiner digest =', format(dg, '096x'))
    print('  CSRNG genbits    =', ' '.join(f'{w:08x}' for w in words))
    return words


if __name__ == '__main__':
    _aes_kat()
    ok = _csrng_entropy_kat()
    print('CSRNG entropy-seed KAT', 'PASS' if ok else 'FAIL')
    _csrng_smoke_kat()
    _print_chain_expected()
