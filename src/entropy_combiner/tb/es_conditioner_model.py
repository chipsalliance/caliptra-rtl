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
# entropy_src conditioner + dual-iTRNG combine reference model (FIPS mode).
#
# VALIDATED: the FIPS_WINDOW=1024 golden this model emits matches RTL simulation
# (caliptra_top_ss_mode_tb, +CLP_ITRNG1_EN +CLP_DETERMINISTIC_RNG) --
# smoke_test_entropy_combiner_conditioned passed with these exact genbits.
#
# Models the full realistic path used by the conditioner-ENABLED combine test:
#
#   physical_rng_deterministic(seed0) -> ES0 (SHA3-384 conditioner ON) --\
#                                                                          combiner
#   physical_rng_deterministic(seed1) -> ES1 (SHA3-384 conditioner ON) --/  (SHA3-384)
#                                                                            -> CSRNG
#
#   ES_cond_k = SHA3-384( conditioned window of source k )
#   seed      = SHA3-384( ES0_cond || ES1_cond )              (entropy_combiner)
#   genbits   = CTR_DRBG(instantiate=seed).generate(128)      (CSRNG)
#
# The combiner + CSRNG halves are the already-validated model in
# csrng_drbg_model.py; this file only adds the entropy_src conditioner front end.
#
# ---------------------------------------------------------------------------
# entropy_src conditioner facts (verified in entropy_src_core.sv):
#   * Raw RNG delivers 4-bit samples. In 4-lane mode (rng_bit_enable OFF) the
#     health-test window counts SAMPLES: one seed conditions FIPS_WINDOW samples
#     (= FIPS_WINDOW*4 bits). (:1199-1203, :1576-1598, comment :2707-2711)
#   * The FIRST seed after startup absorbs DOUBLE, i.e. 2*FIPS_WINDOW samples,
#     into a single SHA3-384 message. (comment :2707-2711)
#   * Sample->message packing is little-nibble / little-word throughout
#     (postht 4->32, precon 32->64, prim_packer_fifo packs first-in low), the
#     same packing proven by the bypass identity es_bits == InitialSeed, where
#     es_bits[k*4 +: 4] == sample k. So message byte j = s[2j] | (s[2j+1] << 4).
#   * FIPS es_bits = sha3_state[0][383:0] (:2734, :2989), i.e. the SHA3-384
#     digest read little-endian: es_cond = int.from_bytes(digest, 'little').
#     This is the exact convention combiner_digest() already uses.
#
# Constraint: keep FIPS_WINDOW a multiple of 8 samples so the conditioned window
# is a whole number of 64-bit SHA3 message words (FIPS_WINDOW/8 bytes per lane
# ... startup message = FIPS_WINDOW bytes). rng_bit_enable must stay OFF.
#
# The two LFSR seeds below MUST match the physical_rng_deterministic instances in
# src/integration/tb/caliptra_top_tb.sv, and FIPS_WINDOW MUST match the value the
# C test programs into HEALTH_TEST_WINDOWS.FIPS_WINDOW.
# ---------------------------------------------------------------------------

import hashlib

from csrng_drbg_model import combiner_digest, csrng_genbits_words

# LFSR parameters -- must match physical_rng_deterministic.sv exactly.
LFSR_TAPS = 0xEDB88320  # reversed CRC-32 polynomial
SRC0_SEED = 0xDEADBEEF  # caliptra_top_tb physical_rng_det   (ES0)
SRC1_SEED = 0x12345678  # caliptra_top_tb physical_rng1_det  (ES1)


def lfsr_next(s):
    """One Galois right-shift LFSR step (matches the RTL)."""
    return ((s >> 1) ^ LFSR_TAPS) if (s & 1) else (s >> 1)


def next_sample(s):
    """Build one 4-bit sample from 4 consecutive LFSR output bits.

    sample bit b = the b-th LFSR output bit (the LSB shifted out), so
    sample = {b3, b2, b1, b0}. Returns (sample, advanced_state).
    """
    nib = 0
    for b in range(4):
        nib |= (s & 1) << b
        s = lfsr_next(s)
    return nib, s


def rng_samples(lfsr_seed, n):
    """The first n 4-bit samples the deterministic PRNG emits from lfsr_seed."""
    s = lfsr_seed & 0xFFFFFFFF
    out = []
    for _ in range(n):
        nib, s = next_sample(s)
        out.append(nib)
    return out


def es_conditioner(samples):
    """SHA3-384 conditioner over a sample stream -> 384-bit es_bits integer.

    Packing: message byte j = samples[2j] | (samples[2j+1] << 4).
    es_bits = int.from_bytes(SHA3-384(message), 'little').
    """
    assert len(samples) % 2 == 0, "sample count must be even (2 nibbles/byte)"
    msg = bytes(
        (samples[2 * j] | (samples[2 * j + 1] << 4)) for j in range(len(samples) // 2)
    )
    return int.from_bytes(hashlib.sha3_384(msg).digest(), "little")


def es_startup_seed(lfsr_seed, fips_window):
    """First (startup) conditioned ES seed: conditions 2*FIPS_WINDOW samples."""
    return es_conditioner(rng_samples(lfsr_seed, 2 * fips_window))


def rng_seed_slice(lfsr_seed, k, fips_window):
    """The contiguous sample slice consumed for the k-th ES seed.

    Seed 0 is the startup seed (2*FIPS_WINDOW samples); each subsequent
    steady-state seed consumes FIPS_WINDOW samples. Because the deterministic PRNG
    streams a single contiguous sequence (hold-on-disable), seed k maps to a fixed
    slice: k==0 -> [0, 2W); k>=1 -> [2W+(k-1)*W, 2W+k*W).
    """
    W = fips_window
    if k == 0:
        return rng_samples(lfsr_seed, 2 * W)
    start = 2 * W + (k - 1) * W
    return rng_samples(lfsr_seed, start + W)[start:start + W]


def es_seed_k(lfsr_seed, k, fips_window):
    """The k-th conditioned ES seed (k=0 startup, k>=1 steady-state)."""
    return es_conditioner(rng_seed_slice(lfsr_seed, k, fips_window))


def multiseed_genbits(num_seeds, fips_window, num_bits=128,
                      seed0=SRC0_SEED, seed1=SRC1_SEED):
    """Golden CSRNG genbits for num_seeds consecutive combined seeds.

    Each CSRNG (re-)instantiate-from-ES pulls the next combined seed
    SHA3-384(ES0_cond_k || ES1_cond_k); each combine is an independent CTR_DRBG
    instance (uninstantiate resets state).
    """
    out = []
    for k in range(num_seeds):
        es0 = es_seed_k(seed0, k, fips_window)
        es1 = es_seed_k(seed1, k, fips_window)
        seed = combiner_digest(es0, es1)
        out.append(csrng_genbits_words(seed, num_bits))
    return out


def conditioned_startup_genbits(fips_window, num_bits=128,
                                seed0=SRC0_SEED, seed1=SRC1_SEED):
    """Golden CSRNG genbits for the conditioner-enabled combine startup seed."""
    es0 = es_startup_seed(seed0, fips_window)
    es1 = es_startup_seed(seed1, fips_window)
    seed = combiner_digest(es0, es1)
    return es0, es1, seed, csrng_genbits_words(seed, num_bits)


if __name__ == "__main__":
    import sys

    # FIPS_WINDOW in samples; must equal the value the C test programs. Multiple
    # of 8. Default 96 -> startup absorbs 192 samples = 768 bits = 96 message
    # bytes per ES (one SHA3-384 block).
    W = int(sys.argv[1]) if len(sys.argv) > 1 else 96

    # Optional 2nd arg = number of consecutive seeds -> print the multi-seed
    # goldens (Plan E). Otherwise print just the single startup-seed golden.
    if len(sys.argv) > 2:
        n = int(sys.argv[2])
        print(f"FIPS_WINDOW = {W} samples; {n} consecutive combined seeds "
              f"(seed 0 = startup 2xW, seed k>=1 = steady-state 1xW)")
        allw = multiseed_genbits(n, W)
        for k, words in enumerate(allw):
            print(f"EXP_GENBITS_SEED_{k} = {{"
                  + ", ".join(f"0x{w:08x}" for w in words) + "}")
    else:
        es0, es1, seed, words = conditioned_startup_genbits(W)
        print(f"FIPS_WINDOW = {W} samples; startup absorbs {2 * W} samples "
              f"= {2 * W * 4} bits ({W} message bytes) per ES")
        print(f"ES0_cond              = 0x{es0:096x}")
        print(f"ES1_cond              = 0x{es1:096x}")
        print(f"combined seed         = 0x{seed:096x}")
        print("EXP_GENBITS_CONDITIONED = {"
              + ", ".join(f"0x{w:08x}" for w in words) + "}")
