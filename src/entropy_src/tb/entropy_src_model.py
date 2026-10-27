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
# entropy_src reference model for the smoke_test_entropy_src_* tests.
#
# Predicts the seeds entropy_src delivers to firmware (ENTROPY_DATA) when it is
# fed by physical_rng_deterministic (caliptra_top_tb, +CLP_DETERMINISTIC_RNG),
# and computes the health test thresholds as described in the integration
# specification.
#
# Reuses the validated conditioner model of the entropy combiner tests
# (src/entropy_combiner/tb/es_conditioner_model.py): LFSR, sample stream and
# SHA3-384 conditioner with little-nibble packing.
#
# Additional entropy_src facts:
#   * Single-lane mode (CONF.RNG_BIT_ENABLE): the selected lane is
#     sample[RNG_BIT_SEL]. The esbit packer (InW=1, OutW=4) packs the first bit
#     into the LSB, so 4 consecutive lane bits form one 4-bit group, which then
#     follows the same path as a 4-lane sample. A window of W samples covers W
#     bits of the selected lane.
#   * Boot-time / bypass mode (CONF.FIPS_ENABLE disabled): the seed is the
#     first BYPASS_WINDOW tested bits, not conditioned:
#     es_bits[k*4 +: 4] = 4-bit group k.
#   * FIPS mode: seed 0 (startup) conditions 2 windows, every following seed
#     one window.
#   * ENTROPY_DATA returns es_bits[i*32 +: 32] for the i-th read (i = 0..11).
#
# The deterministic RNG restarts from its LFSR seed whenever entropy_src is
# disabled, so every configuration (disable, reconfigure, enable) starts from
# the first sample of the stream.
# ---------------------------------------------------------------------------

import argparse
import math
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', '..', 'entropy_combiner', 'tb'))
from es_conditioner_model import SRC0_SEED, es_conditioner, rng_samples  # noqa: E402

SEED_WORDS = 12
BYPASS_WINDOW = 384


# ------------------------------- data path ---------------------------------
def tested_groups(samples, single_lane, lane):
    """4-bit groups entering the post health test path.

    4-lane mode: the samples themselves. Single-lane mode: the bits of the
    selected lane, packed first-bit-in-LSB into 4-bit groups.
    """
    if not single_lane:
        return list(samples)
    bits = [(s >> lane) & 1 for s in samples]
    assert len(bits) % 4 == 0
    return [bits[i] | bits[i + 1] << 1 | bits[i + 2] << 2 | bits[i + 3] << 3
            for i in range(0, len(bits), 4)]


def boot_seed(single_lane, lane=0, lfsr_seed=SRC0_SEED):
    """Boot-time / bypass seed: the first BYPASS_WINDOW tested bits."""
    samples_per_window = BYPASS_WINDOW if single_lane else BYPASS_WINDOW // 4
    groups = tested_groups(rng_samples(lfsr_seed, samples_per_window), single_lane, lane)
    return sum(g << (4 * k) for k, g in enumerate(groups))


def fips_seed(k, fips_window, single_lane, lane=0, lfsr_seed=SRC0_SEED):
    """k-th FIPS mode seed (k=0 startup: 2 windows, k>=1: 1 window)."""
    w = fips_window
    start, length = (0, 2 * w) if k == 0 else (2 * w + (k - 1) * w, w)
    samples = rng_samples(lfsr_seed, start + length)[start:]
    return es_conditioner(tested_groups(samples, single_lane, lane))


def seed_words(seed):
    return [(seed >> (32 * i)) & 0xFFFFFFFF for i in range(SEED_WORDS)]


# ------------------------------ thresholds ---------------------------------
def critbinom(n, p, a):
    """Smallest k with P(X <= k) >= a for X ~ Binomial(n, p)."""
    from decimal import Decimal, getcontext
    getcontext().prec = 80
    p = Decimal(p)
    q = 1 - p
    a = Decimal(a)
    cdf = Decimal(0)
    term = q ** n
    for k in range(n + 1):
        if k > 0:
            term = term * Decimal(n - k + 1) / Decimal(k) * p / q
        cdf += term
        if cdf >= a:
            return k
    return n


def apt_cutoff(w, h, alpha_log2):
    """NIST SP 800-90B Adaptive Proportion test cutoff C (Section 4.4.2)."""
    from decimal import Decimal
    p = Decimal(2) ** Decimal(-h)
    a = 1 - Decimal(2) ** -alpha_log2
    return 1 + critbinom(w, p, a)


def rct_cutoff(h, alpha_log2):
    """NIST SP 800-90B Repetition Count test cutoff C (Section 4.4.1)."""
    return 1 + math.ceil(alpha_log2 / h)


def thresholds(fips, single_lane, fips_window, h_bit, h_symbol, alpha_log2):
    """Thresholds as described in the integration specification.

    Single-lane mode: ADAPTP and REPCNT configured, ADAPTPS and REPCNTS left at
    their reset values. 4-bit symbol mode: ADAPTPS and REPCNTS configured,
    ADAPTP and REPCNT left at their reset values. The window size is the one of
    the operating mode (FIPS_WINDOW or BYPASS_WINDOW).
    """
    t = dict(repcnt=0xFFFF, repcnts=0xFFFF, adaptp_hi=0xFFFF, adaptp_lo=0x0,
             adaptps=0xFFFF)
    if single_lane:
        n = fips_window if fips else BYPASS_WINDOW
        c = apt_cutoff(n, h_bit, alpha_log2)
        t['adaptp_hi'] = c
        t['adaptp_lo'] = max(0, n - c)
        t['repcnt'] = rct_cutoff(h_bit, alpha_log2)
    else:
        w = fips_window if fips else BYPASS_WINDOW // 4
        t['adaptps'] = apt_cutoff(w, h_symbol, alpha_log2)
        t['repcnts'] = rct_cutoff(h_symbol, alpha_log2)
    return t


# ---------------------------------- CLI ------------------------------------
# Configurations of smoke_test_entropy_src: (name, FIPS mode, single lane, lane,
# FIPS_WINDOW, skipped seeds). The FIPS windows are the NIST SP 800-90B window
# sizes for non-binary (4-bit symbols) and binary (single lane) noise sources.
#
# When entropy_src is disabled in FIPS mode, the conditioner is already
# absorbing the next window, and this partial message is left in the SHA3
# sponge (see sha3_start_mask in entropy_src_core.sv). The startup seed of the
# next FIPS configuration therefore also contains this leftover data, whose size
# depends on the firmware timing. Its startup seed is read and skipped, and the
# following seeds are checked.
SMOKE_TEST_CONFIGS = [
    ('boot-time mode, 4-bit symbols', False, False, 0, 512,  0),
    ('boot-time mode, single lane',   False, True,  2, 1024, 0),
    ('FIPS mode, 4-bit symbols',      True,  False, 0, 512,  0),
    ('FIPS mode, single lane',        True,  True,  2, 1024, 1),
]


def c_header(num_seeds, h_bit, h_symbol, alpha_log2):
    out = [f"// Generated by src/entropy_src/tb/entropy_src_model.py {' '.join(sys.argv[1:])}",
           f"// Thresholds: H = {h_bit} per bit / {h_symbol} per 4-bit symbol, "
           f"alpha = 2^-{alpha_log2}",
           "",
           "#ifndef ES_VECTORS_H",
           "#define ES_VECTORS_H",
           "",
           "#include <stdint.h>",
           "",
           f"#define ES_SEED_WORDS  {SEED_WORDS}",
           f"#define ES_NUM_CONFIGS {len(SMOKE_TEST_CONFIGS)}",
           f"#define ES_MAX_SEEDS   {num_seeds}",
           "",
           "typedef struct {",
           "  const char *name;",
           "  uint32_t    fips_mode;    // 1: FIPS mode, 0: boot-time / bypass mode",
           "  uint32_t    single_lane;  // 1: single-lane mode (CONF.RNG_BIT_ENABLE)",
           "  uint32_t    lane;         // CONF.RNG_BIT_SEL",
           "  uint32_t    fips_window;  // HEALTH_TEST_WINDOWS.FIPS_WINDOW, in samples",
           "  uint32_t    repcnt_thresh;",
           "  uint32_t    repcnts_thresh;",
           "  uint32_t    adaptp_hi_thresh;",
           "  uint32_t    adaptp_lo_thresh;",
           "  uint32_t    adaptps_thresh;",
           "  uint32_t    skip_seeds;   // seeds read and skipped before the checked ones",
           "  uint32_t    num_seeds;",
           "  uint32_t    exp_seeds[ES_MAX_SEEDS][ES_SEED_WORDS];",
           "} es_test_cfg_t;",
           "",
           "static const es_test_cfg_t es_configs[ES_NUM_CONFIGS] = {"]
    for name, fips, single_lane, lane, fips_window, skip in SMOKE_TEST_CONFIGS:
        t = thresholds(fips, single_lane, fips_window, h_bit, h_symbol, alpha_log2)
        seeds = ([boot_seed(single_lane, lane)] if not fips else
                 [fips_seed(k, fips_window, single_lane, lane)
                  for k in range(skip, skip + num_seeds)])
        out += [f"  {{ // {name}",
                f"    .name = \"{name}\", .fips_mode = {int(fips)}, "
                f".single_lane = {int(single_lane)}, .lane = {lane}, "
                f".fips_window = {fips_window},",
                f"    .repcnt_thresh = 0x{t['repcnt']:04x}, "
                f".repcnts_thresh = 0x{t['repcnts']:04x}, "
                f".adaptp_hi_thresh = 0x{t['adaptp_hi']:04x}, "
                f".adaptp_lo_thresh = 0x{t['adaptp_lo']:04x}, "
                f".adaptps_thresh = 0x{t['adaptps']:04x},",
                f"    .skip_seeds = {skip}, .num_seeds = {len(seeds)},",
                "    .exp_seeds = {"]
        for s in seeds:
            w = seed_words(s)
            out.append("      {" + ", ".join(f"0x{x:08x}" for x in w[:6]) + ",")
            out.append("       " + ", ".join(f"0x{x:08x}" for x in w[6:]) + "},")
        out += ["    },", "  },"]
    out += ["};", "", "#endif // ES_VECTORS_H"]
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--num-seeds', type=int, default=2,
                    help='Number of seeds checked in FIPS mode')
    ap.add_argument('--h-bit', type=float, default=0.5)
    ap.add_argument('--h-symbol', type=float, default=2.0)
    ap.add_argument('--alpha-log2', type=int, default=40)
    a = ap.parse_args()
    print(c_header(a.num_seeds, a.h_bit, a.h_symbol, a.alpha_log2))


if __name__ == '__main__':
    main()
