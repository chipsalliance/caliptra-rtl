// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
//----------------------------------------------------------------------
// smoke_test_entropy_combiner_kat
//
// Exercises the entropy_combiner's purpose-built SHA3-384 single-block KAT and
// its MuBi4 AHB_LOCK enforcement over the Caliptra internal AHB. This is
// independent of the ES/CSRNG datapath: the KAT hashes KAT_MSG directly through
// the same ot_sha3 core used for operational entropy combine, so it needs no
// entropy_src/CSRNG programming, no +CLP_ITRNG1_EN, and no combine_en strap. It
// therefore runs in the default caliptra_top_tb build (CALIPTRA_INTERNAL_TRNG,
// which instantiates the combiner).
//
// Part 1 - KAT: for each vector, program KAT_MSG[0..23] (ES0 low words then ES1
//   low words), set KAT_MSG_LEN=96, pulse KAT_CTRL.START, poll KAT_STATUS.VALID,
//   and compare KAT_DIGEST[0..11] against the golden SHA3-384(ES0||ES1). Golden
//   vectors are taken verbatim from tb/entropy_combiner_test_vectors.hex (the
//   same vectors checked behaviorally in entropy_combiner_tb.sv). Word 0 is the
//   least-significant 32 bits of each 384-bit field.
//
// Part 2 - AHB_LOCK: after the KATs, set the W1S MuBi4 AHB_LOCK and verify
//   post-lock enforcement: KAT digest/status scrubbed to 0, KAT cannot run,
//   COMBINER_CTRL FIPS policy frozen, and the lock is sticky (cleared only by
//   reset). AHB_LOCK is not clearable in-sim, so this runs last.
//----------------------------------------------------------------------

#include <stdint.h>
#include <string.h>

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "printf.h"
#include "riscv-csr.h"
#include "riscv_hw_if.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// KAT window is a full 768-bit single block: 96 bytes = 12 x 64-bit beats.
#define KAT_MSG_LEN_BYTES     0x60
// MuBi4 AHB_LOCK codes: MuBi4False=unlocked (reset), MuBi4True=locked.
#define AHB_LOCK_UNLOCKED     0x9
#define AHB_LOCK_LOCKED       0x6
// COMBINER_CTRL.es_fips_policy values used for the freeze check (mask 0x3).
#define ES_FIPS_POLICY_ES0    0x1  // PRIMARY_ES0_ONLY (programmed before lock)
#define ES_FIPS_POLICY_ALT    0x2  // CONFIG_VALUE     (rejected after lock)

#define NUM_KAT_VECTORS 4

// Golden KAT vectors from tb/entropy_combiner_test_vectors.hex, split into
// 32-bit words with word 0 = least-significant 32 bits of the 384-bit field.
//   A: ES0=0, ES1=0                      (baseline)
//   B: ES0 word0=1, ES1=0               (ES0-half ordering guard)
//   C: ES0=0, ES1 word0=1               (ES1-half ordering guard)
//   D: fully asymmetric byte-ramp       (intra-half word/byte ordering guard)
static const uint32_t kat_es0[NUM_KAT_VECTORS][12] = {
  { 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000 },
  { 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000 },
  { 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000 },
  { 0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514,
    0x1b1a1918, 0x1f1e1d1c, 0x23222120, 0x27262524, 0x2b2a2928, 0x2f2e2d2c },
};
static const uint32_t kat_es1[NUM_KAT_VECTORS][12] = {
  { 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000 },
  { 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000 },
  { 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000 },
  { 0x33323130, 0x37363534, 0x3b3a3938, 0x3f3e3d3c, 0x43424140, 0x47464544,
    0x4b4a4948, 0x4f4e4d4c, 0x53525150, 0x57565554, 0x5b5a5958, 0x5f5e5d5c },
};
static const uint32_t kat_digest[NUM_KAT_VECTORS][12] = {
  { 0x3f9645f1, 0x50f31c99, 0xe2980056, 0x63800b09, 0x0ea1501b, 0xc0a6226f,
    0x366425e0, 0x34c27ca8, 0xa014c0b4, 0x1d93b4b3, 0xb164bc4e, 0x5f83c342 },
  { 0x5178ea39, 0x35d4cab0, 0xfcc8815e, 0x279c4b82, 0xd2534c13, 0x14dba5b6,
    0x5f25544f, 0xef27d4e3, 0x261d6135, 0x159026b4, 0xc4b4ffdc, 0xc8498f63 },
  { 0x9aa7d72f, 0x9d30da3b, 0x7d91f1c8, 0xd1daff51, 0xa66d8268, 0xa32290b7,
    0x77eec90d, 0x8a9bb77e, 0x668dd7aa, 0xc4d2d741, 0xaf6f1897, 0x75bb7a63 },
  { 0x9766e2d6, 0xd4dc3f0a, 0x86da33a8, 0x9a179915, 0x69570b06, 0xb493e959,
    0x30298569, 0x238ce34e, 0x702a10c7, 0x68d5c484, 0x2355d9b1, 0xe77740d1 },
};

// read data and compare against expected value. If there is no error, return 0
int read_and_compare(uint32_t addr, uint32_t exp_data) {
  uint32_t act_data;
  act_data = lsu_read_32(addr);
  if (act_data != exp_data) {
    VPRINTF(ERROR, "Got:%x Want:%x @%x\n", act_data, exp_data, addr);
    return 1;
  }
  return 0;
}

// poll a register until value read back matches expected value
void poll_reg(uint32_t addr, uint32_t expected_data) {
  uint32_t read_data;

  VPRINTF(LOW, "  - Polling addr=%x until it reads back %x...\n", addr,
         expected_data);
  do {
    read_data = lsu_read_32(addr);
  } while (read_data != expected_data);
}

// Program one KAT vector, run it, and check the digest. Returns error count.
int run_kat(const uint32_t es0[12], const uint32_t es1[12],
            const uint32_t exp_digest[12]) {
  int error = 0;
  int i;

  // KAT_MSG[0..11] = ES0 low-word-first, KAT_MSG[12..23] = ES1 low-word-first,
  // matching the operational ES0||ES1 SHA3 feed.
  for (i = 0; i < 12; i++) {
    lsu_write_32(CLP_ENTROPY_COMBINER_REG_KAT_MSG_0 + (uint32_t)(4 * i), es0[i]);
  }
  for (i = 0; i < 12; i++) {
    lsu_write_32(CLP_ENTROPY_COMBINER_REG_KAT_MSG_0 + (uint32_t)(4 * (12 + i)),
                 es1[i]);
  }

  lsu_write_32(CLP_ENTROPY_COMBINER_REG_KAT_MSG_LEN, KAT_MSG_LEN_BYTES);

  // START is a W1 single-pulse; it also clears any previous KAT_STATUS.VALID.
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_KAT_CTRL,
               ENTROPY_COMBINER_REG_KAT_CTRL_START_MASK);

  // Completion: BUSY clears (0) and VALID sets (1) => status == VALID_MASK.
  poll_reg(CLP_ENTROPY_COMBINER_REG_KAT_STATUS,
           ENTROPY_COMBINER_REG_KAT_STATUS_VALID_MASK);

  for (i = 0; i < 12; i++) {
    error += read_and_compare(
        CLP_ENTROPY_COMBINER_REG_KAT_DIGEST_0 + (uint32_t)(4 * i),
        exp_digest[i]);
  }

  return error;
}

int run_kat_tests() {
  int error = 0;
  int v;

  VPRINTF(LOW, "\nEntropy Combiner SHA3-384 KAT\n");
  for (v = 0; v < NUM_KAT_VECTORS; v++) {
    VPRINTF(LOW, "  - KAT vector %d\n", v);
    error += run_kat(kat_es0[v], kat_es1[v], kat_digest[v]);
  }
  return error;
}

int run_ahb_lock_test() {
  int error = 0;
  int i;
  uint32_t status;

  VPRINTF(LOW, "\nEntropy Combiner AHB_LOCK Enforcement Test\n");

  // 1. Pre-lock sanity: AHB_LOCK reads unlocked (MuBi4False).
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_AHB_LOCK, AHB_LOCK_UNLOCKED);

  // 2. Program a FIPS policy while unlocked; it must take (swwe = !lock).
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL, ES_FIPS_POLICY_ES0);
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL,
                            ES_FIPS_POLICY_ES0);

  // 3. Lock: write MuBi4True.
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_AHB_LOCK, AHB_LOCK_LOCKED);

  // 4. Confirm locked.
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_AHB_LOCK, AHB_LOCK_LOCKED);

  // 5a. KAT state scrubbed: every KAT_DIGEST word and KAT_STATUS read 0.
  for (i = 0; i < 12; i++) {
    error += read_and_compare(
        CLP_ENTROPY_COMBINER_REG_KAT_DIGEST_0 + (uint32_t)(4 * i), 0x0);
  }
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_KAT_STATUS, 0x0);

  // 5b. KAT cannot run while locked: program a fresh message and pulse START;
  //     KAT_STATUS must never go busy/valid and KAT_DIGEST must stay 0.
  for (i = 0; i < 24; i++) {
    lsu_write_32(CLP_ENTROPY_COMBINER_REG_KAT_MSG_0 + (uint32_t)(4 * i),
                 0xA5A5A5A5);
  }
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_KAT_MSG_LEN, KAT_MSG_LEN_BYTES);
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_KAT_CTRL,
               ENTROPY_COMBINER_REG_KAT_CTRL_START_MASK);
  for (i = 0; i < 32; i++) {
    status = lsu_read_32(CLP_ENTROPY_COMBINER_REG_KAT_STATUS);
    if (status != 0x0) {
      VPRINTF(ERROR, "KAT ran while locked: KAT_STATUS=%x\n", status);
      error += 1;
      break;
    }
  }
  for (i = 0; i < 12; i++) {
    error += read_and_compare(
        CLP_ENTROPY_COMBINER_REG_KAT_DIGEST_0 + (uint32_t)(4 * i), 0x0);
  }

  // 5c. FIPS policy frozen: a write to a different value must be rejected.
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL, ES_FIPS_POLICY_ALT);
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL,
                            ES_FIPS_POLICY_ES0);

  // 5d. Lock sticky: an unlock attempt must be ignored (W1S, clears on reset).
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_AHB_LOCK, AHB_LOCK_UNLOCKED);
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_AHB_LOCK, AHB_LOCK_LOCKED);

  // 6. COMBINER_STATUS is a read-only strap mirror, still readable after lock.
  status = lsu_read_32(CLP_ENTROPY_COMBINER_REG_COMBINER_STATUS);
  VPRINTF(LOW, "COMBINER_STATUS=%x (combine_en=%x)\n", status,
          status & ENTROPY_COMBINER_REG_COMBINER_STATUS_COMBINE_EN_MASK);

  return error;
}

void main() {
  int error = 0;

  VPRINTF(LOW, "----------------------------------------\n");
  VPRINTF(LOW, " Entropy Combiner KAT + AHB_LOCK Test \n");
  VPRINTF(LOW, "----------------------------------------\n");

  // KAT functional test first; the AHB lock is sticky until reset, so the lock
  // enforcement test must run last.
  error += run_kat_tests();
  error += run_ahb_lock_test();

  if (error > 0) {
    VPRINTF(ERROR, "Error: %d\n", error);
    SEND_STDOUT_CTRL(0x1);
  } else {
    VPRINTF(LOW, "Entropy combiner KAT and AHB_LOCK checks passed\n");
    SEND_STDOUT_CTRL(0xff);
  }
}
