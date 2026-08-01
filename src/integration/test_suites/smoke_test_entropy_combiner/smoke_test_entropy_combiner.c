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
// smoke_test_entropy_combiner
//
// Exercises the real dual-iTRNG entropy datapath in combine mode:
//
//   physical_rng (IS0) --itrng--> entropy_src ES0 --\
//                                                     entropy_combiner --> CSRNG
//   physical_rng1(IS1) --itrng--> entropy_src ES1 --/   (SHA3-384)
//
// With combine mode enabled (dual_iTRNG_en strap = 1, set via +CLP_ITRNG1_EN),
// the combiner delivers SHA3-384(IS0 || IS1) as the CSRNG seed instead of the
// ES0-only bypass seed. CSRNG then instantiates from that seed and generates
// 128 bits, which are checked against the golden value computed by the isolated
// entropy_combiner_es_csrng_tb / csrng_drbg_model.py reference model.
//
// This is the same flow as smoke_test_trng (which runs the combiner in bypass,
// ES0 only), except that ES1 is also enabled and combine mode is active, so the
// expected genbits differ (EXP_GENBITS_COMBINE vs EXP_GENBITS_BYPASS).
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

// Combine-mode genbits: seed = SHA3-384(IS0 || IS1), where
//   IS0 = physical_rng  InitialSeed (0x33f63b65...b7de947)
//   IS1 = physical_rng1 InitialSeed (0x9e3779b9...be6d2c0a)
// Golden value taken verbatim from EXP_GENBITS_COMBINE in
// src/entropy_combiner/tb/entropy_combiner_es_csrng_tb.sv (LSW read first).
#define EXP_GENBITS_COMBINE_0 0xae5f5d34
#define EXP_GENBITS_COMBINE_1 0x43f0422c
#define EXP_GENBITS_COMBINE_2 0x0057f623
#define EXP_GENBITS_COMBINE_3 0x08c811aa

// Raw entropy_src config used for a deterministic seed: FIPS/health-test
// conditioning off (CONF) and MODULE_ENABLE on, so es_bits == the InitialSeed
// streamed by physical_rng (identity packing). Same values as smoke_test_trng.
#define ES_CONF_RAW          0x2649999
#define ES_MODULE_ENABLE      0x6
// ES1's register map is ES0's base + 0x1000.
#define ES1_OFFSET (CLP_ENTROPY_SRC1_REG_BASE_ADDR - CLP_ENTROPY_SRC_REG_BASE_ADDR)

// read data and compare against expected value. If there is no error, return 0
int read_and_compare(uint32_t addr, uint32_t exp_data) {
  uint32_t act_data;
  act_data = lsu_read_32(addr);
  if (act_data != exp_data) {
    VPRINTF(ERROR, "Got:%x Want: %x", act_data, exp_data);
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

void end_sim_if_itrng_disabled() {
  uint32_t hw_cfg;
  hw_cfg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
  if (hw_cfg & SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK) {
    VPRINTF(LOW, "Internal TRNG is enabled, running entropy combiner test\n");
  } else {
    VPRINTF(FATAL, "Internal TRNG is not enabled, skipping entropy combiner test\n");
    SEND_STDOUT_CTRL(0xFF);
    while (1)
      ;
  }
}

// Combine mode (SHA3-384 of ES0||ES1) is only active when the dual_iTRNG_en
// strap is set. That strap requires a subsystem-mode build (CALIPTRA_MODE_SUBSYSTEM
// + CALIPTRA_INTERNAL_TRNG, i.e. the caliptra_top_ss_mode_tb target) AND the
// +CLP_ITRNG1_EN plusarg; it is reflected in CPTRA_HW_CONFIG.dual_iTRNG_en.
// Without it the combiner bypasses ES1 and the golden combine value can never be
// produced, so gracefully skip (like the itrng-disabled case) rather than report
// a false failure when the test is launched in a non-subsystem configuration.
void end_sim_if_dual_itrng_disabled() {
  uint32_t hw_cfg;
  hw_cfg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
  if (hw_cfg & SOC_IFC_REG_CPTRA_HW_CONFIG_DUAL_ITRNG_EN_MASK) {
    VPRINTF(LOW, "Dual iTRNG (combine mode) is enabled\n");
  } else {
    VPRINTF(FATAL, "Dual iTRNG not enabled (needs ss_mode build + CLP_ITRNG1_EN); skipping combiner test\n");
    SEND_STDOUT_CTRL(0xFF);
    while (1)
      ;
  }
}

// Enable one entropy_src block with the raw (deterministic) config, then verify
// the config read-back is as expected (CONF/MODULE_ENABLE took, no recoverable
// config alert). es_offset is 0 for ES0, ES1_OFFSET for ES1. Returns error count.
int enable_entropy_src(uint32_t es_offset) {
  int error = 0;
  lsu_write_32(CLP_ENTROPY_SRC_REG_CONF + es_offset, ES_CONF_RAW);
  lsu_write_32(CLP_ENTROPY_SRC_REG_MODULE_ENABLE + es_offset, ES_MODULE_ENABLE);

  error += read_and_compare(CLP_ENTROPY_SRC_REG_CONF + es_offset, ES_CONF_RAW);
  error += read_and_compare(CLP_ENTROPY_SRC_REG_MODULE_ENABLE + es_offset,
                            ES_MODULE_ENABLE);
  error += read_and_compare(CLP_ENTROPY_SRC_REG_RECOV_ALERT_STS + es_offset, 0x0);
  return error;
}

int enable_combiner_chain() {
  int error = 0;
  // Both entropy_src blocks feed the combiner in combine mode, so both must be
  // enabled with the same raw config before CSRNG requests a seed.
  VPRINTF(LOW, "Enabling entropy_src ES0\n");
  error += enable_entropy_src(0);

  VPRINTF(LOW, "Enabling entropy_src ES1\n");
  error += enable_entropy_src(ES1_OFFSET);

  VPRINTF(LOW, "Enabling csrng\n");
  lsu_write_32(CLP_CSRNG_REG_CTRL, 0x666);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x901);

  VPRINTF(LOW, "  - Waiting for ES0 boot done...\n");
  poll_reg(CLP_ENTROPY_SRC_REG_DEBUG_STATUS,
           ENTROPY_SRC_REG_DEBUG_STATUS_MAIN_SM_BOOT_DONE_MASK);

  VPRINTF(LOW, "  - Waiting for ES1 boot done...\n");
  poll_reg(CLP_ENTROPY_SRC1_REG_DEBUG_STATUS,
           ENTROPY_SRC1_REG_DEBUG_STATUS_MAIN_SM_BOOT_DONE_MASK);
  return error;
}

int run_combine_seed_test() {
  int error = 0;

  VPRINTF(LOW, "\nEntropy Combiner Seed Test (combine mode)\n");

  VPRINTF(LOW, "Instantiate/Generate Command\n");
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x1003);

  VPRINTF(LOW, "  - Waiting for csrng to generate bits ...\n");
  poll_reg(CLP_CSRNG_REG_GENBITS_VLD, CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK);

  error += read_and_compare(CLP_CSRNG_REG_GENBITS, EXP_GENBITS_COMBINE_0);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, EXP_GENBITS_COMBINE_1);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, EXP_GENBITS_COMBINE_2);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, EXP_GENBITS_COMBINE_3);

  return error;
}

// Read the entropy_combiner FIPS-flag config (COMBINER_CTRL): es_fips_policy[1:0]
// selects how the ES0/ES1 FIPS flags combine, es_fips_cfg[8] is the FIPS flag
// value used in CONFIG_VALUE policy. Verify + print it (reset = 0: AND_OF_BOTH_ES,
// flag 0).
int check_combiner_fips_flag(uint32_t expected) {
  uint32_t ctrl = lsu_read_32(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL);
  VPRINTF(LOW, "  COMBINER_CTRL(FIPS)=%x (es_fips_policy=%x es_fips_flag=%x)\n",
          ctrl, ctrl & ENTROPY_COMBINER_REG_COMBINER_CTRL_ES_FIPS_POLICY_MASK,
          (ctrl & ENTROPY_COMBINER_REG_COMBINER_CTRL_ES_FIPS_CFG_MASK) ? 1 : 0);
  if (ctrl != expected) {
    VPRINTF(ERROR, "  COMBINER_CTRL FIPS flag got %x want %x\n", ctrl, expected);
    return 1;
  }
  return 0;
}

void main() {
  int error = 0;

  VPRINTF(LOW, "----------------------------------\n");
  VPRINTF(LOW, " Entropy Combiner Smoke Test \n");
  VPRINTF(LOW, "----------------------------------\n");

  end_sim_if_itrng_disabled();
  end_sim_if_dual_itrng_disabled();
  error += enable_combiner_chain();
  // Combiner FIPS flag is at its reset default (this test does not program it).
  error += check_combiner_fips_flag(0x0);
  error += run_combine_seed_test();

  if (error > 0) {
    VPRINTF(ERROR, "Error: %d\n", error);
    SEND_STDOUT_CTRL(0x1);
  } else {
    VPRINTF(LOW, "Entropy combiner combine-mode genbits match golden\n");
    SEND_STDOUT_CTRL(0xff);
  }
}
