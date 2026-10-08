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

// ENTROPY_SRC zeroize test:
//   entropy_src runs in FIPS mode (SHA3 conditioner enabled) and the seeds are
//   routed to firmware (ENTROPY_DATA register).
//   1. Read a first seed.
//   2. Zeroize while a seed is waiting in the esfinal FIFO.
//      Check that the FIFO is cleared.
//   3. Zeroize during the startup health tests.
//   4. Zeroize during the continuous health tests (SHA3 is absorbing).
//   5. Zeroize several times back-to-back.
//   After each zeroize, entropy_src restarts on its own (it stays enabled).
//   Check that a new seed is delivered, that it is not all-zero and that it
//   differs from all the previous seeds. Also check that no error or alert was
//   raised by the zeroize.

#include <stdint.h>

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "printf.h"
#include "riscv-csr.h"
#include "riscv_hw_if.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// MuBi4 encodings
#define MUBI4_TRUE  0x6
#define MUBI4_FALSE 0x9

// CONF: FIPS_ENABLE=True, FIPS_FLAG=False, RNG_FIPS=False, RNG_BIT_ENABLE=False,
// THRESHOLD_SCOPE=False, ENTROPY_DATA_REG_ENABLE=True, RNG_BIT_SEL=0
#define ES_CONF               0x0699996
// ENTROPY_CONTROL: ES_ROUTE=True (seeds to firmware), ES_TYPE=False (use the conditioner)
#define ES_ENTROPY_CONTROL    0x96
// HEALTH_TEST_WINDOWS: FIPS_WINDOW=128 samples to keep the sim short,
// BYPASS_WINDOW=384 bits
#define ES_HT_WINDOWS         0x01800080

// Main state machine states (see entropy_src_main_sm_pkg.sv)
#define ES_MAIN_SM_STARTUP_PHASE1   0x101
#define ES_MAIN_SM_CONT_HT_RUNNING  0x1a2
#define ES_MAIN_SM_ERROR            0x073

#define SEED_WORDS        12
#define NUM_SEEDS         8
#define NUM_BACK_TO_BACK  4
#define MAX_POLLS         1000000

uint32_t seeds[NUM_SEEDS][SEED_WORDS];
uint32_t num_seeds = 0;

void fail() {
  SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
  while (1);
}

void end_sim_if_itrng_disabled() {
  uint32_t hw_cfg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
  if (hw_cfg & SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK) {
    VPRINTF(LOW, "Internal TRNG is enabled\n");
  } else {
    VPRINTF(FATAL, "Internal TRNG is not enabled, skipping test\n");
    SEND_STDOUT_CTRL(0xFF);
    while (1);
  }
}

void entropy_src_zeroize() {
  lsu_write_32(CLP_ENTROPY_SRC_REG_ENTROPY_SRC_CTRL, ENTROPY_SRC_REG_ENTROPY_SRC_CTRL_ZEROIZE_MASK);
}

uint32_t esfinal_depth() {
  return lsu_read_32(CLP_ENTROPY_SRC_REG_DEBUG_STATUS) &
         ENTROPY_SRC_REG_DEBUG_STATUS_ENTROPY_FIFO_DEPTH_MASK;
}

void configure_entropy_src() {
  VPRINTF(LOW, "Configuring entropy_src (FIPS mode, seeds to firmware)\n");
  lsu_write_32(CLP_ENTROPY_SRC_REG_CONF, ES_CONF);
  lsu_write_32(CLP_ENTROPY_SRC_REG_ENTROPY_CONTROL, ES_ENTROPY_CONTROL);
  lsu_write_32(CLP_ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS, ES_HT_WINDOWS);
  // Widen the thresholds so that the health tests never fail on the TB noise source.
  lsu_write_32(CLP_ENTROPY_SRC_REG_REPCNT_THRESHOLD,    0xFFFF);
  lsu_write_32(CLP_ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLD, 0xFFFF);
  lsu_write_32(CLP_ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLD, 0x0000);
  lsu_write_32(CLP_ENTROPY_SRC_REG_MODULE_ENABLE, MUBI4_TRUE);
}

void wait_main_sm_state(uint32_t state, const char *ctx) {
  for (uint32_t i = 0; i < MAX_POLLS; i++) {
    if (lsu_read_32(CLP_ENTROPY_SRC_REG_MAIN_SM_STATE) == state) return;
  }
  VPRINTF(ERROR, "%s: main SM never reached state 0x%x\n", ctx, state);
  fail();
}

void wait_seed(const char *ctx) {
  for (uint32_t i = 0; i < MAX_POLLS; i++) {
    if (esfinal_depth() != 0) return;
  }
  VPRINTF(ERROR, "%s: no seed delivered (MAIN_SM_STATE = 0x%x)\n", ctx,
          lsu_read_32(CLP_ENTROPY_SRC_REG_MAIN_SM_STATE));
  fail();
}

/**
 * Wait for a seed, read it through ENTROPY_DATA and check that it is not
 * all-zero and differs from all the previous seeds.
 */
void read_and_check_seed(const char *ctx) {
  uint32_t *seed = seeds[num_seeds];
  uint32_t or_all = 0;

  wait_seed(ctx);
  for (int i = 0; i < SEED_WORDS; i++) {
    seed[i] = lsu_read_32(CLP_ENTROPY_SRC_REG_ENTROPY_DATA);
    or_all |= seed[i];
  }
  VPRINTF(LOW, "%s: seed[0] = 0x%x\n", ctx, seed[0]);

  if (or_all == 0) {
    VPRINTF(ERROR, "%s: all-zero seed\n", ctx);
    fail();
  }
  for (uint32_t s = 0; s < num_seeds; s++) {
    int equal = 1;
    for (int i = 0; i < SEED_WORDS; i++) {
      if (seeds[s][i] != seed[i]) equal = 0;
    }
    if (equal) {
      VPRINTF(ERROR, "%s: seed is equal to seed %d\n", ctx, s);
      fail();
    }
  }
  num_seeds++;
}

/**
 * Check the state right after a zeroize:
 *  - esfinal FIFO empty
 *  - main SM not in the Error state
 *  - no error or recoverable alert raised
 */
void check_zeroized(const char *ctx) {
  uint32_t data;

  if (esfinal_depth() != 0) {
    VPRINTF(ERROR, "%s: esfinal FIFO not empty after zeroize\n", ctx);
    fail();
  }
  if (lsu_read_32(CLP_ENTROPY_SRC_REG_MAIN_SM_STATE) == ES_MAIN_SM_ERROR) {
    VPRINTF(ERROR, "%s: main SM in Error state after zeroize\n", ctx);
    fail();
  }
  if ((data = lsu_read_32(CLP_ENTROPY_SRC_REG_ERR_CODE)) != 0) {
    VPRINTF(ERROR, "%s: ERR_CODE = 0x%x after zeroize\n", ctx, data);
    fail();
  }
  if ((data = lsu_read_32(CLP_ENTROPY_SRC_REG_RECOV_ALERT_STS)) != 0) {
    VPRINTF(ERROR, "%s: RECOV_ALERT_STS = 0x%x after zeroize\n", ctx, data);
    fail();
  }
}

void main() {
  VPRINTF(LOW, "----------------------------------\n");
  VPRINTF(LOW, " ENTROPY_SRC zeroize test!\n"        );
  VPRINTF(LOW, "----------------------------------\n");

  end_sim_if_itrng_disabled();
  configure_entropy_src();

  // ---------------------------------------------------------------------
  // 1. First seed
  // ---------------------------------------------------------------------
  VPRINTF(LOW, "Step 1: first seed\n");
  read_and_check_seed("first seed");

  // ---------------------------------------------------------------------
  // 2. Zeroize while a seed is waiting in the esfinal FIFO
  // ---------------------------------------------------------------------
  VPRINTF(LOW, "Step 2: zeroize with a seed in the esfinal FIFO\n");
  wait_seed("seed in esfinal");
  entropy_src_zeroize();
  check_zeroized("zeroize with seed in esfinal");
  read_and_check_seed("seed after zeroize with seed in esfinal");

  // ---------------------------------------------------------------------
  // 3. Zeroize during the startup health tests
  // ---------------------------------------------------------------------
  VPRINTF(LOW, "Step 3: zeroize during the startup health tests\n");
  entropy_src_zeroize();
  wait_main_sm_state(ES_MAIN_SM_STARTUP_PHASE1, "startup");
  entropy_src_zeroize();
  check_zeroized("zeroize during startup");
  read_and_check_seed("seed after zeroize during startup");

  // ---------------------------------------------------------------------
  // 4. Zeroize during the continuous health tests (SHA3 absorbing)
  // ---------------------------------------------------------------------
  VPRINTF(LOW, "Step 4: zeroize during the continuous health tests\n");
  wait_main_sm_state(ES_MAIN_SM_CONT_HT_RUNNING, "continuous");
  entropy_src_zeroize();
  check_zeroized("zeroize during continuous");
  read_and_check_seed("seed after zeroize during continuous");

  // ---------------------------------------------------------------------
  // 5. Back-to-back zeroizes
  // ---------------------------------------------------------------------
  VPRINTF(LOW, "Step 5: back-to-back zeroizes\n");
  for (int i = 0; i < NUM_BACK_TO_BACK; i++) {
    entropy_src_zeroize();
  }
  check_zeroized("back-to-back zeroizes");
  read_and_check_seed("seed after back-to-back zeroizes");

  VPRINTF(LOW, "ENTROPY_SRC zeroize test passed\n");

  // Write 0xff to STDOUT for TB to terminate test.
  SEND_STDOUT_CTRL(0xff);
  while (1);
}
