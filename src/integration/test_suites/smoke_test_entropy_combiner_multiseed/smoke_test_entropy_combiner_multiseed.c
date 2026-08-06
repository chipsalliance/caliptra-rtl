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
// smoke_test_entropy_combiner_multiseed
//
// Back-to-back multi-seed dual-iTRNG combine test (Plan E). Proves the combiner
// produces MULTIPLE consecutive combined seeds -- exercising the FSM's
// return-to-idle / re-request path (combiner_st_comb_ack -> idle -> req_entropy)
// and the ES esfinal FIFO refill / steady-state (ContHTStart) seed production --
// not just the first (startup) seed that the other tests cover.
//
// Both entropy_src blocks run their SHA3-384 conditioners (FIPS mode). CSRNG
// pulls NUM_SEEDS consecutive combined seeds via uninstantiate -> re-instantiate,
// generating 128 bits from each and checking against per-seed goldens:
//
//   seed 0  = SHA3-384(ES0_cond_0 || ES1_cond_0)   ES_cond_0 = startup (2 x FIPS_WINDOW samples)
//   seed k>=1 = SHA3-384(ES0_cond_k || ES1_cond_k) ES_cond_k = steady-state (1 x FIPS_WINDOW samples)
//   genbits_k = CTR_DRBG(instantiate=seed_k).generate(128)
//
// The deterministic PRNG (+CLP_DETERMINISTIC_RNG) streams a single contiguous
// sequence, so seed k maps to a fixed sample slice. The goldens below were
// produced OFFLINE (FIPS_WINDOW=1024, seeds 0xDEADBEEF/0x12345678):
//
//   python3 src/entropy_combiner/tb/es_conditioner_model.py 1024 4
//
// seed 0's golden equals smoke_test_entropy_combiner_conditioned's (sim-validated).
//
// Requires the subsystem build (caliptra_top_ss_mode_tb) with +CLP_ITRNG1_EN and
// +CLP_DETERMINISTIC_RNG. FIPS_WINDOW here MUST match the golden generation value.
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

#define NUM_SEEDS 4

// Golden CSRNG genbits for NUM_SEEDS consecutive combined seeds (FIPS_WINDOW=1024),
// from tb/es_conditioner_model.py (LSW read first). seed 0 is sim-validated (it is
// smoke_test_entropy_combiner_conditioned's golden).
static const uint32_t exp_genbits[NUM_SEEDS][4] = {
  { 0x1f20f163, 0x46403f59, 0xd3535e1f, 0xdfddd030 },  // seed 0 (startup)
  { 0x22ed9ea6, 0x95777a90, 0xde6041ed, 0xf599d094 },  // seed 1 (steady-state)
  { 0x667f0b9f, 0x87ae6bf9, 0x5bf713bc, 0x4cf4376b },  // seed 2 (steady-state)
  { 0x727cb92f, 0xd6aa5580, 0x2196fb05, 0x075462bb },  // seed 3 (steady-state)
};

// ES FIPS-mode config (see smoke_test_entropy_combiner_conditioned).
#define ES_CONF_FIPS          0x2649996
#define ES_ENTROPY_CONTROL    0x99
#define ES_HT_WINDOWS         0x00600400  // FIPS_WINDOW=1024, BYPASS_WINDOW=96
#define ES_MODULE_ENABLE       0x6
#define ES1_OFFSET (CLP_ENTROPY_SRC1_REG_BASE_ADDR - CLP_ENTROPY_SRC_REG_BASE_ADDR)

// CSRNG command encodings (see smoke_test_trng).
#define CSRNG_CTRL_ENABLE      0x666
#define CSRNG_CMD_INSTANTIATE  0x901
#define CSRNG_CMD_UNINSTANTIATE 0x905
#define CSRNG_CMD_GENERATE_128 0x1003
#define CSRNG_CMD_DONE (CSRNG_REG_SW_CMD_STS_CMD_RDY_MASK | \
                        CSRNG_REG_SW_CMD_STS_CMD_ACK_MASK)

void poll_reg(uint32_t addr, uint32_t expected_data) {
  uint32_t read_data;
  do {
    read_data = lsu_read_32(addr);
  } while (read_data != expected_data);
}

int read_and_compare(uint32_t addr, uint32_t exp_data) {
  uint32_t act_data = lsu_read_32(addr);
  if (act_data != exp_data) {
    VPRINTF(ERROR, "Got:%x Want:%x @%x\n", act_data, exp_data, addr);
    return 1;
  }
  return 0;
}

void end_sim_if_itrng_disabled() {
  uint32_t hw_cfg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
  if (hw_cfg & SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK) {
    VPRINTF(LOW, "Internal TRNG is enabled\n");
  } else {
    VPRINTF(FATAL, "Internal TRNG is not enabled, skipping test\n");
    SEND_STDOUT_CTRL(0xFF);
    while (1)
      ;
  }
}

void end_sim_if_dual_itrng_disabled() {
  uint32_t hw_cfg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
  if (hw_cfg & SOC_IFC_REG_CPTRA_HW_CONFIG_DUAL_ITRNG_EN_MASK) {
    VPRINTF(LOW, "Dual iTRNG (combine mode) is enabled\n");
  } else {
    VPRINTF(FATAL, "Dual iTRNG not enabled (needs ss_mode build + CLP_ITRNG1_EN); skipping\n");
    SEND_STDOUT_CTRL(0xFF);
    while (1)
      ;
  }
}

// Configure one entropy_src instance for FIPS/conditioned mode (only REPCNT and
// ADAPTP health tests are used; the rest stay at their never-fail resets), then
// verify the config read-back is as expected. Returns error count.
int configure_es_fips(uint32_t es_offset) {
  int error = 0;
  lsu_write_32(CLP_ENTROPY_SRC_REG_CONF + es_offset, ES_CONF_FIPS);
  lsu_write_32(CLP_ENTROPY_SRC_REG_ENTROPY_CONTROL + es_offset, ES_ENTROPY_CONTROL);
  lsu_write_32(CLP_ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS + es_offset, ES_HT_WINDOWS);
  lsu_write_32(CLP_ENTROPY_SRC_REG_REPCNT_THRESHOLDS    + es_offset, 0xFFFFFFFF);
  lsu_write_32(CLP_ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS + es_offset, 0xFFFFFFFF);
  lsu_write_32(CLP_ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS + es_offset, 0x00000000);
  lsu_write_32(CLP_ENTROPY_SRC_REG_MODULE_ENABLE + es_offset, ES_MODULE_ENABLE);

  // Verify the FIPS config is as expected once the conditioner is enabled.
  error += read_and_compare(CLP_ENTROPY_SRC_REG_CONF + es_offset, ES_CONF_FIPS);
  error += read_and_compare(CLP_ENTROPY_SRC_REG_MODULE_ENABLE + es_offset,
                            ES_MODULE_ENABLE);
  error += read_and_compare(CLP_ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS + es_offset,
                            ES_HT_WINDOWS);
  error += read_and_compare(CLP_ENTROPY_SRC_REG_RECOV_ALERT_STS + es_offset, 0x0);
  return error;
}

// Issue a CSRNG command and wait for completion; logs and returns non-zero on a
// command status error instead of hanging.
int csrng_cmd(uint32_t cmd) {
  uint32_t sts;
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, cmd);
  do {
    sts = lsu_read_32(CLP_CSRNG_REG_SW_CMD_STS);
    if (sts & CSRNG_REG_SW_CMD_STS_CMD_STS_MASK) {
      VPRINTF(ERROR, "CSRNG cmd %x status error, SW_CMD_STS=%x\n", cmd, sts);
      return 1;
    }
  } while ((sts & CSRNG_CMD_DONE) != CSRNG_CMD_DONE);
  return 0;
}

// Pull the k-th combined seed and generate/check 128 bits against exp_genbits[k].
int run_seed(int k) {
  int error = 0;
  int i;
  uint32_t gb[4];

  // Pull a fresh combined seed: instantiate for seed 0, else uninstantiate then
  // re-instantiate so the combiner re-requests the next ES seed pair.
  if (k > 0) {
    error += csrng_cmd(CSRNG_CMD_UNINSTANTIATE);
  }
  error += csrng_cmd(CSRNG_CMD_INSTANTIATE);

  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, CSRNG_CMD_GENERATE_128);
  poll_reg(CLP_CSRNG_REG_GENBITS_VLD, CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK);
  // Read + print each word. The VPRINTF between reads spaces the AHB reads so
  // reg_re stays a single-cycle pulse (back-to-back reads of the same CSRNG
  // register trip csrng_reg_top's rePulse assertion).
  for (i = 0; i < 4; i++) {
    gb[i] = lsu_read_32(CLP_CSRNG_REG_GENBITS);
    VPRINTF(LOW, "  seed %d genbits[%d] got=%x exp=%x\n", k, i, gb[i],
            exp_genbits[k][i]);
  }
  poll_reg(CLP_CSRNG_REG_SW_CMD_STS, CSRNG_CMD_DONE);

  for (i = 0; i < 4; i++) {
    if (gb[i] != exp_genbits[k][i]) {
      VPRINTF(ERROR, "  seed %d word %d mismatch: got %x want %x\n", k, i, gb[i],
              exp_genbits[k][i]);
      error += 1;
    }
  }
  return error;
}

int run_multiseed_test() {
  int error = 0;
  int k;
  uint32_t status;

  VPRINTF(LOW, "\nConfiguring ES0/ES1 in FIPS (conditioned) mode\n");
  error += configure_es_fips(0);
  error += configure_es_fips(ES1_OFFSET);

  lsu_write_32(CLP_CSRNG_REG_CTRL, CSRNG_CTRL_ENABLE);

  // Sanity: the combiner sampled combine_en=1 (two-ES combine topology).
  status = lsu_read_32(CLP_ENTROPY_COMBINER_REG_COMBINER_STATUS);
  if (!(status & ENTROPY_COMBINER_REG_COMBINER_STATUS_COMBINE_EN_MASK)) {
    VPRINTF(ERROR, "COMBINER_STATUS.combine_en not set: %x\n", status);
    error += 1;
  }

  // Read the combiner COMBINE POLICY (COMBINER_CTRL). This is NOT the conditioner
  // enable -- that is entropy_src CONF.FIPS_ENABLE (=MuBi4True 0x6), already
  // verified in configure_es_fips(). COMBINER_CTRL only selects HOW the two ES
  // FIPS bits merge: reset default 0x0 = AND_OF_BOTH_ES, so the combined FIPS flag
  // delivered to CSRNG = es0_fips & es1_fips = 1 at runtime (both conditioners on).
  // es_fips_cfg is consulted only under CONFIG_VALUE policy, so it stays 0 here.
  {
    uint32_t ctrl = lsu_read_32(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL);
    VPRINTF(LOW, "  COMBINER_CTRL(policy)=%x (es_fips_policy=%x es_fips_cfg=%x)\n",
            ctrl, ctrl & ENTROPY_COMBINER_REG_COMBINER_CTRL_ES_FIPS_POLICY_MASK,
            (ctrl & ENTROPY_COMBINER_REG_COMBINER_CTRL_ES_FIPS_CFG_MASK) ? 1 : 0);
    error += (ctrl == 0x0) ? 0 : 1;  // AND_OF_BOTH_ES (reset default)
  }

  VPRINTF(LOW, "Pulling %d consecutive combined seeds\n", NUM_SEEDS);
  for (k = 0; k < NUM_SEEDS; k++) {
    error += run_seed(k);
  }

  // No CSRNG hardware exception / error across the run.
  error += read_and_compare(CLP_CSRNG_REG_HW_EXC_STS, 0x0);
  error += read_and_compare(CLP_CSRNG_REG_ERR_CODE, 0x0);

  return error;
}

void main() {
  int error = 0;

  VPRINTF(LOW, "-----------------------------------------------\n");
  VPRINTF(LOW, " Entropy Combiner Back-to-Back Multi-Seed Test \n");
  VPRINTF(LOW, "-----------------------------------------------\n");

  end_sim_if_itrng_disabled();
  end_sim_if_dual_itrng_disabled();

  error += run_multiseed_test();

  if (error > 0) {
    VPRINTF(ERROR, "Error: %d\n", error);
    SEND_STDOUT_CTRL(0x1);
  } else {
    VPRINTF(LOW, "All %d consecutive combined seeds match golden\n", NUM_SEEDS);
    SEND_STDOUT_CTRL(0xff);
  }
}
