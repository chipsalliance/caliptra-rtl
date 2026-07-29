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
// smoke_test_entropy_combiner_lock_op
//
// Operational-after-lock test for the dual-iTRNG entropy_combiner. Proves two
// properties that neither the combine test nor the KAT test cover:
//
//   1. LIVENESS: with the combiner's W1S AHB_LOCK set, the operational combine
//      datapath still works -- CSRNG pulls a SHA3-384(ES0||ES1) seed through the
//      LOCKED combiner. (In RTL the operational buffers es0_bits_q/es1_bits_q/
//      digest_q are separate from the KAT buffers and are NOT wiped by the lock;
//      only the KAT registers are scrubbed and the FSM combine path is not
//      ahb_locked-gated.)
//   2. PERSISTENCE: the lock enforcement holds across the live combine --
//      KAT_DIGEST/KAT_STATUS stay scrubbed to 0, COMBINER_CTRL FIPS policy stays
//      frozen, and AHB_LOCK stays sticky (checked before AND after the combine).
//
// Bypass-mode ES limit: with the entropy_src conditioners off (raw CONF), the ES
// main FSM emits exactly ONE boot seed and then parks (BootPhaseDone), so only a
// single combine is possible per reset -- a second instantiate-from-ES would
// deadlock waiting for a seed that never comes. This test therefore does its one
// and only combine AFTER the lock, which both stays within the one-seed budget
// AND proves the datapath operates while locked. The seed is deterministic
// (boot seed = IS0/IS1), so it is checked against the exact EXP_GENBITS_COMBINE
// golden. (Repeated/steady-state combine after lock would need FIPS/continuous
// mode and is out of scope here.)
//
// The lock is W1S and clears only on reset. Run this last / in its own sim.
// Requires the subsystem build (caliptra_top_ss_mode_tb) with +CLP_ITRNG1_EN so
// combine mode is active.
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

// Deterministic pre-lock combine genbits: seed = SHA3-384(IS0 || IS1). Golden
// value from EXP_GENBITS_COMBINE in
// src/entropy_combiner/tb/entropy_combiner_es_csrng_tb.sv (LSW read first).
#define EXP_GENBITS_COMBINE_0 0xae5f5d34
#define EXP_GENBITS_COMBINE_1 0x43f0422c
#define EXP_GENBITS_COMBINE_2 0x0057f623
#define EXP_GENBITS_COMBINE_3 0x08c811aa

// Raw entropy_src config: es_bits == streamed InitialSeed (identity packing).
#define ES_CONF_RAW           0x2649999
#define ES_MODULE_ENABLE       0x6
// ES1's register map is ES0's base + 0x1000.
#define ES1_OFFSET (CLP_ENTROPY_SRC1_REG_BASE_ADDR - CLP_ENTROPY_SRC_REG_BASE_ADDR)

// CSRNG command encodings (see smoke_test_trng).
#define CSRNG_CTRL_ENABLE      0x666
#define CSRNG_CMD_INSTANTIATE  0x901   // instantiate from entropy source
#define CSRNG_CMD_UNINSTANTIATE 0x905
#define CSRNG_CMD_GENERATE_128 0x1003  // generate one 128-bit block
// SW_CMD_STS reads this (RDY|ACK, status field 0) when a command completes ok.
#define CSRNG_CMD_DONE (CSRNG_REG_SW_CMD_STS_CMD_RDY_MASK | \
                        CSRNG_REG_SW_CMD_STS_CMD_ACK_MASK)

// MuBi4 AHB_LOCK codes and FIPS policy values.
#define AHB_LOCK_UNLOCKED     0x9
#define AHB_LOCK_LOCKED       0x6
#define ES_FIPS_POLICY_ES0    0x1  // PRIMARY_ES0_ONLY (programmed before lock)
#define ES_FIPS_POLICY_ALT    0x2  // CONFIG_VALUE     (rejected after lock)

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

// poll a register until all bits in mask are set. Use for multi-field status
// registers (e.g. ENTROPY_SRC DEBUG_STATUS) where an exact-match poll would spin
// forever once other fields (like ENTROPY_FIFO_DEPTH) are non-zero.
void poll_reg_mask(uint32_t addr, uint32_t mask) {
  uint32_t read_data;

  VPRINTF(LOW, "  - Polling addr=%x until mask %x is set...\n", addr, mask);
  do {
    read_data = lsu_read_32(addr);
  } while ((read_data & mask) != mask);
}

void end_sim_if_itrng_disabled() {
  uint32_t hw_cfg;
  hw_cfg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
  if (hw_cfg & SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK) {
    VPRINTF(LOW, "Internal TRNG is enabled\n");
  } else {
    VPRINTF(FATAL, "Internal TRNG is not enabled, skipping test\n");
    SEND_STDOUT_CTRL(0xFF);
    while (1)
      ;
  }
}

// Combine mode requires the subsystem build (CALIPTRA_MODE_SUBSYSTEM +
// CALIPTRA_INTERNAL_TRNG) and +CLP_ITRNG1_EN; skip gracefully otherwise.
void end_sim_if_dual_itrng_disabled() {
  uint32_t hw_cfg;
  hw_cfg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
  if (hw_cfg & SOC_IFC_REG_CPTRA_HW_CONFIG_DUAL_ITRNG_EN_MASK) {
    VPRINTF(LOW, "Dual iTRNG (combine mode) is enabled\n");
  } else {
    VPRINTF(FATAL, "Dual iTRNG not enabled (needs ss_mode build + CLP_ITRNG1_EN); skipping\n");
    SEND_STDOUT_CTRL(0xFF);
    while (1)
      ;
  }
}

// Enable one entropy_src block with the raw config, then verify the config
// read-back is as expected. es_offset is 0 for ES0, ES1_OFFSET for ES1.
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

// Wait for the outstanding CSRNG command to complete. Polls SW_CMD_STS for
// RDY|ACK, but bails out with a log if the command reports a non-zero CMD_STS
// (command status error) so an errored command surfaces instead of hanging the
// poll forever. Returns non-zero on a command status error.
int csrng_wait_done(uint32_t cmd) {
  uint32_t sts;
  do {
    sts = lsu_read_32(CLP_CSRNG_REG_SW_CMD_STS);
    if (sts & CSRNG_REG_SW_CMD_STS_CMD_STS_MASK) {
      VPRINTF(ERROR, "CSRNG cmd %x status error, SW_CMD_STS=%x\n", cmd, sts);
      return 1;
    }
  } while ((sts & CSRNG_CMD_DONE) != CSRNG_CMD_DONE);
  return 0;
}

// Issue a CSRNG command and wait for completion. Returns non-zero on a command
// status error. Use for non-generate commands (instantiate/uninstantiate).
int csrng_cmd(uint32_t cmd) {
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, cmd);
  return csrng_wait_done(cmd);
}

// Generate one 128-bit block and capture the 4 words (LSW first). Returns
// non-zero on a CSRNG command status error.
int csrng_generate_128(uint32_t gb[4]) {
  int i;
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, CSRNG_CMD_GENERATE_128);
  poll_reg(CLP_CSRNG_REG_GENBITS_VLD, CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK);
  // VPRINTF between reads spaces the AHB reads so reg_re stays a single-cycle
  // pulse; back-to-back reads of the same CSRNG register trip csrng_reg_top's
  // rePulse assertion ($rose(re) |=> !re).
  for (i = 0; i < 4; i++) {
    gb[i] = lsu_read_32(CLP_CSRNG_REG_GENBITS);
    VPRINTF(LOW, "  genbits[%d]=%x\n", i, gb[i]);
  }
  return csrng_wait_done(CSRNG_CMD_GENERATE_128);
}

int enable_combiner_chain() {
  int error = 0;
  // Both entropy_src blocks feed the combiner in combine mode.
  VPRINTF(LOW, "Enabling entropy_src ES0/ES1 and CSRNG\n");
  error += enable_entropy_src(0);
  error += enable_entropy_src(ES1_OFFSET);

  lsu_write_32(CLP_CSRNG_REG_CTRL, CSRNG_CTRL_ENABLE);

  // Masked poll: DEBUG_STATUS also carries ENTROPY_FIFO_DEPTH (bits [1:0]),
  // which is non-zero here because the boot seed is buffered but not yet pulled
  // (CSRNG is instantiated after the lock). An exact-match poll for
  // MAIN_SM_BOOT_DONE would never match and hang.
  VPRINTF(LOW, "  - Waiting for ES0/ES1 boot done...\n");
  poll_reg_mask(CLP_ENTROPY_SRC_REG_DEBUG_STATUS,
                ENTROPY_SRC_REG_DEBUG_STATUS_MAIN_SM_BOOT_DONE_MASK);
  poll_reg_mask(CLP_ENTROPY_SRC1_REG_DEBUG_STATUS,
                ENTROPY_SRC1_REG_DEBUG_STATUS_MAIN_SM_BOOT_DONE_MASK);

  // Note: CSRNG is deliberately NOT instantiated here. In bypass mode each ES
  // produces exactly one boot seed (now buffered in its esfinal FIFO); that
  // single combine is pulled AFTER the lock, to prove the combine datapath
  // operates while the combiner is AHB-locked.
  return error;
}

// Verify every post-lock enforcement point still holds. Called immediately after
// locking and again after each live combine to prove persistence.
int check_lock_enforcement() {
  int error = 0;
  int i;

  // KAT state stays scrubbed.
  for (i = 0; i < 12; i++) {
    error += read_and_compare(
        CLP_ENTROPY_COMBINER_REG_KAT_DIGEST_0 + (uint32_t)(4 * i), 0x0);
  }
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_KAT_STATUS, 0x0);

  // FIPS policy stays frozen: a write to a different value is rejected.
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL, ES_FIPS_POLICY_ALT);
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL,
                            ES_FIPS_POLICY_ES0);

  // Lock stays sticky: an unlock attempt is ignored.
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_AHB_LOCK, AHB_LOCK_UNLOCKED);
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_AHB_LOCK, AHB_LOCK_LOCKED);

  return error;
}

// Pull the single bypass-mode boot seed through the LOCKED combiner and check
// the exact golden. This is the one and only combine (bypass ES emits one seed),
// done post-lock to prove the datapath operates while AHB-locked.
int run_post_lock_combine() {
  int error = 0;
  uint32_t gb[4];

  // Instantiate-from-ES: pulls SHA3-384(IS0||IS1) through the locked combiner.
  error += csrng_cmd(CSRNG_CMD_INSTANTIATE);

  // The instantiate must not have raised a CSRNG hardware exception / error.
  error += read_and_compare(CLP_CSRNG_REG_HW_EXC_STS, 0x0);
  error += read_and_compare(CLP_CSRNG_REG_ERR_CODE, 0x0);

  error += csrng_generate_128(gb);

  // The boot seed is deterministic (IS0/IS1), so the genbits are the exact
  // combine golden even though the combiner is locked.
  if (gb[0] != EXP_GENBITS_COMBINE_0 || gb[1] != EXP_GENBITS_COMBINE_1 ||
      gb[2] != EXP_GENBITS_COMBINE_2 || gb[3] != EXP_GENBITS_COMBINE_3) {
    VPRINTF(ERROR, "Post-lock combine genbits mismatch: %x %x %x %x\n", gb[0],
            gb[1], gb[2], gb[3]);
    error += 1;
  } else {
    VPRINTF(LOW, "  - Post-lock combine genbits match golden: %x %x %x %x\n",
            gb[0], gb[1], gb[2], gb[3]);
  }

  return error;
}

void main() {
  int error = 0;
  uint32_t status;
  uint32_t ctrl;

  VPRINTF(LOW, "--------------------------------------------\n");
  VPRINTF(LOW, " Entropy Combiner Operational-After-Lock Test \n");
  VPRINTF(LOW, "--------------------------------------------\n");

  end_sim_if_itrng_disabled();
  end_sim_if_dual_itrng_disabled();
  error += enable_combiner_chain();

  // Sanity: the combiner sampled combine_en=1 (topology is two-ES combine).
  status = lsu_read_32(CLP_ENTROPY_COMBINER_REG_COMBINER_STATUS);
  if (!(status & ENTROPY_COMBINER_REG_COMBINER_STATUS_COMBINE_EN_MASK)) {
    VPRINTF(ERROR, "COMBINER_STATUS.combine_en not set: %x\n", status);
    error += 1;
  }

  // Read the combiner FIPS-flag config (COMBINER_CTRL) at its reset default.
  ctrl = lsu_read_32(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL);
  VPRINTF(LOW, "  COMBINER_CTRL(FIPS)=%x (es_fips_policy=%x es_fips_flag=%x)\n",
          ctrl, ctrl & ENTROPY_COMBINER_REG_COMBINER_CTRL_ES_FIPS_POLICY_MASK,
          (ctrl & ENTROPY_COMBINER_REG_COMBINER_CTRL_ES_FIPS_CFG_MASK) ? 1 : 0);
  error += (ctrl == 0x0) ? 0 : 1;

  // Program a FIPS policy while unlocked (must take).
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL, ES_FIPS_POLICY_ES0);
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL,
                            ES_FIPS_POLICY_ES0);

  // Lock (W1S MuBi4True).
  VPRINTF(LOW, "\nSetting AHB_LOCK\n");
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_AHB_LOCK, AHB_LOCK_LOCKED);
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_AHB_LOCK, AHB_LOCK_LOCKED);

  // Enforcement check before the live combine.
  error += check_lock_enforcement();

  // The single bypass-mode boot seed combined through the LOCKED combiner.
  VPRINTF(LOW, "\nPost-lock combine\n");
  error += run_post_lock_combine();

  // Enforcement check after the live combine (proves it did not disturb the lock).
  error += check_lock_enforcement();

  if (error > 0) {
    VPRINTF(ERROR, "Error: %d\n", error);
    SEND_STDOUT_CTRL(0x1);
  } else {
    VPRINTF(LOW, "Combine operates while locked and lock enforcement persists\n");
    SEND_STDOUT_CTRL(0xff);
  }
}
