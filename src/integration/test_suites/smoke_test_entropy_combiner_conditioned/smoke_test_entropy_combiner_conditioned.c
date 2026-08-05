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
// smoke_test_entropy_combiner_conditioned
//
// Conditioner-ENABLED dual-iTRNG combine test. Unlike smoke_test_entropy_combiner
// (which runs the entropy_src blocks in raw/bypass), this turns the per-ES
// SHA3-384 conditioners ON (FIPS mode) so the full realistic path is exercised:
//
//   physical_rng_deterministic(seed0) -> ES0 (SHA3-384 conditioner ON) --\
//                                                                          combiner
//   physical_rng_deterministic(seed1) -> ES1 (SHA3-384 conditioner ON) --/  (SHA3-384)
//                                                                            -> CSRNG
//   ES_cond_k = SHA3-384(2 x FIPS_WINDOW samples of source k)   (startup seed)
//   seed      = SHA3-384(ES0_cond || ES1_cond)                  (entropy_combiner)
//   genbits   = CTR_DRBG(instantiate=seed).generate(128)        (CSRNG)
//
// Two phases:
//   1. Power-on KAT then lock: run the combiner SHA3-384 KAT (empty message) to
//      populate KAT_DIGEST, program the FIPS policy, then set the combiner W1S
//      AHB_LOCK BEFORE any entropy flows (mirrors ROM KAT->lock). The entropy flow
//      then runs THROUGH the already-locked combiner: instantiate + generate and
//      check CSRNG genbits against the golden -- confirming the FIPS conditioned
//      datapath produces correct values while the combiner is locked.
//   2. Post-operation enforcement: verify the lock held throughout -- the KAT
//      digest produced in phase 1 is scrubbed to 0 (no confidential data
//      readable), KAT_STATUS is 0, the FIPS policy is frozen, and the lock is
//      sticky.
//
// Determinism: the RNG sources are driven by physical_rng_deterministic (a
// reproducible LFSR stream) selected with +CLP_DETERMINISTIC_RNG, and FIPS_WINDOW
// is programmed to 1024 samples. The golden genbits below were produced OFFLINE
// by tb/es_conditioner_model.py (which reuses the validated combiner + CSRNG
// model) with FIPS_WINDOW=1024 and LFSR seeds 0xDEADBEEF/0x12345678:
//
//   python3 src/entropy_combiner/tb/es_conditioner_model.py 1024
//
// Health tests: only REPCNT (RPTCNT) and ADAPTP (APTCNT) are used; their
// thresholds are widened so the deterministic stream never trips them (which
// would stall the ES). REPCNTS (symbol), BUCKET and MARKOV are not
// implemented/used and stay at their never-fail reset defaults. Threshold config
// does not change the conditioned output (SHA3 hashes the raw samples anyway).
//
// Requires the subsystem build (caliptra_top_ss_mode_tb) with +CLP_ITRNG1_EN so
// combine mode is active, and +CLP_DETERMINISTIC_RNG so the deterministic RNG is
// selected. FIPS_WINDOW here MUST match the value used to generate the golden.
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

// Golden CSRNG genbits for the conditioned startup seed (FIPS_WINDOW=1024),
// from tb/es_conditioner_model.py (LSW read first). Sim-validated: this test
// passes with these values in caliptra_top_ss_mode_tb.
#define EXP_GENBITS_CONDITIONED_0 0x1f20f163
#define EXP_GENBITS_CONDITIONED_1 0x46403f59
#define EXP_GENBITS_CONDITIONED_2 0xd3535e1f
#define EXP_GENBITS_CONDITIONED_3 0xdfddd030

// Golden digest for the power-on KAT run before locking: SHA3-384("") (empty
// message, KAT_MSG_LEN=0), LSW-first. Populating KAT_DIGEST makes the post-lock
// scrub-to-0 check below meaningful (the value is non-zero pre-lock).
static const uint32_t kat_empty_digest[12] = {
  0x5ba7630c, 0x7d4f5e84, 0x857d1001, 0x85244c2e, 0xaa501ac5, 0x61fc94aa,
  0xbb715e99, 0x2a3a98ee, 0x313871c3, 0x47db4a26, 0xe0d16bfb, 0x04f0d558
};

// ES FIPS-mode config. Same as the raw config (0x2649999) but FIPS_ENABLE=[3:0]
// MuBi4True (0x6) instead of MuBi4False (0x9): conditioner + FIPS startup path on,
// RNG_BIT_ENABLE stays MuBi4False (4-lane), THRESHOLD_SCOPE / ENTROPY_DATA_REG
// stay MuBi4False.
#define ES_CONF_FIPS          0x2649996
// ENTROPY_CONTROL: ES_ROUTE=MuBi4False (to CSRNG, not SW), ES_TYPE=MuBi4False
// (use conditioner, not bypass).
#define ES_ENTROPY_CONTROL    0x99
// HEALTH_TEST_WINDOWS: FIPS_WINDOW[15:0]=1024 (0x400) is the conditioned-mode
// window used here. BYPASS_WINDOW[31:16]=96 is the bypass/boot-mode window
// (unused in FIPS mode; kept at the required SeedLen/4=96 so the register is
// well-formed).
#define ES_HT_WINDOWS         0x00600400
#define ES_MODULE_ENABLE       0x6

// ES1's register map is ES0's base + 0x1000.
#define ES1_OFFSET (CLP_ENTROPY_SRC1_REG_BASE_ADDR - CLP_ENTROPY_SRC_REG_BASE_ADDR)

// CSRNG command encodings (see smoke_test_trng).
#define CSRNG_CTRL_ENABLE      0x666
#define CSRNG_CMD_INSTANTIATE  0x901   // instantiate from entropy source
#define CSRNG_CMD_GENERATE_128 0x1003  // generate one 128-bit block
#define CSRNG_CMD_DONE (CSRNG_REG_SW_CMD_STS_CMD_RDY_MASK | \
                        CSRNG_REG_SW_CMD_STS_CMD_ACK_MASK)

// Combiner MuBi4 AHB_LOCK codes and COMBINER_CTRL.es_fips_policy values, used for
// the post-lock enforcement / no-confidential-read checks after the combine.
#define AHB_LOCK_UNLOCKED     0x9
#define AHB_LOCK_LOCKED       0x6
#define COMB_POLICY_PRIMARY   0x1  // PRIMARY_ES0_ONLY (programmed before lock)
#define COMB_POLICY_ALT       0x2  // rejected after lock

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
  do {
    read_data = lsu_read_32(addr);
  } while (read_data != expected_data);
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

// Combine mode requires the subsystem build + CLP_ITRNG1_EN; skip otherwise.
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

// Configure one entropy_src instance for FIPS/conditioned mode and verify the
// config was accepted. es_offset is 0 for ES0 and ES1_OFFSET for ES1. Config
// registers are written before MODULE_ENABLE, which is written last to start the
// block. Returns non-zero if the read-back config is not as expected.
int configure_es_fips(uint32_t es_offset) {
  int error = 0;

  lsu_write_32(CLP_ENTROPY_SRC_REG_CONF + es_offset, ES_CONF_FIPS);
  lsu_write_32(CLP_ENTROPY_SRC_REG_ENTROPY_CONTROL + es_offset, ES_ENTROPY_CONTROL);
  lsu_write_32(CLP_ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS + es_offset, ES_HT_WINDOWS);

  // Only REPCNT (RPTCNT) and ADAPTP (APTCNT) health tests are used; widen their
  // thresholds so the deterministic stream never trips them and stalls the ES.
  // REPCNTS (symbol), BUCKET and MARKOV are not implemented/used and are left at
  // their never-fail reset defaults (HI=0xffff, LO=0x0), i.e. disabled.
  lsu_write_32(CLP_ENTROPY_SRC_REG_REPCNT_THRESHOLDS    + es_offset, 0xFFFFFFFF);
  lsu_write_32(CLP_ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS + es_offset, 0xFFFFFFFF);
  lsu_write_32(CLP_ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS + es_offset, 0x00000000);

  lsu_write_32(CLP_ENTROPY_SRC_REG_MODULE_ENABLE + es_offset, ES_MODULE_ENABLE);

  // Verify the FIPS configuration is as expected once the conditioner is enabled:
  // read back CONF (FIPS_ENABLE=MuBi4True), MODULE_ENABLE and the window, and
  // confirm no recoverable config alert fired (an invalid MuBi field, or a config
  // the block rejected, would set RECOV_ALERT_STS).
  error += read_and_compare(CLP_ENTROPY_SRC_REG_CONF + es_offset, ES_CONF_FIPS);
  error += read_and_compare(CLP_ENTROPY_SRC_REG_MODULE_ENABLE + es_offset,
                            ES_MODULE_ENABLE);
  error += read_and_compare(CLP_ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS + es_offset,
                            ES_HT_WINDOWS);
  error += read_and_compare(CLP_ENTROPY_SRC_REG_RECOV_ALERT_STS + es_offset, 0x0);
  return error;
}

// Issue a CSRNG command and wait for completion. Bails out with a log if the
// command reports a non-zero CMD_STS (status error) instead of hanging. Returns
// non-zero on error.
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

int run_conditioned_combine_test() {
  int error = 0;
  int i;
  uint32_t status;
  uint32_t gb[4];
  const uint32_t exp[4] = {EXP_GENBITS_CONDITIONED_0, EXP_GENBITS_CONDITIONED_1,
                           EXP_GENBITS_CONDITIONED_2, EXP_GENBITS_CONDITIONED_3};

  // --- Power-on KAT then lock (mirror ROM: KAT -> lock, BEFORE any entropy flows)
  // Run the combiner's SHA3-384 KAT (empty message) so KAT_DIGEST holds a real
  // non-zero digest; this makes the post-lock scrub-to-0 check meaningful. Then
  // program the FIPS policy and set the combiner W1S AHB_LOCK. The lock only
  // affects the combiner's own registers -- not ES/CSRNG or the operational
  // combine datapath -- so the entropy flow below runs THROUGH the already-locked
  // combiner (the realistic ROM sequence).
  VPRINTF(LOW, "\nRunning combiner power-on KAT (empty message)\n");
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_KAT_MSG_LEN, 0x0);
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_KAT_CTRL,
               ENTROPY_COMBINER_REG_KAT_CTRL_START_MASK);
  poll_reg(CLP_ENTROPY_COMBINER_REG_KAT_STATUS,
           ENTROPY_COMBINER_REG_KAT_STATUS_VALID_MASK);
  for (i = 0; i < 12; i++) {
    error += read_and_compare(
        CLP_ENTROPY_COMBINER_REG_KAT_DIGEST_0 + (uint32_t)(4 * i),
        kat_empty_digest[i]);
  }

  VPRINTF(LOW, "Programming policy and locking combiner AHB (pre-operation)\n");
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL, COMB_POLICY_PRIMARY);
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL, COMB_POLICY_PRIMARY);
  // Read/decode the combiner COMBINE POLICY (COMBINER_CTRL). This is the policy
  // for merging the two ES FIPS bits (here PRIMARY_ES0_ONLY), NOT the conditioner
  // enable -- that is entropy_src CONF.FIPS_ENABLE (=6), verified in
  // configure_es_fips(). es_fips_cfg is consulted only under CONFIG_VALUE policy.
  {
    uint32_t ctrl = lsu_read_32(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL);
    VPRINTF(LOW, "  COMBINER_CTRL(policy)=%x (es_fips_policy=%x es_fips_cfg=%x)\n",
            ctrl, ctrl & ENTROPY_COMBINER_REG_COMBINER_CTRL_ES_FIPS_POLICY_MASK,
            (ctrl & ENTROPY_COMBINER_REG_COMBINER_CTRL_ES_FIPS_CFG_MASK) ? 1 : 0);
  }
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_AHB_LOCK, AHB_LOCK_LOCKED);
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_AHB_LOCK, AHB_LOCK_LOCKED);

  VPRINTF(LOW, "Configuring ES0/ES1 in FIPS (conditioned) mode\n");
  error += configure_es_fips(0);
  error += configure_es_fips(ES1_OFFSET);

  VPRINTF(LOW, "Enabling CSRNG and instantiating from entropy source\n");
  lsu_write_32(CLP_CSRNG_REG_CTRL, CSRNG_CTRL_ENABLE);
  // Instantiate: pulls the conditioned startup seed SHA3-384(ES0_cond||ES1_cond)
  // through the LOCKED combiner. Waits for both ES startup seeds (no boot-done
  // poll: MAIN_SM_BOOT_DONE is a bypass-mode signal, not set in FIPS mode).
  error += csrng_cmd(CSRNG_CMD_INSTANTIATE);

  // Sanity: the combiner sampled combine_en=1 (two-ES combine topology).
  status = lsu_read_32(CLP_ENTROPY_COMBINER_REG_COMBINER_STATUS);
  if (!(status & ENTROPY_COMBINER_REG_COMBINER_STATUS_COMBINE_EN_MASK)) {
    VPRINTF(ERROR, "COMBINER_STATUS.combine_en not set: %x\n", status);
    error += 1;
  }

  VPRINTF(LOW, "Generating 128b and checking against conditioned golden\n");
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, CSRNG_CMD_GENERATE_128);
  poll_reg(CLP_CSRNG_REG_GENBITS_VLD, CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK);
  // Read + print each genbits word. The VPRINTF between reads also SPACES the AHB
  // reads: back-to-back reads of the same CSRNG register hold reg_re high for 2
  // cycles and trip csrng_reg_top's rePulse assertion ($rose(re) |=> !re).
  // Printing got vs exp also makes a pass visibly confirmed (not a false pass).
  for (i = 0; i < 4; i++) {
    gb[i] = lsu_read_32(CLP_CSRNG_REG_GENBITS);
    VPRINTF(LOW, "  genbits[%d] got=%x exp=%x\n", i, gb[i], exp[i]);
  }
  poll_reg(CLP_CSRNG_REG_SW_CMD_STS, CSRNG_CMD_DONE);

  for (i = 0; i < 4; i++) {
    if (gb[i] != exp[i]) {
      VPRINTF(ERROR, "  genbits[%d] mismatch: got %x want %x\n", i, gb[i], exp[i]);
      error += 1;
    }
  }

  // The instantiate/generate must not have raised a CSRNG error.
  error += read_and_compare(CLP_CSRNG_REG_HW_EXC_STS, 0x0);
  error += read_and_compare(CLP_CSRNG_REG_ERR_CODE, 0x0);

  // --- Post-operation: the lock held throughout; confirm enforcement -----------
  VPRINTF(LOW, "\nVerifying post-operation lock enforcement\n");

  // No confidential data readable: the KAT digest we produced above is now
  // scrubbed -- every KAT_DIGEST word and KAT_STATUS read 0.
  for (i = 0; i < 12; i++) {
    error += read_and_compare(
        CLP_ENTROPY_COMBINER_REG_KAT_DIGEST_0 + (uint32_t)(4 * i), 0x0);
  }
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_KAT_STATUS, 0x0);

  // Config frozen: a policy write to a different value is rejected (stays PRIMARY).
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL, COMB_POLICY_ALT);
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_COMBINER_CTRL, COMB_POLICY_PRIMARY);

  // Lock sticky: an unlock attempt is ignored.
  lsu_write_32(CLP_ENTROPY_COMBINER_REG_AHB_LOCK, AHB_LOCK_UNLOCKED);
  error += read_and_compare(CLP_ENTROPY_COMBINER_REG_AHB_LOCK, AHB_LOCK_LOCKED);

  return error;
}

void main() {
  int error = 0;

  VPRINTF(LOW, "-------------------------------------------------\n");
  VPRINTF(LOW, " Entropy Combiner Conditioned (FIPS) Combine Test \n");
  VPRINTF(LOW, "-------------------------------------------------\n");

  end_sim_if_itrng_disabled();
  end_sim_if_dual_itrng_disabled();

  error += run_conditioned_combine_test();

  if (error > 0) {
    VPRINTF(ERROR, "Error: %d\n", error);
    SEND_STDOUT_CTRL(0x1);
  } else {
    VPRINTF(LOW, "Conditioned combine genbits match golden; post-lock enforcement OK\n");
    SEND_STDOUT_CTRL(0xff);
  }
}
