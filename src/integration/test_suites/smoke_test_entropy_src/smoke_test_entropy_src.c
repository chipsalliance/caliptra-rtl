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

// entropy_src smoke test.
//
// entropy_src (ES0) is fed by the deterministic RNG of caliptra_top_tb
// (+CLP_DETERMINISTIC_RNG). The test runs the following configurations, each
// starting from a disabled entropy_src (the deterministic RNG then restarts from
// its LFSR seed):
//   1. boot-time / bypass mode, 4-bit symbols (multi lane)
//   2. boot-time / bypass mode, single lane
//   3. FIPS mode, 4-bit symbols (multi lane)
//   4. FIPS mode, single lane
// The seeds are routed to firmware (ENTROPY_DATA) and compared against the
// reference model src/entropy_src/tb/entropy_src_model.py, which also generated
// the health test thresholds in es_vectors.h. The thresholds are configured as
// described in the integration specification: in single-lane mode ADAPTP and
// REPCNT, in 4-bit symbol mode ADAPTPS and REPCNTS, the other tests are left at
// their reset values. After each configuration, the test checks that no error,
// alert or health test failure has been recorded.
//
// When entropy_src is disabled in FIPS mode, the conditioner is already
// absorbing the next window and this partial message is left in the SHA3 sponge.
// The startup seed of the following FIPS configuration therefore also contains
// this leftover data, which depends on the firmware timing. This startup seed is
// skipped and the following seeds are checked.

#include <stdint.h>

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "es_vectors.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define MUBI4_TRUE  0x6
#define MUBI4_FALSE 0x9

#define ES_BYPASS_WINDOW 384
#define ES_MAX_POLLS     1000000

// Main state machine error states (see entropy_src_main_sm_pkg.sv)
#define ES_MAIN_SM_ALERT_HANG 0x1fb
#define ES_MAIN_SM_ERROR      0x073

static uint32_t mubi4(uint32_t b) {
  return b ? MUBI4_TRUE : MUBI4_FALSE;
}

void fail_if_itrng_disabled(void) {
  uint32_t hw_cfg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
  if (!(hw_cfg & SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK)) {
    VPRINTF(ERROR, "Internal TRNG is not enabled, test cannot run\n");
    SEND_STDOUT_CTRL(0x1);
    while (1);
  }
}

// Disable entropy_src and wait until it is fully disabled (REGWEN set), so that
// the noise source is disabled and the deterministic RNG restarts.
int es_disable(void) {
  lsu_write_32(CLP_ENTROPY_SRC_REG_MODULE_ENABLE, MUBI4_FALSE);
  for (uint32_t i = 0; i < ES_MAX_POLLS; i++) {
    if (lsu_read_32(CLP_ENTROPY_SRC_REG_REGWEN) & ENTROPY_SRC_REG_REGWEN_REGWEN_MASK) {
      return 0;
    }
  }
  VPRINTF(ERROR, "entropy_src not disabled\n");
  return 1;
}

void es_configure(const es_test_cfg_t *cfg) {
  uint32_t conf;

  conf = (mubi4(cfg->fips_mode)   << ENTROPY_SRC_REG_CONF_FIPS_ENABLE_LOW) |
         (MUBI4_FALSE             << ENTROPY_SRC_REG_CONF_FIPS_FLAG_LOW) |
         (MUBI4_FALSE             << ENTROPY_SRC_REG_CONF_RNG_FIPS_LOW) |
         (mubi4(cfg->single_lane) << ENTROPY_SRC_REG_CONF_RNG_BIT_ENABLE_LOW) |
         (MUBI4_FALSE             << ENTROPY_SRC_REG_CONF_THRESHOLD_SCOPE_LOW) |
         (MUBI4_TRUE              << ENTROPY_SRC_REG_CONF_ENTROPY_DATA_REG_ENABLE_LOW) |
         (cfg->lane               << ENTROPY_SRC_REG_CONF_RNG_BIT_SEL_LOW);
  lsu_write_32(CLP_ENTROPY_SRC_REG_CONF, conf);

  // Seeds routed to firmware, conditioned in FIPS mode
  lsu_write_32(CLP_ENTROPY_SRC_REG_ENTROPY_CONTROL,
               (MUBI4_TRUE  << ENTROPY_SRC_REG_ENTROPY_CONTROL_ES_ROUTE_LOW) |
               (MUBI4_FALSE << ENTROPY_SRC_REG_ENTROPY_CONTROL_ES_TYPE_LOW));

  lsu_write_32(CLP_ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS,
               (cfg->fips_window  << ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS_FIPS_WINDOW_LOW) |
               (ES_BYPASS_WINDOW << ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS_BYPASS_WINDOW_LOW));

  lsu_write_32(CLP_ENTROPY_SRC_REG_REPCNT_THRESHOLD,    cfg->repcnt_thresh);
  lsu_write_32(CLP_ENTROPY_SRC_REG_REPCNTS_THRESHOLD,   cfg->repcnts_thresh);
  lsu_write_32(CLP_ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLD, cfg->adaptp_hi_thresh);
  lsu_write_32(CLP_ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLD, cfg->adaptp_lo_thresh);
  lsu_write_32(CLP_ENTROPY_SRC_REG_ADAPTPS_THRESHOLD,   cfg->adaptps_thresh);

  lsu_write_32(CLP_ENTROPY_SRC_REG_MODULE_ENABLE, MUBI4_TRUE);
}

// Wait for a seed and compare it against the expected value (exp == 0: read and
// skip the seed).
int es_read_and_check_seed(const uint32_t *exp, uint32_t k) {
  uint32_t i;
  uint32_t data;
  int errors = 0;

  for (i = 0; i < ES_MAX_POLLS; i++) {
    if (lsu_read_32(CLP_ENTROPY_SRC_REG_DEBUG_STATUS) &
        ENTROPY_SRC_REG_DEBUG_STATUS_ENTROPY_FIFO_DEPTH_MASK) {
      break;
    }
  }
  if (i == ES_MAX_POLLS) {
    VPRINTF(ERROR, "  seed %d: no seed delivered (MAIN_SM_STATE = 0x%x)\n", k,
            lsu_read_32(CLP_ENTROPY_SRC_REG_MAIN_SM_STATE));
    return ES_SEED_WORDS;
  }

  for (i = 0; i < ES_SEED_WORDS; i++) {
    data = lsu_read_32(CLP_ENTROPY_SRC_REG_ENTROPY_DATA);
    if (exp && data != exp[i]) {
      VPRINTF(ERROR, "  seed %d: word %d got 0x%x want 0x%x\n", k, i, data, exp[i]);
      errors++;
    }
  }
  VPRINTF(LOW, "  seed %d: %s\n", k,
          !exp ? "skipped" : errors ? "MISMATCH" : "matches the model");
  return errors;
}

static int es_expect_zero(uint32_t addr, const char *name) {
  uint32_t data = lsu_read_32(addr);
  if (data != 0) {
    VPRINTF(ERROR, "  %s = 0x%x, expected 0\n", name, data);
    return 1;
  }
  return 0;
}

// Check that no error, alert or health test failure has been recorded.
int es_check_health(void) {
  int errors = 0;
  uint32_t state = lsu_read_32(CLP_ENTROPY_SRC_REG_MAIN_SM_STATE);

  if (state == ES_MAIN_SM_ALERT_HANG || state == ES_MAIN_SM_ERROR) {
    VPRINTF(ERROR, "  MAIN_SM_STATE = 0x%x (alert / error)\n", state);
    errors++;
  }
  errors += es_expect_zero(CLP_ENTROPY_SRC_REG_ERR_CODE, "ERR_CODE");
  errors += es_expect_zero(CLP_ENTROPY_SRC_REG_RECOV_ALERT_STS, "RECOV_ALERT_STS");
  errors += es_expect_zero(CLP_ENTROPY_SRC_REG_ALERT_SUMMARY_FAIL_COUNTS,
                           "ALERT_SUMMARY_FAIL_COUNTS");
  errors += es_expect_zero(CLP_ENTROPY_SRC_REG_REPCNT_TOTAL_FAILS, "REPCNT_TOTAL_FAILS");
  errors += es_expect_zero(CLP_ENTROPY_SRC_REG_REPCNTS_TOTAL_FAILS, "REPCNTS_TOTAL_FAILS");
  errors += es_expect_zero(CLP_ENTROPY_SRC_REG_ADAPTP_HI_TOTAL_FAILS, "ADAPTP_HI_TOTAL_FAILS");
  errors += es_expect_zero(CLP_ENTROPY_SRC_REG_ADAPTP_LO_TOTAL_FAILS, "ADAPTP_LO_TOTAL_FAILS");
  errors += es_expect_zero(CLP_ENTROPY_SRC_REG_ADAPTPS_TOTAL_FAILS, "ADAPTPS_TOTAL_FAILS");
  return errors;
}

void main() {
  int errors = 0;

  VPRINTF(LOW, "----------------------------------\n");
  VPRINTF(LOW, " ENTROPY_SRC smoke test\n"          );
  VPRINTF(LOW, "----------------------------------\n");

  fail_if_itrng_disabled();

  for (uint32_t c = 0; c < ES_NUM_CONFIGS; c++) {
    const es_test_cfg_t *cfg = &es_configs[c];

    VPRINTF(LOW, "Config %d: %s\n", c, cfg->name);
    errors += es_disable();
    es_configure(cfg);
    for (uint32_t k = 0; k < cfg->skip_seeds; k++) {
      errors += es_read_and_check_seed(0, k);
    }
    for (uint32_t k = 0; k < cfg->num_seeds; k++) {
      errors += es_read_and_check_seed(cfg->exp_seeds[k], cfg->skip_seeds + k);
    }
    errors += es_check_health();
  }

  if (errors) {
    VPRINTF(ERROR, "ENTROPY_SRC smoke test failed with %d errors\n", errors);
    SEND_STDOUT_CTRL(0x1);
  } else {
    VPRINTF(LOW, "ENTROPY_SRC smoke test passed\n");
    SEND_STDOUT_CTRL(0xff);
  }
  while (1);
}
