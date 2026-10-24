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
// Fuse-like firmware configuration register smoke test.
//
// Checks the access rules of the registers below: SoC-writable until
// CPTRA_FUSE_WR_DONE and locked afterwards, read-only to Caliptra, reset only by
// cptra_pwrgood, and SoC access restricted to the fuse AXI_USER.
//   CPTRA_iTRNG_ENTROPY_CONFIG_0/1/2, CPTRA_iTRNG1_ENTROPY_CONFIG_0/1/2,
//   SS_OTP_FC_STATUS_CFG, SS_OTP_FC_CMD_CFG, SS_FW_FEATURE_CFG
//
// Companion to the +CALIPTRA_TEST_FW_CFG_LOCK hooks in caliptra_top_tb_soc_bfm.sv.
// The plusarg is declared in smoke_test_fw_cfg_lock.yml; a direct make invocation
// must pass RUN_PLUSARGS=+CALIPTRA_TEST_FW_CFG_LOCK or the firmware hangs.
//
//   boot 0 (cold): BFM programs pattern A before CPTRA_FUSE_WR_DONE and attempts
//                  pattern B after it. FW checks A, then attempts its own writes
//                  and checks A again.
//   boot 1 (warm): BFM attempts pattern B before re-writing CPTRA_FUSE_WR_DONE.
//                  FW checks A survived the warm reset.
//   boot 2 (cold): BFM checks every register reads 0, locks the fuse AXI_USER,
//                  checks a default-user pattern C gets AXI errors and a
//                  valid-user pattern D lands. FW checks the BFM verdict and D.

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"
#include <stdint.h>
#include "printf.h"
#include "caliptra_isr.h"

volatile uint32_t* stdout = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Must match caliptra_top_tb_pkg.sv
#define FW_CFG_POST_LOCK_WR_DONE    0x600dfc01u
#define FW_CFG_AXI_USER_CHECK_PASS  0x600dfc02u
#define FW_CFG_AXI_USER_CHECK_FAIL  0xdeadfc03u
#define FW_CFG_PATTERN_A            0xa5a55a5au
#define FW_CFG_PATTERN_D            0x3cc3c33cu

typedef struct {
    const char *name;
    uint32_t    addr;
    uint32_t    mask; // implemented bits
} fw_cfg_reg_t;

// Order must match FW_CFG_REG_ADDR in caliptra_top_tb_soc_bfm.sv
static const fw_cfg_reg_t fw_cfg_regs[] = {
    {"CPTRA_iTRNG_ENTROPY_CONFIG_0",  CLP_SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0,  0xffffffffu},
    {"CPTRA_iTRNG_ENTROPY_CONFIG_1",  CLP_SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1,  0xffffffffu},
    {"CPTRA_iTRNG_ENTROPY_CONFIG_2",  CLP_SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_2,  0xffffffffu},
    {"CPTRA_iTRNG1_ENTROPY_CONFIG_0", CLP_SOC_IFC_REG_CPTRA_ITRNG1_ENTROPY_CONFIG_0, 0xffffffffu},
    {"CPTRA_iTRNG1_ENTROPY_CONFIG_1", CLP_SOC_IFC_REG_CPTRA_ITRNG1_ENTROPY_CONFIG_1, 0xffffffffu},
    {"CPTRA_iTRNG1_ENTROPY_CONFIG_2", CLP_SOC_IFC_REG_CPTRA_ITRNG1_ENTROPY_CONFIG_2, 0xffffffffu},
    {"SS_OTP_FC_STATUS_CFG",          CLP_SOC_IFC_REG_SS_OTP_FC_STATUS_CFG,          0xffffffffu},
    {"SS_OTP_FC_CMD_CFG",             CLP_SOC_IFC_REG_SS_OTP_FC_CMD_CFG,
                                      SOC_IFC_REG_SS_OTP_FC_CMD_CFG_DIRECT_ACCESS_CMD_OFFSET_MASK},
    {"SS_FW_FEATURE_CFG",             CLP_SOC_IFC_REG_SS_FW_FEATURE_CFG,
                                      SOC_IFC_REG_SS_FW_FEATURE_CFG_STABLE_OWNER_KEY_EN_MASK |
                                      SOC_IFC_REG_SS_FW_FEATURE_CFG_VENDOR_DEBUG_IMAGES_DIS_MASK},
};
#define FW_CFG_NUM_REGS (sizeof(fw_cfg_regs) / sizeof(fw_cfg_regs[0]))

// Must match fw_cfg_value() in caliptra_top_tb_soc_bfm.sv
static inline uint32_t fw_cfg_value(uint32_t pattern, uint32_t idx) {
    return pattern ^ (0x11111111u * (idx + 1u));
}

static void fail(const char *why, uint32_t got, uint32_t exp) {
    VPRINTF(ERROR, "ERROR: %s (got 0x%08x, expected 0x%08x)\n", why, got, exp);
    SEND_STDOUT_CTRL(0x1);
    while (1);
}

static void check_regs(uint32_t pattern, const char *phase) {
    VPRINTF(LOW, "FW: %s\n", phase);
    for (uint32_t i = 0; i < FW_CFG_NUM_REGS; i++) {
        uint32_t exp = fw_cfg_value(pattern, i) & fw_cfg_regs[i].mask;
        uint32_t got = lsu_read_32(fw_cfg_regs[i].addr);
        if (got != exp) {
            VPRINTF(ERROR, "ERROR: %s mismatch\n", fw_cfg_regs[i].name);
            fail(phase, got, exp);
        }
    }
}

static void check_warm_reset(uint32_t exp) {
    uint32_t got = (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_RESET_REASON) &
                    SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK) ? 1u : 0u;
    if (got != exp) {
        fail("CPTRA_RESET_REASON.WARM_RESET", got, exp);
    }
}

void main() {
    uint32_t verdict;

    VPRINTF(LOW, "------------------------------------------\n");
    VPRINTF(LOW, " Smoke test fw cfg register lock, boot %d\n", rst_count);
    VPRINTF(LOW, "------------------------------------------\n");

    if (rst_count == 0) {
        // BFM reports when its writes after CPTRA_FUSE_WR_DONE are done
        while (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0) != FW_CFG_POST_LOCK_WR_DONE);
        check_warm_reset(0);
        check_regs(FW_CFG_PATTERN_A, "boot 0: SoC writes land before CPTRA_FUSE_WR_DONE and are dropped after it");

        for (uint32_t i = 0; i < FW_CFG_NUM_REGS; i++) {
            lsu_write_32(fw_cfg_regs[i].addr, ~fw_cfg_value(FW_CFG_PATTERN_A, i));
        }
        check_regs(FW_CFG_PATTERN_A, "boot 0: Caliptra writes are dropped");

        rst_count = 1;
        VPRINTF(LOW, "FW: requesting warm reset\n");
        SEND_STDOUT_CTRL(0xf6);
        while (1);
    }
    else if (rst_count == 1) {
        check_warm_reset(1);
        check_regs(FW_CFG_PATTERN_A, "boot 1: values survive warm reset and SoC writes stay locked");

        rst_count = 2;
        VPRINTF(LOW, "FW: requesting cold reset\n");
        SEND_STDOUT_CTRL(0xf5);
        while (1);
    }
    else {
        check_warm_reset(0);

        do {
            verdict = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);
        } while ((verdict != FW_CFG_AXI_USER_CHECK_PASS) && (verdict != FW_CFG_AXI_USER_CHECK_FAIL));
        if (verdict != FW_CFG_AXI_USER_CHECK_PASS) {
            fail("BFM reset-value / fuse AXI_USER checks, see [fw_cfg_lock] errors in sim log", verdict, FW_CFG_AXI_USER_CHECK_PASS);
        }
        check_regs(FW_CFG_PATTERN_D, "boot 2: only the valid fuse AXI_USER write lands");

        VPRINTF(LOW, "FW: all fw cfg register lock checks passed\n");
        SEND_STDOUT_CTRL(0xff);
    }
}
