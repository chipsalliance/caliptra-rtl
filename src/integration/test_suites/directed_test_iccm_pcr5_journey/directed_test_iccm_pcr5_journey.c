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
// directed_test_iccm_pcr5_journey.c
// Multi-boot directed test for the PCR5 "Journey" register.
// PCR4 is wiped on every fw_update_reset; PCR5 is only wiped on cold reset
// so it accumulates across boots.  Runs 3 ICCM-hash boots separated by
// fw_update_reset and verifies PCR4 resets each time while PCR5 chains.
//
// Boot 0: 64 words {0x10..0x4F}     --> lock --> check PCR4 + PCR5 --> fw_update_reset
// Boot 1: 28 words {0xBB00..0xBB1B} --> lock --> check PCR4 + PCR5 --> fw_update_reset
// Boot 2: 32 words {0xC000..0xC01F} --> lock --> check PCR4 + PCR5 --> PASS
//
// Pre-hash on Boot >= 1: verify PCR4 was wiped and PCR5 survived.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "iccm_hash.h"
#include "printf.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Persistent state across fw_update_reset (DCCM survives reset)
static uint32_t iteration __attribute__ ((section(".dccm.persistent"))) = 0;

// Expected PCR4 values per boot (always extend-from-zero of that boot's data)
// Boot 0: 64 words {0x10..0x4F} -- matches expected_default_iccm_hash_pcr
static const uint32_t expected_pcr4_boot0[ICCM_HASH_PCR_DWORDS] = {
    0x73c26a32, 0x28bce060, 0x94b092a6, 0x4d3c6007,
    0xbe359bab, 0xa1b76c71, 0x812f325a, 0x99a13504,
    0x665282d5, 0xa2df5e62, 0xf00187ff, 0x61da0cd0
};
// Boot 1: 28 words {0xBB00..0xBB1B}
static const uint32_t expected_pcr4_boot1[ICCM_HASH_PCR_DWORDS] = {
    0xbd1c801b, 0x247dd517, 0x3ddff4e1, 0xf4336345,
    0x177dd7d3, 0xf7803a8b, 0x25e87434, 0x3811fde4,
    0x5aee0f9b, 0x0012e968, 0xf5cee942, 0x1941d55e
};
// Boot 2: 32 words {0xC000..0xC01F}
static const uint32_t expected_pcr4_boot2[ICCM_HASH_PCR_DWORDS] = {
    0x01c32e80, 0x6e0812d2, 0x3d2cf9c7, 0xd716f30f,
    0xaf590d10, 0x167979cf, 0x8e8ff08d, 0x1f7c1e42,
    0xfb0ccb85, 0x86552358, 0x0ab4d913, 0xa9bd6004
};

// Expected PCR5 values per boot, chained Journey-style:
//   PCR5_boot0 = SHA-384(48_zeros        || iccm_digest_boot0)
//   PCR5_boot1 = SHA-384(PCR5_boot0      || iccm_digest_boot1)
//   PCR5_boot2 = SHA-384(PCR5_boot1      || iccm_digest_boot2)
// boot 0 matches expected_pcr4_boot0 (first extend is from zero).
static const uint32_t expected_pcr5_boot0[ICCM_HASH_PCR_DWORDS] = {
    0x73c26a32, 0x28bce060, 0x94b092a6, 0x4d3c6007,
    0xbe359bab, 0xa1b76c71, 0x812f325a, 0x99a13504,
    0x665282d5, 0xa2df5e62, 0xf00187ff, 0x61da0cd0
};
// boot 1: chained from boot 0
static const uint32_t expected_pcr5_boot1[ICCM_HASH_PCR_DWORDS] = {
    0x16a6931f, 0x9de7cc27, 0xae1f95a4, 0x5f019e6d,
    0x10314fc3, 0x081f95dd, 0x9f0c3b99, 0x7ee4d957,
    0x7d11da80, 0x182b2076, 0x30cd492f, 0x1844c378
};
// boot 2: chained from boot 1
static const uint32_t expected_pcr5_boot2[ICCM_HASH_PCR_DWORDS] = {
    0x821e8f81, 0x6e3251aa, 0xa929f6b3, 0x531b9cd5,
    0x2e51001c, 0x3400d178, 0xa88f785f, 0x419deb7e,
    0xb686dba3, 0x54417144, 0x7eb49f6e, 0x6b182c0b
};

// Run an ICCM hash with a specific data pattern (each boot uses different data)
static uint8_t run_boot_hash(uint32_t boot) {
    volatile uint32_t *iccm = (volatile uint32_t *)RV_ICCM_SADR;
    if (boot == 0) {
        for (uint32_t i = 0; i < 64; i++) iccm[i] = 0x10 + i;
    } else if (boot == 1) {
        for (uint32_t i = 0; i < 28; i++) iccm[i] = 0xBB00 + i;
    } else {
        for (uint32_t i = 0; i < 32; i++) iccm[i] = 0xC000 + i;
    }
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK,
                 SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK);
    return wait_pcr4_ready();
}

void main(void) {

    uint8_t fail_cmd = 0x1;

    VPRINTF(LOW, "------------------------------------------\n");
    VPRINTF(LOW, " ICCM PCR5 Journey Test - Boot %d\n", iteration);
    VPRINTF(LOW, "------------------------------------------\n");

    init_interrupts();

    // Check if subsystem mode is active (ICCM hash feature only in SS mode)
    uint32_t hw_config = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
    uint32_t ss_mode = (hw_config >> SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_LOW) & 0x1;
    if (!ss_mode) {
        VPRINTF(LOW, "Passive mode: ICCM hash not present, skipping. PASS\n");
        SEND_STDOUT_CTRL(0xff);
        return;
    }

    // Pre-hash checks on every boot >= 1: PCR4 was wiped, PCR5 survived.
    if (iteration == 1) {
        VPRINTF(LOW, "Boot1 pre-check: PCR4 cleared, PCR5 holds Boot0 value\n");
        if (!check_pcr_zero(CLP_PV_REG_PCR_ENTRY_4_0, 4)) {
            VPRINTF(ERROR, "FAIL: PCR4 not cleared after fw_update_reset\n");
            SEND_STDOUT_CTRL(fail_cmd); while(1);
        }
        if (!check_pcr_match(CLP_PV_REG_PCR_ENTRY_5_0, expected_pcr5_boot0, 5, 1)) {
            VPRINTF(ERROR, "FAIL: PCR5 did not survive fw_update_reset (Boot1 pre-check)\n");
            SEND_STDOUT_CTRL(fail_cmd); while(1);
        }
    } else if (iteration == 2) {
        VPRINTF(LOW, "Boot2 pre-check: PCR4 cleared, PCR5 holds Boot1 value\n");
        if (!check_pcr_zero(CLP_PV_REG_PCR_ENTRY_4_0, 4)) {
            VPRINTF(ERROR, "FAIL: PCR4 not cleared after fw_update_reset\n");
            SEND_STDOUT_CTRL(fail_cmd); while(1);
        }
        if (!check_pcr_match(CLP_PV_REG_PCR_ENTRY_5_0, expected_pcr5_boot1, 5, 2)) {
            VPRINTF(ERROR, "FAIL: PCR5 did not survive fw_update_reset (Boot2 pre-check)\n");
            SEND_STDOUT_CTRL(fail_cmd); while(1);
        }
    }

    // Run this boot's ICCM hash
    if (!run_boot_hash(iteration)) {
        VPRINTF(ERROR, "FAIL: Timed out waiting for PCR4 (boot %d)\n", iteration);
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }

    // Verify PCR4 (extend from zero) and PCR5 (chained extend)
    const uint32_t *exp_pcr4;
    const uint32_t *exp_pcr5;
    if (iteration == 0)      { exp_pcr4 = expected_pcr4_boot0; exp_pcr5 = expected_pcr5_boot0; }
    else if (iteration == 1) { exp_pcr4 = expected_pcr4_boot1; exp_pcr5 = expected_pcr5_boot1; }
    else                     { exp_pcr4 = expected_pcr4_boot2; exp_pcr5 = expected_pcr5_boot2; }

    if (!check_pcr_match(CLP_PV_REG_PCR_ENTRY_4_0, exp_pcr4, 4, iteration)) {
        VPRINTF(ERROR, "FAIL: PCR4 mismatch on boot %d\n", iteration);
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    if (!check_pcr_match(CLP_PV_REG_PCR_ENTRY_5_0, exp_pcr5, 5, iteration)) {
        VPRINTF(ERROR, "FAIL: PCR5 mismatch on boot %d\n", iteration);
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: Boot %d PCR4 and PCR5 both match expected\n", iteration);

    iteration++;

    if (iteration < 3) {
        VPRINTF(LOW, "Triggering fw_update_reset...\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET,
                     SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK);
        while(1);
    }

    VPRINTF(LOW, "=== ALL 3 BOOTS PASSED - PCR5 Journey verified ===\n");
    SEND_STDOUT_CTRL(0xff);
}
