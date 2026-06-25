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
// smoke_test_iccm_hash.c
// Verifies that the ICCM write hash feature computes SHA-384 of data
// written to ICCM and stores the result in PCR4.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Expected PCR4 after extend: SHA-384(48_zeros || SHA-384(iccm_write_stream))
// ICCM writes: 4 words {0x1, 0x2, 0x3, 0x4} as little-endian (no byte swap).
static const uint32_t expected_pcr4[12] = {
    0xe5c90c31, 0x559326f8, 0x581e6ce0, 0xda2ea02c,
    0xc80367c0, 0x0e5a196f, 0x16814243, 0x156d040d,
    0x4cac6766, 0x7c6504dd, 0xad29a6cd, 0xa6743964
};

void main(void) {

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " ICCM Hash -> PCR4 Smoke Test\n");
    VPRINTF(LOW, "----------------------------------\n");

    init_interrupts();

    uint32_t reg_val;
    uint8_t fail_cmd = 0x1;

    // Check if subsystem mode is active (ICCM hash feature only present in SS mode)
    uint32_t hw_config = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
    uint32_t ss_mode = (hw_config >> SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_LOW) & 0x1;

    // Write test data to ICCM (both modes -- ICCM writes always work)
    VPRINTF(LOW, "Writing test data to ICCM...\n");
    volatile uint32_t *iccm = (volatile uint32_t *)RV_ICCM_SADR;
    iccm[0] = 0x00000001;
    iccm[1] = 0x00000002;
    iccm[2] = 0x00000003;
    iccm[3] = 0x00000004;

    VPRINTF(LOW, "Locking ICCM...\n");
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK,
                 SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK);

    if (!ss_mode) {
        // ---------------------------------------------------------------
        // Passive mode: ICCM hash feature not present.
        // Verify PCR4 remains at zero (no HW writes it).
        // ---------------------------------------------------------------
        VPRINTF(LOW, "Passive mode: verifying PCR4 stays zero...\n");
        volatile uint32_t *pcr4 = (volatile uint32_t *)CLP_PV_REG_PCR_ENTRY_4_0;
        for (int i = 0; i < 12; i++) {
            if (pcr4[i] != 0) {
                VPRINTF(ERROR, "ERROR: PCR4[%d] = 0x%x (expected 0 in passive mode)\n",
                        i, pcr4[i]);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
        }
        VPRINTF(LOW, "PASS: PCR4 is zero (passive mode, feature not present)\n");
        SEND_STDOUT_CTRL(0xff);
        return;
    }

    // ---------------------------------------------------------------
    // Subsystem mode: ICCM hash feature active.
    // Wait for the extend FSM to write PCR4.
    // ---------------------------------------------------------------
    VPRINTF(LOW, "Subsystem mode: waiting for PCR4 write...\n");
    uint32_t timeout = 10000;
    while (timeout--) {
        reg_val = lsu_read_32(CLP_PV_REG_PCR_ENTRY_4_0);
        if (reg_val != 0) break;
    }
    if (reg_val == 0) {
        VPRINTF(ERROR, "ERROR: Timed out waiting for PCR4 to be written!\n");
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }

    VPRINTF(LOW, "Checking PCR4 value...\n");
    volatile uint32_t *pcr4 = (volatile uint32_t *)CLP_PV_REG_PCR_ENTRY_4_0;
    uint8_t mismatch = 0;
    for (int i = 0; i < 12; i++) {
        reg_val = pcr4[i];
        if (reg_val != expected_pcr4[i]) {
            VPRINTF(ERROR, "ERROR: PCR4[%d] mismatch! Got 0x%x, expected 0x%x\n",
                    i, reg_val, expected_pcr4[i]);
            mismatch = 1;
        }
    }

    if (mismatch) {
        VPRINTF(ERROR, "FAIL: PCR4 does not match expected SHA-384 digest\n");
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }

    VPRINTF(LOW, "PASS: PCR4 matches expected SHA-384 of ICCM writes!\n");

    // ---------------------------------------------------------------
    // Sanity check: extend PCR0 with the same ICCM digest using the
    // normal SHA512 pcr_hash_extend path. Since PCR0 starts at 0,
    // the result should match PCR4.
    // ---------------------------------------------------------------
    VPRINTF(LOW, "Sanity: Extending PCR0 via SHA512 pcr_hash_extend...\n");

    // Known ICCM digest of {0x1, 0x2, 0x3, 0x4} as LE words:
    static const uint32_t iccm_raw_digest[12] = {
        0x1639dafc, 0xda504134, 0x9489cdac, 0xe63691bc,
        0x887ff539, 0xb61e635b, 0x0f5849e5, 0x85344d5b,
        0xb13af6fa, 0x55f6041a, 0x12fc1ef6, 0xc09cf6cf
    };

    // Trigger PCR read into BLOCK[0:11]
    timeout = 10000;
    while (timeout--) {
        reg_val = lsu_read_32(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);
        if (reg_val & SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK) break;
    }
    lsu_write_32(CLP_SHA512_REG_SHA512_VAULT_RD_CTRL,
                 (1 << SHA512_REG_SHA512_VAULT_RD_CTRL_READ_EN_LOW) |
                 (0 << SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_LOW) |
                 (1 << SHA512_REG_SHA512_VAULT_RD_CTRL_PCR_HASH_EXTEND_LOW));

    timeout = 10000;
    while (timeout--) {
        reg_val = lsu_read_32(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);
        if (reg_val & SHA512_REG_SHA512_VAULT_RD_STATUS_VALID_MASK) break;
    }

    // Write ICCM digest into BLOCK[12:23]
    for (int i = 0; i < 12; i++) {
        lsu_write_32(CLP_SHA512_REG_SHA512_BLOCK_12 + (i * 4), iccm_raw_digest[i]);
    }

    // Write SHA-384 padding into BLOCK[24:31]
    lsu_write_32(CLP_SHA512_REG_SHA512_BLOCK_24, 0x80000000);
    for (int i = 25; i < 31; i++) {
        lsu_write_32(CLP_SHA512_REG_SHA512_BLOCK_0 + (i * 4), 0x00000000);
    }
    lsu_write_32(CLP_SHA512_REG_SHA512_BLOCK_0 + (31 * 4), 0x00000300);

    // Trigger SHA-384 init
    timeout = 10000;
    while (timeout--) {
        reg_val = lsu_read_32(CLP_SHA512_REG_SHA512_STATUS);
        if (reg_val & SHA512_REG_SHA512_STATUS_READY_MASK) break;
    }
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL,
                 (1 << SHA512_REG_SHA512_CTRL_INIT_LOW) |
                 (2 << SHA512_REG_SHA512_CTRL_MODE_LOW) |
                 (1 << SHA512_REG_SHA512_CTRL_LAST_LOW));

    // Wait for completion
    timeout = 10000;
    while (timeout--) {
        reg_val = lsu_read_32(CLP_SHA512_REG_SHA512_STATUS);
        if (reg_val & SHA512_REG_SHA512_STATUS_READY_MASK) break;
    }
    if (!(reg_val & SHA512_REG_SHA512_STATUS_READY_MASK)) {
        VPRINTF(ERROR, "ERROR: SHA512 pcr_hash_extend timed out!\n");
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }

    // Compare PCR0 with PCR4
    VPRINTF(LOW, "Comparing PCR0 vs PCR4...\n");
    volatile uint32_t *pcr0 = (volatile uint32_t *)CLP_PV_REG_PCR_ENTRY_0_0;
    mismatch = 0;
    for (int i = 0; i < 12; i++) {
        uint32_t pcr0_val = pcr0[i];
        uint32_t pcr4_val = pcr4[i];
        if (pcr0_val != pcr4_val) {
            VPRINTF(ERROR, "ERROR: PCR0[%d]=0x%x != PCR4[%d]=0x%x\n",
                    i, pcr0_val, i, pcr4_val);
            mismatch = 1;
        }
    }

    if (mismatch) {
        VPRINTF(ERROR, "FAIL: PCR0 and PCR4 differ after extending with same digest!\n");
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }

    VPRINTF(LOW, "PASS: PCR0 == PCR4 -- extend paths produce identical results!\n");
    SEND_STDOUT_CTRL(0xff);
}
