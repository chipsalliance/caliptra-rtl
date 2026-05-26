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

// ICCM_MODE field is bit[2] of the MODE register (added in this feature).
// Until CSR is regenerated, define manually.
#ifndef SHA512_ACC_CSR_MODE_ICCM_MODE_MASK
#define SHA512_ACC_CSR_MODE_ICCM_MODE_MASK (0x4)
#endif

// Test pattern: 4 words written to ICCM
// CPU is little-endian, so ICCM stores bytes: 01 00 00 00  02 00 00 00 ...
// SHA-384 hashes the raw memory contents (no byte swap in iccm_mode).
// Expected SHA-384 digest (12 dwords):
static const uint32_t expected_pcr4[12] = {
    0x1639dafc, 0xda504134, 0x9489cdac, 0xe63691bc,
    0x887ff539, 0xb61e635b, 0x0f5849e5, 0x85344d5b,
    0xb13af6fa, 0x55f6041a, 0x12fc1ef6, 0xc09cf6cf
};

void main(void) {

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " ICCM Hash -> PCR4 Smoke Test\n");
    VPRINTF(LOW, "----------------------------------\n");

    init_interrupts();

    uint32_t reg_val;
    uint8_t fail_cmd = 0x1;

    // ---------------------------------------------------------------
    // Step 1: Acquire SHA accelerator lock
    // The LOCK register resets to 1 (locked). Write-1-to-clear releases it,
    // then the next read returns 0 (acquired) or 1 (contention).
    // ---------------------------------------------------------------
    VPRINTF(LOW, "Releasing SHA acc lock (reset default)...\n");
    lsu_write_32(CLP_SHA512_ACC_CSR_LOCK, SHA512_ACC_CSR_LOCK_LOCK_MASK);

    VPRINTF(LOW, "Acquiring SHA acc lock...\n");
    do {
        reg_val = lsu_read_32(CLP_SHA512_ACC_CSR_LOCK);
    } while (reg_val & SHA512_ACC_CSR_LOCK_LOCK_MASK);
    VPRINTF(LOW, "SHA acc lock acquired\n");

    // ---------------------------------------------------------------
    // Step 2: Set ICCM_MODE in SHA acc MODE register
    // ---------------------------------------------------------------
    VPRINTF(LOW, "Setting ICCM_MODE...\n");
    lsu_write_32(CLP_SHA512_ACC_CSR_MODE, SHA512_ACC_CSR_MODE_ICCM_MODE_MASK);

    // ---------------------------------------------------------------
    // Step 3: Write known data to ICCM
    // The AND-OR mux in caliptra_top captures each ICCM write and
    // feeds it to the SHA accelerator in iccm_mode.
    // ---------------------------------------------------------------
    VPRINTF(LOW, "Writing test data to ICCM...\n");
    volatile uint32_t *iccm = (volatile uint32_t *)RV_ICCM_SADR;
    iccm[0] = 0x00000001;
    iccm[1] = 0x00000002;
    iccm[2] = 0x00000003;
    iccm[3] = 0x00000004;

    // ---------------------------------------------------------------
    // Step 4: Lock ICCM (triggers hash finalization)
    // ---------------------------------------------------------------
    VPRINTF(LOW, "Locking ICCM (triggers hash finalize)...\n");
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK,
                 SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK);

    // ---------------------------------------------------------------
    // Step 5: Wait for hash completion
    // The SHA engine processes padding and computes the final digest,
    // then the kv_write_client sequences it into PCR4.
    // Poll until PCR4[0] is non-zero (digest written).
    // ---------------------------------------------------------------
    VPRINTF(LOW, "Waiting for PCR4 write...\n");
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

    // ---------------------------------------------------------------
    // Step 6: Read PCR4 and compare against expected SHA-384 digest
    // ---------------------------------------------------------------
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
    SEND_STDOUT_CTRL(0xff); // End test with success
}
