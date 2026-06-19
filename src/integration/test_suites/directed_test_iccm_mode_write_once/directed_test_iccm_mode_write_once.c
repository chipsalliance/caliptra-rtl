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
// directed_test_iccm_mode_write_once.c
// Verifies ICCM_MODE is write-once per boot. The iccm_mode_done sticky
// flag in sha512_acc_top.sv blocks re-trigger until iccm_unlock fires.
//
// Step 1: Run an ICCM hash to completion, capture the resulting PCR4.
// Step 2: Re-write MODE.ICCM_MODE = 1; field must read back zero.
// Step 3: Write fresh data to ICCM and assert iccm_lock again; PCR4
//         must NOT change (no second hash happens).

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

void main(void) {

    uint8_t fail_cmd = 0x1;
    uint32_t pcr4_after_first[ICCM_HASH_PCR_DWORDS];

    VPRINTF(LOW, "------------------------------------------\n");
    VPRINTF(LOW, " ICCM_MODE Write-Once Test\n");
    VPRINTF(LOW, "------------------------------------------\n");

    init_interrupts();

    // Step 1: run first ICCM hash and snapshot PCR4
    VPRINTF(LOW, "Running first ICCM hash...\n");
    if (!run_default_iccm_hash()) {
        VPRINTF(ERROR, "FAIL: Timed out waiting for PCR4 after first hash\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    snapshot_pcr(CLP_PV_REG_PCR_ENTRY_4_0, pcr4_after_first);
    VPRINTF(LOW, "PASS: First hash done, PCR4 snapshot taken\n");

    // Step 2: try to re-trigger ICCM_MODE
    VPRINTF(LOW, "Attempting to re-set MODE.ICCM_MODE...\n");
    lsu_write_32(CLP_SHA512_ACC_CSR_MODE, SHA512_ACC_CSR_MODE_ICCM_MODE_MASK);
    uint32_t mode_reg = lsu_read_32(CLP_SHA512_ACC_CSR_MODE);
    if (mode_reg & SHA512_ACC_CSR_MODE_ICCM_MODE_MASK) {
        VPRINTF(ERROR, "FAIL: ICCM_MODE re-triggered! mode_reg=0x%x\n", mode_reg);
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: ICCM_MODE blocked (read back 0x%x)\n", mode_reg);

    // Step 3: write fresh data to ICCM and assert iccm_lock again.
    // No second hash should happen, so PCR4 must equal the Step-1 snapshot.
    VPRINTF(LOW, "Writing fresh ICCM data + locking ICCM (PCR4 must not change)...\n");
    volatile uint32_t *iccm = (volatile uint32_t *)RV_ICCM_SADR;
    for (uint32_t i = 0; i < 32; i++) {
        iccm[i] = 0xAA00 + i;
    }
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK,
                 SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK);
    if (!check_pcr_match(CLP_PV_REG_PCR_ENTRY_4_0, pcr4_after_first, 4, 0)) {
        VPRINTF(ERROR, "FAIL: PCR4 changed after re-trigger attempt\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: PCR4 unchanged after re-trigger attempt\n");

    VPRINTF(LOW, "=== ICCM_MODE write-once verified ===\n");
    SEND_STDOUT_CTRL(0xff);
}
