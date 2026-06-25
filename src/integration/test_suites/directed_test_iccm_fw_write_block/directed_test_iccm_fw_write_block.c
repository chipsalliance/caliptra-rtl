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
// directed_test_iccm_fw_write_block.c
// Verifies that FW AHB writes to PCR4 and PCR5 are blocked. Only the ICCM
// hash engine can write these PCRs; FW writes are silently dropped.
//
// Step 1: Pre-hash -- both PCRs are zero. FW writes 0xDEADBEEF to every
//         dword of PCR_ENTRY[4] and PCR_ENTRY[5]. All 24 dwords must
//         still read 0 after the writes.
// Step 2: Run a real ICCM hash so PCR4 and PCR5 hold non-zero digests.
// Step 3: Post-hash -- FW writes 0xDEADBEEF again. Both PCRs must still
//         equal the post-hash digest, not 0xDEADBEEF.

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

    VPRINTF(LOW, "------------------------------------------\n");
    VPRINTF(LOW, " ICCM FW Write Block Test\n");
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

    // Step 1: pre-hash empty-PCR attack
    VPRINTF(LOW, "Attempting FW write attack on empty PCR4/PCR5...\n");
    fw_write_attack(CLP_PV_REG_PCR_ENTRY_4_0);
    fw_write_attack(CLP_PV_REG_PCR_ENTRY_5_0);
    if (!check_pcr_zero(CLP_PV_REG_PCR_ENTRY_4_0, 4) ||
        !check_pcr_zero(CLP_PV_REG_PCR_ENTRY_5_0, 5)) {
        VPRINTF(ERROR, "FAIL: empty PCR4/PCR5 not zero after FW write\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: empty PCR4 and PCR5 stayed zero\n");

    // Step 2: run a real ICCM hash so PCR4 and PCR5 hold non-zero digests
    VPRINTF(LOW, "Running ICCM hash to populate PCR4/PCR5...\n");
    if (!run_default_iccm_hash()) {
        VPRINTF(ERROR, "FAIL: Timed out waiting for PCR4 after ICCM hash\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }

    // Step 3: post-hash populated-PCR attack
    VPRINTF(LOW, "Attempting FW write attack on populated PCR4/PCR5...\n");
    fw_write_attack(CLP_PV_REG_PCR_ENTRY_4_0);
    fw_write_attack(CLP_PV_REG_PCR_ENTRY_5_0);
    if (!check_pcr_match(CLP_PV_REG_PCR_ENTRY_4_0, expected_default_iccm_hash_pcr, 4, 0) ||
        !check_pcr_match(CLP_PV_REG_PCR_ENTRY_5_0, expected_default_iccm_hash_pcr, 5, 0)) {
        VPRINTF(ERROR, "FAIL: populated PCR4/PCR5 tampered by FW write\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: populated PCR4 and PCR5 unchanged by FW write attack\n");

    VPRINTF(LOW, "=== FW write block verified ===\n");
    SEND_STDOUT_CTRL(0xff);
}
