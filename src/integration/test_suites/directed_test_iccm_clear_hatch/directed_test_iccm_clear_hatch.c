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
// directed_test_iccm_clear_hatch.c
// Verifies the PCR_CTRL[n].clear escape hatch for PCR4 and PCR5.
// FW can wipe these PCRs to zero, but cannot write a nonzero value after.
//
// Step 1: Run ICCM hash to populate PCR4/PCR5 with non-zero digests.
// Step 2: Write PCR_CTRL[4].clear and PCR_CTRL[5].clear; both must read zero.
// Step 3: FW AHB write 0xDEADBEEF; both must still read zero.
// Step 4: SHA-ctrl pcr_hash_extend targeting PCR4 and PCR5; both must still
//         read zero (pv.sv guard still drops pv_write[0] to entries 4/5).

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

// Arbitrary digest pattern for the SHA-ctrl extend attempt
static const uint32_t test_digest[ICCM_HASH_PCR_DWORDS] = {
    0xdeadbeef, 0xcafebabe, 0x12345678, 0x9abcdef0,
    0x11223344, 0x55667788, 0x99aabbcc, 0xddeeff00,
    0xf00dface, 0xfeedface, 0x01234567, 0x89abcdef
};

void main(void) {

    uint8_t fail_cmd = 0x1;

    VPRINTF(LOW, "------------------------------------------\n");
    VPRINTF(LOW, " ICCM PCR4/PCR5 Clear Hatch Test\n");
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

    // Step 1: run ICCM hash so PCR4 and PCR5 hold non-zero digests
    VPRINTF(LOW, "Running ICCM hash to populate PCR4/PCR5...\n");
    if (!run_default_iccm_hash()) {
        VPRINTF(ERROR, "FAIL: Timed out waiting for PCR4 after ICCM hash\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    if (!check_pcr_nonzero(CLP_PV_REG_PCR_ENTRY_4_0, 4) ||
        !check_pcr_nonzero(CLP_PV_REG_PCR_ENTRY_5_0, 5)) {
        VPRINTF(ERROR, "FAIL: PCR4/PCR5 not populated after ICCM hash\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: PCR4 and PCR5 populated by ICCM hash\n");

    // Step 2: assert PCR_CTRL[4].clear and PCR_CTRL[5].clear
    VPRINTF(LOW, "Writing PCR_CTRL[4].clear and PCR_CTRL[5].clear...\n");
    lsu_write_32(CLP_PV_REG_PCR_CTRL_4, PV_REG_PCR_CTRL_4_CLEAR_MASK);
    lsu_write_32(CLP_PV_REG_PCR_CTRL_5, PV_REG_PCR_CTRL_5_CLEAR_MASK);
    if (!check_pcr_zero(CLP_PV_REG_PCR_ENTRY_4_0, 4) ||
        !check_pcr_zero(CLP_PV_REG_PCR_ENTRY_5_0, 5)) {
        VPRINTF(ERROR, "FAIL: PCR4/PCR5 not zeroed by PCR_CTRL.clear\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: PCR4 and PCR5 zeroed by clear hatch\n");

    // Step 3: FW AHB writes must still be blocked
    VPRINTF(LOW, "Attempting FW AHB write attack on cleared PCRs...\n");
    fw_write_attack(CLP_PV_REG_PCR_ENTRY_4_0);
    fw_write_attack(CLP_PV_REG_PCR_ENTRY_5_0);
    if (!check_pcr_zero(CLP_PV_REG_PCR_ENTRY_4_0, 4) ||
        !check_pcr_zero(CLP_PV_REG_PCR_ENTRY_5_0, 5)) {
        VPRINTF(ERROR, "FAIL: FW AHB write tampered cleared PCR\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: FW AHB write blocked on cleared PCRs\n");

    // Step 4: SHA-ctrl pcr_hash_extend must still be blocked too
    VPRINTF(LOW, "Attempting SHA-ctrl extend on cleared PCRs...\n");
    if (!sha_ctrl_extend(4, test_digest)) {
        VPRINTF(ERROR, "FAIL: SHA512 timed out during PCR4 extend attempt\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    if (!sha_ctrl_extend(5, test_digest)) {
        VPRINTF(ERROR, "FAIL: SHA512 timed out during PCR5 extend attempt\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    if (!check_pcr_zero(CLP_PV_REG_PCR_ENTRY_4_0, 4) ||
        !check_pcr_zero(CLP_PV_REG_PCR_ENTRY_5_0, 5)) {
        VPRINTF(ERROR, "FAIL: SHA-ctrl extend tampered cleared PCR\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: SHA-ctrl extend blocked on cleared PCRs\n");

    VPRINTF(LOW, "=== Clear hatch verified ===\n");
    SEND_STDOUT_CTRL(0xff);
}
