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
// directed_test_iccm_sha_ctrl_block.c
// Verifies the regular SHA512 controller's pcr_hash_extend path cannot
// target PCR4 or PCR5. The pv.sv guard drops any pv_write[0] to entry 4/5.
//
// Step 1: SHA-ctrl extend targeting PCR4 -- PCR4 must remain zero.
// Step 2: SHA-ctrl extend targeting PCR5 -- PCR5 must remain zero.
// Step 3: Control: same flow against PCR0 -- PCR0 must change (proves the
//         extend path itself works).

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

// Arbitrary digest pattern fed to BLOCK[12:23] for the extend
static const uint32_t test_digest[ICCM_HASH_PCR_DWORDS] = {
    0xdeadbeef, 0xcafebabe, 0x12345678, 0x9abcdef0,
    0x11223344, 0x55667788, 0x99aabbcc, 0xddeeff00,
    0xf00dface, 0xfeedface, 0x01234567, 0x89abcdef
};

void main(void) {

    uint8_t fail_cmd = 0x1;

    VPRINTF(LOW, "------------------------------------------\n");
    VPRINTF(LOW, " ICCM SHA-Ctrl PCR4/PCR5 Block Test\n");
    VPRINTF(LOW, "------------------------------------------\n");

    init_interrupts();

    // Step 1: SHA-ctrl extend targeting PCR4 -- pv.sv guard must drop write
    VPRINTF(LOW, "Attempting SHA-ctrl extend to PCR4 (must be blocked)...\n");
    if (!sha_ctrl_extend(4, test_digest)) {
        VPRINTF(ERROR, "FAIL: SHA512 timed out during PCR4 extend attempt\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    if (!check_pcr_zero(CLP_PV_REG_PCR_ENTRY_4_0, 4)) {
        VPRINTF(ERROR, "FAIL: PCR4 changed -- pv.sv guard did not drop pv_write[0]\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: PCR4 stayed zero after SHA-ctrl extend attempt\n");

    // Step 2: same against PCR5
    VPRINTF(LOW, "Attempting SHA-ctrl extend to PCR5 (must be blocked)...\n");
    if (!sha_ctrl_extend(5, test_digest)) {
        VPRINTF(ERROR, "FAIL: SHA512 timed out during PCR5 extend attempt\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    if (!check_pcr_zero(CLP_PV_REG_PCR_ENTRY_5_0, 5)) {
        VPRINTF(ERROR, "FAIL: PCR5 changed -- pv.sv guard did not drop pv_write[0]\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: PCR5 stayed zero after SHA-ctrl extend attempt\n");

    // Step 3: control -- same flow against PCR0 must succeed
    VPRINTF(LOW, "Extending PCR0 via SHA-ctrl (control, must succeed)...\n");
    if (!sha_ctrl_extend(0, test_digest)) {
        VPRINTF(ERROR, "FAIL: SHA512 timed out during PCR0 extend\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    if (!check_pcr_nonzero(CLP_PV_REG_PCR_ENTRY_0_0, 0)) {
        VPRINTF(ERROR, "FAIL: PCR0 unchanged -- SHA-ctrl extend path itself is broken\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: PCR0 changed -- control extend works as expected\n");

    VPRINTF(LOW, "=== SHA-ctrl PCR4/PCR5 block verified ===\n");
    SEND_STDOUT_CTRL(0xff);
}
