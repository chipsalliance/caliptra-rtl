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
// directed_test_iccm_cold_reset_pcr5.c
// Verifies PCR5 (Journey) is wiped on cold reset (cptra_pwrgood toggle).
// PCR5 normally survives fw_update_reset; cold reset is the only event
// that re-anchors the journey chain to zero.
//
// Boot 0: Run ICCM hash so PCR5 holds a non-zero digest, then trigger
//         cold reset (SEND_STDOUT_CTRL 0xf5).
// Boot 1: After cold-boot, PCR5 must read all zeros before any new hash.

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

// Persistent state across cold reset (DCCM .dccm.persistent survives 0xf5)
static uint32_t iteration __attribute__ ((section(".dccm.persistent"))) = 0;

void main(void) {

    uint8_t fail_cmd = 0x1;

    VPRINTF(LOW, "------------------------------------------\n");
    VPRINTF(LOW, " ICCM Cold-Reset PCR5 Test - Boot %d\n", iteration);
    VPRINTF(LOW, "------------------------------------------\n");

    init_interrupts();

    if (iteration == 0) {
        // Boot 0: populate PCR5 with a real digest, then cold reset
        VPRINTF(LOW, "Boot 0: running ICCM hash to populate PCR5\n");
        if (!run_default_iccm_hash()) {
            VPRINTF(ERROR, "FAIL: Timed out waiting for PCR4 after ICCM hash\n");
            SEND_STDOUT_CTRL(fail_cmd); while(1);
        }
        if (!check_pcr_nonzero(CLP_PV_REG_PCR_ENTRY_5_0, 5)) {
            VPRINTF(ERROR, "FAIL: PCR5 not populated after ICCM hash\n");
            SEND_STDOUT_CTRL(fail_cmd); while(1);
        }
        VPRINTF(LOW, "PASS: Boot 0 PCR5 populated\n");

        iteration++;
        VPRINTF(LOW, "Triggering cold reset for Boot 1\n");
        SEND_STDOUT_CTRL(0xf5);
        while(1);
    }

    // Boot 1: cold-boot fresh. PCR5 must be all zeros (Journey re-anchored).
    VPRINTF(LOW, "Boot 1: post-cold-reset, PCR5 must be all zeros\n");
    if (!check_pcr_zero(CLP_PV_REG_PCR_ENTRY_5_0, 5)) {
        VPRINTF(ERROR, "FAIL: PCR5 not wiped on cold reset\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: PCR5 wiped to zero on cold reset\n");

    VPRINTF(LOW, "=== Cold-reset PCR5 verified ===\n");
    SEND_STDOUT_CTRL(0xff);
}
