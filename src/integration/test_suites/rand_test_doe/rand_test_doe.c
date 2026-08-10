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

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "doe.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#ifdef MY_RANDOM_SEED
    unsigned time = (unsigned) MY_RANDOM_SEED;
#else
    unsigned time = 0;
#endif

// KV slot 23 is the OCP LOCK key-release slot (OCP_LOCK_KEY_RELEASE_KV_SLOT in
// kv_defines_pkg.sv). When OCP lock is in progress, only AES may write it, so a
// DOE write targeting this slot must be rejected by the KV write-rule check.
#define OCP_LOCK_KEY_RELEASE_KV_SLOT 23
// KV_NUM_KEYS from kv_defines_pkg.sv (slots 0..23).
#define NUM_KV_SLOTS                 24

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Program DOE_CTRL with the given command and KV destination slot.
void doe_start(const enum doe_cmd_e cmd, uint32_t kv_dest) {
    lsu_write_32(CLP_DOE_REG_DOE_CTRL,
        ((cmd        << DOE_REG_DOE_CTRL_CMD_LOW    ) & DOE_REG_DOE_CTRL_CMD_MASK    ) |
        ((kv_dest    << DOE_REG_DOE_CTRL_DEST_LOW   ) & DOE_REG_DOE_CTRL_DEST_MASK   ) |
        (((cmd >> 2) << DOE_REG_DOE_CTRL_CMD_EXT_LOW) & DOE_REG_DOE_CTRL_CMD_EXT_MASK));
}

// Run a DOE flow and check the expected outcome.
//  expect_error == 0 : poll for VALID (write succeeded)
//  expect_error == 1 : poll for ERROR (write rejected by KV OCP-lock rule)
void doe_run(const enum doe_cmd_e cmd, uint32_t kv_dest, uint8_t expect_error) {
    VPRINTF(LOW, "DOE: cmd=%d dest=%d expect_error=%d\n", cmd, kv_dest, expect_error);
    doe_start(cmd, kv_dest);
    if (expect_error) {
        while ((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_ERROR_MASK) == 0);
        VPRINTF(LOW, "DOE: received expected error writing to OCP-lock slot %d\n", kv_dest);
    } else {
        while ((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_VALID_MASK) == 0);
        VPRINTF(LOW, "DOE: completed successfully to slot %d\n", kv_dest);
    }
}

void main() {
    VPRINTF(LOW,"------------------------------------------\n");
    VPRINTF(LOW," DOE Random Test (rand UDS/FE + rand OCP) \n");
    VPRINTF(LOW,"------------------------------------------\n");

    volatile uint8_t ocp_progress = 0;
    uint32_t fe_dest;
    uint32_t uds_dest;

    srand(time);

    // OCP lock is only meaningful when the mode is enabled in HW config.
    uint32_t ocp_lock_mode = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) &
                             SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK;
    VPRINTF(LOW, "OCP_LOCK_MODE_EN: 0x%x\n", ocp_lock_mode);

    if (ocp_lock_mode) {
        // Randomly decide whether to put OCP lock in progress this run so that
        // regression seeds cover both the positive and negative paths.
        ocp_progress = rand() % 2;
        if (ocp_progress) {
            VPRINTF(LOW, "OCP lock in progress\n");
            lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, 1);
        } else {
            VPRINTF(LOW, "OCP lock not in progress\n");
        }
    }

    if (ocp_progress) {
        // OCP lock in progress: a DOE write to the OCP-lock key-release slot
        // (KV23) must be rejected. Inject a random FE value, drive the FE flow
        // at KV23, and verify the DOE error is raised.
        SEND_STDOUT_CTRL(0xed); // TB service: inject random FE
        doe_run(DOE_FE, OCP_LOCK_KEY_RELEASE_KV_SLOT, /*expect_error=*/1);
    } else {
        // Not in progress (OCP lock disabled or idle): DOE may target any KV
        // slot. Inject random FE/UDS values and drive both flows to random
        // destinations (including KV23), expecting success.
        fe_dest  = rand() % NUM_KV_SLOTS;
        uds_dest = rand() % NUM_KV_SLOTS;

        SEND_STDOUT_CTRL(0xed); // TB service: inject random FE
        doe_run(DOE_FE, fe_dest, /*expect_error=*/0);

        SEND_STDOUT_CTRL(0xec); // TB service: inject random UDS
        doe_run(DOE_UDS, uds_dest, /*expect_error=*/0);
    }

    SEND_STDOUT_CTRL(0xff); // End the test
}
