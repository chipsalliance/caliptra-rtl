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
// kv_defines_pkg.sv). The DOE engine gates its KV write-rule check on the
// synth-time OCP-lock strap (ocp_lock_en == OCP_LOCK_MODE_EN), NOT on the
// SS_OCP_LOCK_CTRL "in progress" register -- see doe_fsm.sv, where
// kv_write_metrics.ocp_lock_in_progress is driven from ocp_lock_en. Therefore a
// DOE write targeting KV23 is rejected whenever OCP-lock mode is enabled,
// regardless of the in-progress bit. On a rejected write the DOE FSM stalls in
// DOE_WRITE (kv_write_allow==0, no offset advance), so the test must poll ERROR
// (never VALID) and then issue a cold reset to unstick the engine.
#define OCP_LOCK_KEY_RELEASE_KV_SLOT 23
// KV_NUM_KEYS from kv_defines_pkg.sv (slots 0..23).
#define NUM_KV_SLOTS                 24
// Non-OCP-lock destinations (slots 0..22) never trip the KV23 write rule.
#define NUM_NON_OCP_SLOTS            23

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Program DOE_CTRL with the given command and KV destination slot.
void doe_start(const enum doe_cmd_e cmd, uint32_t kv_dest) {
    lsu_write_32(CLP_DOE_REG_DOE_CTRL,
        ((cmd        << DOE_REG_DOE_CTRL_CMD_LOW    ) & DOE_REG_DOE_CTRL_CMD_MASK    ) |
        ((kv_dest    << DOE_REG_DOE_CTRL_DEST_LOW   ) & DOE_REG_DOE_CTRL_DEST_MASK   ) |
        (((cmd >> 2) << DOE_REG_DOE_CTRL_CMD_EXT_LOW) & DOE_REG_DOE_CTRL_CMD_EXT_MASK));
}

// Run a DOE flow and check the expected outcome.
//  expect_reject == 0 : poll for VALID (write succeeded)
//  expect_reject == 1 : poll for ERROR (write rejected by KV OCP-lock rule).
// Returns 1 if the write was rejected (caller must cold-reset the hung FSM).
uint8_t doe_run(const enum doe_cmd_e cmd, uint32_t kv_dest, uint8_t expect_reject) {
    VPRINTF(LOW, "DOE: cmd=%d dest=%d expect_reject=%d\n", cmd, kv_dest, expect_reject);
    doe_start(cmd, kv_dest);
    if (expect_reject) {
        while ((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_ERROR_MASK) == 0);
        VPRINTF(LOW, "DOE: received expected err (rejected) writing to OCP-lock slot %d\n", kv_dest);
        return 1;
    }
    while ((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_VALID_MASK) == 0);
    VPRINTF(LOW, "DOE: completed successfully to slot %d\n", kv_dest);
    return 0;
}

void main() {
    VPRINTF(LOW,"------------------------------------------\n");
    VPRINTF(LOW," DOE Random Test (rand UDS/FE + rand OCP) \n");
    VPRINTF(LOW,"------------------------------------------\n");

    init_interrupts();
    rst_count++;

    srand(time);

    // OCP lock is only meaningful when the mode strap is enabled in HW config.
    // This strap (not the in-progress register) is what the DOE engine checks.
    uint32_t ocp_lock_mode = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) &
                             SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK;
    VPRINTF(LOW, "OCP_LOCK_MODE_EN: 0x%x\n", ocp_lock_mode);

    // After a cold reset (issued to unstick a rejected/hung DOE FSM) just end.
    if (rst_count > 1) {
        VPRINTF(LOW, "DOE: post-reject cold reset observed (rst_count=%d), ending\n", rst_count);
        SEND_STDOUT_CTRL(0xff);
        return;
    }

    if (ocp_lock_mode) {
        // Randomly toggle the in-progress bit for coverage. Note this does NOT
        // change the DOE KV23 rejection (DOE uses the strap), but it exercises
        // the SS_OCP_LOCK_CTRL path and downstream consumers.
        if (rand() % 2) {
            VPRINTF(LOW, "OCP lock in progress\n");
            lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, 1);
        } else {
            VPRINTF(LOW, "OCP lock not in progress\n");
        }

        // Randomly choose to exercise the reject path or the success path.
        if (rand() % 2) {
            // Reject path: a DOE write to KV23 must be rejected while OCP-lock
            // mode is enabled. Inject a random FE value, drive FE at KV23,
            // verify the DOE error, then cold reset to unstick the FSM.
            SEND_STDOUT_CTRL(0xed); // TB service: inject random FE
            if (doe_run(DOE_FE, OCP_LOCK_KEY_RELEASE_KV_SLOT, /*expect_reject=*/1)) {
                SEND_STDOUT_CTRL(0xf5); // Cold reset to clear the hung DOE FSM
                return;
            }
        } else {
            // Success path: with mode enabled, restrict random dests to the
            // non-OCP-lock slots (0..22) so the write is not rejected.
            SEND_STDOUT_CTRL(0xed); // TB service: inject random FE
            doe_run(DOE_FE, rand() % NUM_NON_OCP_SLOTS, /*expect_reject=*/0);

            SEND_STDOUT_CTRL(0xec); // TB service: inject random UDS
            doe_run(DOE_UDS, rand() % NUM_NON_OCP_SLOTS, /*expect_reject=*/0);
        }
    } else {
        // OCP lock mode disabled: the KV23 rule never fires, so DOE may target
        // any KV slot. Inject random FE/UDS values to random destinations.
        SEND_STDOUT_CTRL(0xed); // TB service: inject random FE
        doe_run(DOE_FE, rand() % NUM_KV_SLOTS, /*expect_reject=*/0);

        SEND_STDOUT_CTRL(0xec); // TB service: inject random UDS
        doe_run(DOE_UDS, rand() % NUM_KV_SLOTS, /*expect_reject=*/0);
    }

    SEND_STDOUT_CTRL(0xff); // End the test
}
