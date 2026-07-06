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
// directed_fsm_glitch_inject.c
//
// Verifies that glitch injection into sparse-encoded FSMs causes
// CPTRA_HW_ERROR_FATAL.fsm_error to assert. The SOC BFM observes the
// fatal, sets GENERIC_INPUT_WIRES_0 = FSM_ERROR_OBSERVED, W1C clears
// the error register, and issues a warm reset. After reset, this test
// checks GENERIC_INPUT_WIRES_0 for the expected encoding.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>

volatile char* stdout = (char*)STDOUT;
volatile uint32_t intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Iteration counter -- persists across warm resets (DCCM not cleared)
volatile uint32_t iter __attribute__((section(".dccm.persistent"))) = 0;

// TB command: byte 0x95, WriteData[15:8] selects target FSM
// 0=DOE, 1=Boot, 2=Mbox, 3=SHA_acc
#define FSM_GLITCH_CMD      0x95
#define FSM_TARGET_DOE      0
#define FSM_TARGET_BOOT     1
#define FSM_TARGET_MBOX     2
#define FSM_TARGET_SHA_ACC  3

// Expected value on GENERIC_INPUT_WIRES_0 after BFM observes fsm_error
#define FSM_ERROR_OBSERVED  0xdead0f5e

#define NUM_FSMS 4

static const uint32_t fsm_targets[NUM_FSMS] = {
    FSM_TARGET_DOE,
    FSM_TARGET_SHA_ACC,
    FSM_TARGET_MBOX,
    FSM_TARGET_BOOT
};

static const char * const fsm_names[NUM_FSMS] = {
    "DOE",
    "SHA_ACC",
    "MBOX",
    "BOOT"
};

void trigger_fsm_glitch(uint32_t target) {
    uint32_t cmd = (target << 8) | FSM_GLITCH_CMD;
    *((volatile uint32_t *)STDOUT) = cmd;
    // TB will observe cptra_error_fatal, set generic_input_wires, W1C, and warm reset
    for (volatile int i = 0; i < 200; i++);
}

void main(void) {
    uint32_t current = iter++;

    VPRINTF(LOW, "-- directed_fsm_glitch_inject (iter %d) --\n", current);

    // Iterations 1..NUM_FSMS: check that BFM reported FSM_ERROR_OBSERVED from previous glitch
    if (current > 0 && current <= NUM_FSMS) {
        uint32_t resp = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);
        if (resp == FSM_ERROR_OBSERVED) {
            VPRINTF(LOW, "  [PASS] %s: BFM reported fsm fault (wires=0x%08x)\n",
                    fsm_names[current - 1], resp);
        } else {
            VPRINTF(FATAL, "  [FAIL] %s: expected 0x%08x got 0x%08x\n",
                    fsm_names[current - 1], FSM_ERROR_OBSERVED, resp);
            SEND_STDOUT_CTRL(0x01);
            while(1);
        }
    }

    // After all FSMs tested: done
    if (current >= NUM_FSMS) {
        VPRINTF(LOW, "\n-- All %d FSM glitch tests PASSED --\n", NUM_FSMS);
        SEND_STDOUT_CTRL(0xff);
        while(1);
    }

    // Trigger the glitch for this iteration's FSM
    VPRINTF(LOW, "  Triggering %s FSM glitch\n", fsm_names[current]);
    trigger_fsm_glitch(fsm_targets[current]);

    // Wait for TB to observe fatal and issue warm reset
    while(1);
}
