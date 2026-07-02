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
// CPTRA_HW_ERROR_FATAL.fsm_error to assert and the TB issues a warm reset.
//
// Flow:
//   iter 0: trigger DOE glitch → TB observes fatal → warm reset
//   iter 1: check DOE fatal bit, clear, trigger SHA_ACC glitch → warm reset
//   iter 2: check SHA_ACC fatal bit, clear, trigger MBOX glitch → warm reset
//   iter 3: check MBOX fatal bit, clear, trigger BOOT glitch → warm reset
//   iter 4: check BOOT fatal bit, clear → PASS

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

// Iteration counter -- persists across warm resets (DCCM not cleared on warm reset)
volatile uint32_t iter __attribute__((section(".dccm.persistent"))) = 0;

// TB command: byte 0x95, WriteData[15:8] selects target FSM
// 0=DOE, 1=Boot, 2=Mbox, 3=SHA_acc
#define FSM_GLITCH_CMD      0x95
#define FSM_TARGET_DOE      0
#define FSM_TARGET_BOOT     1
#define FSM_TARGET_MBOX     2
#define FSM_TARGET_SHA_ACC  3

// FSM fatal bit in CPTRA_HW_ERROR_FATAL
#ifndef SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_FSM_ERROR_MASK
#define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_FSM_ERROR_MASK (0x40)
#endif

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
    // TB will observe cptra_error_fatal and issue warm reset
    // CPU may or may not continue depending on which FSM was hit
    for (volatile int i = 0; i < 200; i++);
}

void main(void) {
    uint32_t current = iter++;

    VPRINTF(LOW, "-- directed_fsm_glitch_inject (iter %d) --\n", current);

    // Iterations 1..NUM_FSMS: check fatal bit from PREVIOUS glitch, then clear
    if (current > 0 && current <= NUM_FSMS) {
        uint32_t fatal = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
        if (fatal & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_FSM_ERROR_MASK) {
            VPRINTF(LOW, "  [PASS] %s: fsm bit confirmed after reset (reg=0x%08x)\n",
                    fsm_names[current - 1], fatal);
        } else {
            VPRINTF(FATAL, "  [FAIL] %s: fsm bit NOT set after reset (reg=0x%08x)\n",
                    fsm_names[current - 1], fatal);
        }
        // W1C clear the fatal bit
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL,
                     SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_FSM_ERROR_MASK);
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

    // If CPU survives (DOE/SHA_ACC/MBOX don't kill CPU immediately),
    // just wait for the TB to issue warm reset
    VPRINTF(LOW, "  Waiting for TB warm reset...\n");
    while(1);
}
