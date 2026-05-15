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
// Description:
//   Verifies that the KV boot flow monitor is disabled when debug mode
//   is unlocked or scan mode is active.
//
//   Iter 0 (happy path + debug unlock setup):
//     - Complete correct DICE derivation
//     - Jump to FMC -- verify normal transition succeeds
//     - Issue debug unlock (TB cmd 0xfa) to set security_state
//     - Warm reset -- debug_locked=0 propagates via latch capture on reset deassert
//
//   Iter 1 (debug unlock bypass):
//     - System boots with debug_locked=0 (set in iter 0, latched on warm reset)
//     - Complete correct DICE derivation
//     - Jump to FMC
//     - Verify: no kv_fault fires (monitor is disabled in debug mode)
//     - Re-lock debug (TB cmd 0xf9) + warm reset
//
//   Iter 2 (scan mode bypass):
//     - System boots debug-locked (re-locked in iter 1)
//     - Complete correct DICE derivation
//     - Enter scan mode (TB cmd 0xb9) -- propagates via double-flop
//     - Jump to FMC
//     - Verify: no kv_fault fires (monitor is disabled in scan mode)
//     - Exit scan mode, declare pass

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "riscv_hw_if.h"
#include "kv_boot_flow.h"

volatile uint32_t* stdout = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Persistent iteration counter (survives warm reset in DCCM)
volatile uint32_t iter __attribute__((section(".dccm.persistent"))) = 0;

// FMC entry point placed in ICCM
extern uintptr_t iccm_code0_start, iccm_code0_end;
void fmc_entry(void) __attribute__((aligned(4), section(".data_iccm0")));

#define TB_CMD_DEBUG_UNLOCK   0xfa
#define TB_CMD_DEBUG_LOCK     0xf9
#define TB_CMD_SCAN_MODE_ON   0xb9
#define TB_CMD_SCAN_MODE_OFF  0xf0

#define NUM_ITERATIONS 3

// ============================================================
// FMC entry point -- runs from ICCM FMC region
// ============================================================
void fmc_entry(void) {
    uint32_t current_iter = iter - 1; // iter was incremented before jump

    VPRINTF(LOW, "FMC[%d]: Reached FMC entry point\n", current_iter);

    // The key check: no kv_fault should have fired
    check_no_kv_error("FMC");

    VPRINTF(LOW, "FMC[%d]: No kv fault -- pass\n", current_iter);

    switch (current_iter) {
        case 0:
            // Happy path done. Now set up debug unlock for iter 1.
            // Issue debug unlock -- TB sets security_state.debug_locked=0
            // after 100 cycle delay. Then warm reset propagates it.
            VPRINTF(LOW, "FMC[0]: Issuing debug unlock + warm reset\n");
            SEND_STDOUT_CTRL(TB_CMD_DEBUG_UNLOCK);
            // Wait for TB to set security_state.debug_locked=0
            for (volatile int i = 0; i < 200; i++) { __asm__ volatile("nop"); }
            SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
            while(1);

        case 1:
            // Debug bypass confirmed. Re-lock debug and warm reset for iter 2.
            VPRINTF(LOW, "FMC[1]: Debug bypass confirmed -- re-locking + warm reset\n");
            SEND_STDOUT_CTRL(TB_CMD_DEBUG_LOCK);
            for (volatile int i = 0; i < 50; i++) { __asm__ volatile("nop"); }
            SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
            while(1);

        case 2:
            // Scan mode bypass confirmed. Exit scan and pass.
            VPRINTF(LOW, "FMC[2]: Scan bypass confirmed -- exiting scan mode\n");
            SEND_STDOUT_CTRL(TB_CMD_SCAN_MODE_OFF);

            VPRINTF(LOW, "============================================\n");
            VPRINTF(LOW, " All debug/scan bypass tests passed\n");
            VPRINTF(LOW, "============================================\n");
            SEND_STDOUT_CTRL(0xff);
            while(1);
    }
}

void main() {
    uint32_t current_iter = iter;
    iter++;

    init_interrupts();

    // Enable boot flow monitoring (TB force -- in debug/scan mode this
    // has no effect since the RTL gate takes priority)
    SEND_STDOUT_CTRL(TB_CMD_ENABLE_KV_BOOT_FLOW_MONITOR);

    VPRINTF(LOW, "============================================\n");
    VPRINTF(LOW, " KV Debug/Scan Bypass Test -- iter %d\n", current_iter);
    VPRINTF(LOW, "============================================\n");

    if (current_iter >= NUM_ITERATIONS) {
        VPRINTF(FATAL, "[FAIL] Unexpected iteration %d\n", current_iter);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }

    // Clear any stale HW faults from previous iteration
    uint32_t hw_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
    if (hw_err) {
        VPRINTF(LOW, "  Clearing stale HW fault (0x%08x)\n", hw_err);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL, hw_err);
    }

    // --- ROM phase: Standard DICE derivation ---
    VPRINTF(LOW, "ROM[%d]: Populating DICE key slots...\n", current_iter);
    populate_dice_slots();

    // Copy FMC code to ICCM
    VPRINTF(LOW, "ROM[%d]: Copying FMC code to ICCM\n", current_iter);
    copy_to_iccm(FMC_ICCM_ADDR,
                  (uint32_t *)&iccm_code0_start,
                  (uint32_t *)&iccm_code0_end);

    // Program ICCM region registers
    program_iccm_regions();

    // Iter 2: enter scan mode before FMC jump
    if (current_iter == 2) {
        VPRINTF(LOW, "ROM[2]: Entering scan mode\n");
        SEND_STDOUT_CTRL(TB_CMD_SCAN_MODE_ON);
        // Wait for double-flop propagation
        for (volatile int i = 0; i < 200; i++) { __asm__ volatile("nop"); }
    }

    // Jump to FMC
    VPRINTF(LOW, "ROM[%d]: Jumping to FMC...\n", current_iter);
    void (*fmc_fn)(void) = (void (*)(void))FMC_ICCM_ADDR;
    fmc_fn();

    // Should not return
    VPRINTF(FATAL, "[FAIL] FMC returned to ROM\n");
    SEND_STDOUT_CTRL(0x01);
    while(1);
}
