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
//   Fault/glitch injection test for KV boot flow enforcement.
//
//   Iter 0 (MuBi4 invalid encoding -- fail-safe verification):
//     - Complete correct DICE derivation + ICCM region setup
//     - Enable boot flow monitor
//     - TB forces boot_flow_fmc to invalid MuBi4 encoding (4'hA) for 5 clocks
//     - Verify: no kv_fault fires (strict check rejects invalid)
//     - Jump to FMC normally (real transition via ICCM fetch)
//     - Verify: no kv_fault (normal transition succeeds after glitch)
//     - Warm reset to advance
//
//   Iter 1 (shadow storage bit-flip -- detection + lockout):
//     - Program ICCM region registers (2-phase shadow commit)
//     - TB forces bit-flip inside fmc_start shadow register for 5 clocks
//     - Verify: CPTRA_HW_ERROR_FATAL.shadow_storage_err (bit 5) is set
//     - Verify: shadow write is locked out (committed value unchanged)
//     - Warm reset to advance (err_storage is permanent until reset)
//
//   Iter 2 (shadow storage recovery after warm reset):
//     - Warm reset cleared err_storage (shadow reg re-initialized)
//     - Verify: CPTRA_HW_ERROR_FATAL.shadow_storage_err still set (pwrgood-only reset)
//     - W1C clear the fatal bit -- now succeeds since err_storage is gone
//     - Declare pass

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

#define TB_CMD_MUBI4_GLITCH       0xbc
#define TB_CMD_SHADOW_FLIP        0xbe

#define NUM_ITERATIONS 3

// Small delay to allow TB force/release to propagate (auto-releases after 5 clocks)
static inline void tb_settle(void) {
    for (volatile int i = 0; i < 50; i++) { __asm__ volatile("nop"); }
}

// ============================================================
// FMC entry point -- runs from ICCM FMC region (iter 0 only)
// After invalid MuBi4 glitch was released, normal FMC transition
// should succeed without triggering kv_fault.
// ============================================================
void fmc_entry(void) {
    VPRINTF(LOW, "FMC[0]: Reached FMC after MuBi4 glitch recovery\n");

    check_no_kv_error("FMC post-glitch");

    VPRINTF(LOW, "FMC[0]: Glitch fail-safe confirmed -- warm reset\n");
    SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
    while(1);
}

void main() {
    uint32_t current_iter = iter;
    iter++;

    init_interrupts();

    VPRINTF(LOW, "============================================\n");
    VPRINTF(LOW, " KV Glitch Injection Test -- iter %d\n", current_iter);
    VPRINTF(LOW, "============================================\n");

    if (current_iter >= NUM_ITERATIONS) {
        VPRINTF(FATAL, "[FAIL] Unexpected iteration %d\n", current_iter);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }

    // Clear any stale HW faults (skip for iter 2 -- it checks persistence)
    uint32_t hw_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
    if (hw_err && current_iter != 2) {
        VPRINTF(LOW, "  Clearing stale HW fault (0x%08x)\n", hw_err);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL, hw_err);
    }

    switch (current_iter) {
        case 0: {
            // ========================================================
            // Iter 0: MuBi4 invalid encoding fail-safe test
            // Needs full boot flow: DICE derivation + ICCM + monitor.
            // Force lasts 5 clocks then auto-releases in TB.
            // ========================================================

            // Standard DICE derivation
            VPRINTF(LOW, "ROM[0]: Populating DICE key slots...\n");
            populate_dice_slots();

            // Copy FMC code to ICCM
            VPRINTF(LOW, "ROM[0]: Copying FMC code to ICCM\n");
            copy_to_iccm(FMC_ICCM_ADDR,
                          (uint32_t *)&iccm_code0_start,
                          (uint32_t *)&iccm_code0_end);

            // Program ICCM region registers
            program_iccm_regions();

            // Enable boot flow monitoring
            SEND_STDOUT_CTRL(TB_CMD_ENABLE_KV_BOOT_FLOW_MONITOR);

            VPRINTF(LOW, "ROM[0]: Injecting MuBi4 glitch on boot_flow_fmc\n");
            SEND_STDOUT_CTRL(TB_CMD_MUBI4_GLITCH);
            tb_settle(); // Wait for force + auto-release

            // Verify: invalid encoding does NOT trigger kv_fault
            check_no_kv_error("MuBi4 glitch");
            VPRINTF(LOW, "ROM[0]: No spurious fault from invalid MuBi4 (fail-safe OK)\n");

            // Normal FMC jump -- real transition should succeed
            VPRINTF(LOW, "ROM[0]: Jumping to FMC (normal transition)...\n");
            void (*fmc_fn)(void) = (void (*)(void))FMC_ICCM_ADDR;
            fmc_fn();

            // Should not return
            VPRINTF(FATAL, "[FAIL] FMC returned to ROM\n");
            SEND_STDOUT_CTRL(0x01);
            while(1);
        }

        case 1: {
            // ========================================================
            // Iter 1: Shadow storage bit-flip detection test
            // No boot flow monitor needed -- just ICCM shadow regs.
            // The forced bit-flip corrupts the shadow flop permanently
            // (err_storage is combinational: ~shadow_q != committed_q).
            // This is by design -- recovery requires reset.
            //
            // Uses commit_iccm_shadows() (no lock) so write attempts
            // during err_storage produce we=1 (coverage: write×err_storage).
            // ========================================================

            // Commit shadow values (2-phase) without locking
            commit_iccm_shadows();

            // Save the committed value before injection
            uint32_t orig_val = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR);
            VPRINTF(LOW, "ROM[1]: fmc_start before injection: 0x%08x\n", orig_val);

            // Inject shadow bit-flip (auto-releases after 5 clocks,
            // but the flop retains the corrupted value permanently)
            VPRINTF(LOW, "ROM[1]: Injecting shadow storage bit-flip\n");
            SEND_STDOUT_CTRL(TB_CMD_SHADOW_FLIP);
            tb_settle();

            // Verify: shadow_storage_err (bit 5) set in HW_ERROR_FATAL
            hw_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
            if (!(hw_err & SHADOW_STORAGE_ERR_MASK)) {
                VPRINTF(FATAL, "[FAIL] shadow_storage_err not set "
                        "(hw_fatal=0x%08x)\n", hw_err);
                SEND_STDOUT_CTRL(0x01);
                while(1);
            }
            VPRINTF(LOW, "ROM[1]: shadow_storage_err detected (hw_fatal=0x%08x)\n", hw_err);

            // Attempt write -- should be locked out by err_storage
            uint32_t new_val = orig_val ^ 0x100;
            lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, new_val);
            lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, new_val);
            tb_settle();

            uint32_t readback = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR);
            if (readback != orig_val) {
                VPRINTF(FATAL, "[FAIL] Shadow write succeeded during "
                        "err_storage (got 0x%08x, expected 0x%08x)\n",
                        readback, orig_val);
                SEND_STDOUT_CTRL(0x01);
                while(1);
            }
            VPRINTF(LOW, "ROM[1]: Write correctly rejected during err_storage\n");

            // Warm reset -- clears err_storage (shadow re-inits) but
            // CPTRA_HW_ERROR_FATAL persists (pwrgood-only reset domain)
            VPRINTF(LOW, "ROM[1]: Issuing warm reset for recovery check\n");
            SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
            while(1);
        }

        case 2: {
            // ========================================================
            // Iter 2: Verify recovery after warm reset
            // Shadow regs re-initialized, err_storage cleared.
            // Fatal bit should still be set (survives warm reset).
            // W1C should now succeed since HW is no longer driving it.
            // ========================================================

            // Verify fatal bit persisted across warm reset
            hw_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
            if (!(hw_err & SHADOW_STORAGE_ERR_MASK)) {
                VPRINTF(FATAL, "[FAIL] shadow_storage_err did not persist "
                        "across warm reset (hw_fatal=0x%08x)\n", hw_err);
                SEND_STDOUT_CTRL(0x01);
                while(1);
            }
            VPRINTF(LOW, "ROM[2]: shadow_storage_err persisted (hw_fatal=0x%08x)\n", hw_err);

            // W1C clear -- should succeed now that err_storage is gone
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL, SHADOW_STORAGE_ERR_MASK);
            hw_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
            if (hw_err & SHADOW_STORAGE_ERR_MASK) {
                VPRINTF(FATAL, "[FAIL] W1C did not clear shadow_storage_err "
                        "(hw_fatal=0x%08x)\n", hw_err);
                SEND_STDOUT_CTRL(0x01);
                while(1);
            }
            VPRINTF(LOW, "ROM[2]: W1C cleared shadow_storage_err after warm reset\n");

            VPRINTF(LOW, "============================================\n");
            VPRINTF(LOW, " All glitch injection tests passed\n");
            VPRINTF(LOW, "============================================\n");
            SEND_STDOUT_CTRL(0xff);
            while(1);
        }
    }
}
