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
//   Smoke test for KV boot flow monitor. Validates that the boot phase
//   transition detection and KV monitor pass on the happy path through
//   three boot cycles (cold boot, warm reset, fw update reset):
//
//   Boot 0 (cold boot):
//     1. Enable boot flow monitoring via TB service command (0xbb)
//     2. Populate KV slots with correct dest_valid (mimic ROM DICE derivation)
//     3. Copy FMC/RT functions to ICCM
//     4. Jump to FMC (triggers ROM-to-FMC -- monitor checks dest_valid)
//     5. FMC populates RT key slots, jumps to RT (triggers FMC-to-RT)
//     6. RT validates enforcement, issues warm reset
//
//   Boot 1 (warm reset):
//     7. ROM detects warm reset, re-derives all DICE keys (KV slots persist
//        but enforcement requires fresh derivation with correct write counts)
//     8. ICCM code persists -- re-copy for safety, re-program region regs
//     9. Jump to FMC -- monitor checks dest_valid again
//    10. FMC re-derives RT keys, jumps to RT
//    11. RT validates enforcement, issues firmware update reset
//
//   Boot 2 (fw update reset):
//    12. ROM detects fw update reset, skips key derivation (keys persist)
//    13. ICCM code persists -- jump directly to FMC
//    14. FMC re-derives RT keys, jumps to RT
//    15. RT validates enforcement again, test ends with success

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

// Boot counter -- persists across fw update reset (DCCM not cleared)
volatile uint32_t boot_count __attribute__((section(".dccm.persistent"))) = 0;

// FMC function: placed in .data_iccm0 section, will be copied to FMC region (0x40000000)
extern uintptr_t iccm_code0_start, iccm_code0_end;
void fmc_entry(void) __attribute__((aligned(4), section(".data_iccm0")));

// RT function: placed in .data_iccm1 section, will be copied to RT region (0x40008000)
extern uintptr_t iccm_code1_start, iccm_code1_end;
void rt_entry(void) __attribute__((aligned(4), section(".data_iccm1")));

void main() {
    // Initialize interrupts (needed after every reset)
    init_interrupts();

    // Enable boot flow monitoring via TB service (needed after every reset)
    SEND_STDOUT_CTRL(TB_CMD_ENABLE_KV_BOOT_FLOW_MONITOR);

    uint32_t reset_reason = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_RESET_REASON);
    uint32_t is_fw_update = reset_reason & SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_MASK;
    uint32_t is_warm      = reset_reason & SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK;

    if (!is_fw_update && !is_warm) {
        // ============================================================
        // Boot 0: Cold boot -- full DICE derivation
        // ============================================================
        boot_count = 0;
        VPRINTF(LOW, "============================================\n");
        VPRINTF(LOW, " Boot 0: Cold Boot\n");
        VPRINTF(LOW, "============================================\n");

        VPRINTF(LOW, "ROM: Populating DICE key slots...\n");
        populate_dice_slots();

        // Copy FMC and RT code to ICCM
        VPRINTF(LOW, "ROM: Copying FMC code to 0x%x\n", FMC_ICCM_ADDR);
        copy_to_iccm(FMC_ICCM_ADDR,
                      (uint32_t *)&iccm_code0_start,
                      (uint32_t *)&iccm_code0_end);
        VPRINTF(LOW, "ROM: Copying RT code to 0x%x\n", RT_ICCM_ADDR);
        copy_to_iccm(RT_ICCM_ADDR,
                      (uint32_t *)&iccm_code1_start,
                      (uint32_t *)&iccm_code1_end);
    } else if (is_warm) {
        // ============================================================
        // Boot 1: Warm reset -- full DICE re-derivation required
        // ============================================================
        boot_count = 1;
        VPRINTF(LOW, "============================================\n");
        VPRINTF(LOW, " Boot 1: Warm Reset\n");
        VPRINTF(LOW, "============================================\n");

        VPRINTF(LOW, "ROM: Warm reset -- re-deriving DICE keys...\n");
        populate_dice_slots();

        // ICCM content persists across warm reset -- re-copy for safety
        VPRINTF(LOW, "ROM: Re-copying FMC code to ICCM\n");
        copy_to_iccm(FMC_ICCM_ADDR,
                      (uint32_t *)&iccm_code0_start,
                      (uint32_t *)&iccm_code0_end);
        VPRINTF(LOW, "ROM: Re-copying RT code to ICCM\n");
        copy_to_iccm(RT_ICCM_ADDR,
                      (uint32_t *)&iccm_code1_start,
                      (uint32_t *)&iccm_code1_end);
    } else {
        // ============================================================
        // Boot 2: Firmware update reset -- keys persist, skip derivation
        // ============================================================
        boot_count = 2;
        VPRINTF(LOW, "============================================\n");
        VPRINTF(LOW, " Boot 2: FW Update Reset\n");
        VPRINTF(LOW, "============================================\n");

        // Keys persist across fw update reset (dest_valid resets on hard_reset_b only)
        // lock_wr/lock_use were cleared by reset -- enforcement will re-apply
        // ICCM content persists -- no need to re-copy FMC/RT
        VPRINTF(LOW, "ROM: FW update reset detected, skipping key derivation\n");
    }

    // Program ICCM region registers with 2-phase shadow protocol
    VPRINTF(LOW, "ROM: Programming ICCM region registers\n");
    program_iccm_regions();

    // Jump to FMC (triggers ROM-to-FMC transition)
    VPRINTF(LOW, "ROM: Jumping to FMC at 0x%x...\n", FMC_ICCM_ADDR);
    void (*fmc_fn)(void) = (void (*)(void))FMC_ICCM_ADDR;
    fmc_fn();
}

// Simulated FMC entry point - runs from ICCM FMC region (VMA = 0x40000000)
void fmc_entry(void) {
    const char *bp;
    if (boot_count == 0) bp = "FMC[0]";
    else if (boot_count == 1) bp = "FMC[1]";
    else bp = "FMC[2]";
    VPRINTF(LOW, "%s: Executing from ICCM FMC region\n", bp);

    // --- FMC-phase validation (post ROM-to-FMC transition) ---

    // kv_error should NOT be set (monitor passed at ROM-to-FMC)
    check_no_kv_error(bp);

    // lock_wr set on ROM-phase preserved slots (0,1,2,6,7,8)
    VPRINTF(LOW, "%s: Checking lock_wr on ROM-phase slots...\n", bp);
    check_lock_wr(KV_SLOT_SI_IDEV, bp);
    check_lock_wr(KV_SLOT_SI_LDEV, bp);
    check_lock_wr(KV_SLOT_KEY_LADDER, bp);
    check_lock_wr(KV_SLOT_FMC_CDI, bp);
    check_lock_wr(KV_SLOT_FMC_ECDSA, bp);
    check_lock_wr(KV_SLOT_FMC_MLDSA, bp);

    // Non-preserved slots cleared at ROM-to-FMC (3,4,5,9,10-15)
    VPRINTF(LOW, "%s: Checking non-preserved slots cleared...\n", bp);
    check_slot_cleared(KV_SLOT_TMP, bp);
    check_slot_cleared(KV_SLOT_RT_CDI, bp);
    check_slot_cleared(KV_SLOT_RT_ECDSA, bp);
    check_slot_cleared(KV_SLOT_RT_MLDSA, bp);
    for (int i = 10; i < KV_NUM_KEYS; i++) {
        check_slot_cleared(i, bp);
    }

    // DOE is locked
    VPRINTF(LOW, "%s: Checking DOE lockdown...\n", bp);
    check_doe_locked(bp);

    // Mimic FMC DICE derivation -- populate RT key slots
    VPRINTF(LOW, "%s: Populating RT key slots...\n", bp);
    populate_rt_slots();

    // Jump to RT (triggers FMC-to-RT transition)
    VPRINTF(LOW, "%s: Jumping to RT at 0x%x...\n", bp, RT_ICCM_ADDR);
    void (*rt_fn)(void) = (void (*)(void))RT_ICCM_ADDR;
    rt_fn();
}

// Simulated RT entry point - runs from ICCM RT region (VMA = 0x40008000)
void rt_entry(void) {
    const char *bp;
    if (boot_count == 0) bp = "RT[0]";
    else if (boot_count == 1) bp = "RT[1]";
    else bp = "RT[2]";
    VPRINTF(LOW, "%s: Executing from ICCM RT region\n", bp);

    // --- RT-phase validation (post FMC-to-RT transition) ---

    // kv_error should NOT be set (monitor passed at FMC-to-RT)
    check_no_kv_error(bp);

    // lock_wr set on RT-phase slots (4,5,9)
    VPRINTF(LOW, "%s: Checking lock_wr on RT-phase slots...\n", bp);
    check_lock_wr(KV_SLOT_RT_CDI, bp);
    check_lock_wr(KV_SLOT_RT_ECDSA, bp);
    check_lock_wr(KV_SLOT_RT_MLDSA, bp);

    // lock_use set on FMC-phase slots (6,7,8)
    VPRINTF(LOW, "%s: Checking lock_use on FMC-phase slots...\n", bp);
    check_lock_use(KV_SLOT_FMC_CDI, bp);
    check_lock_use(KV_SLOT_FMC_ECDSA, bp);
    check_lock_use(KV_SLOT_FMC_MLDSA, bp);

    // Non-preserved slots cleared at FMC-to-RT (3,10-15)
    VPRINTF(LOW, "%s: Checking non-preserved slots cleared...\n", bp);
    check_slot_cleared(KV_SLOT_TMP, bp);
    for (int i = 10; i < KV_NUM_KEYS; i++) {
        check_slot_cleared(i, bp);
    }

    // DOE still locked
    VPRINTF(LOW, "%s: Checking DOE still locked...\n", bp);
    check_doe_locked(bp);

    if (boot_count == 0) {
        // Boot 0: Issue warm reset -- will re-enter main()
        VPRINTF(LOW, "%s: Boot 0 checks passed, issuing warm reset...\n", bp);
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        // Should not reach here -- reset takes effect
        VPRINTF(ERROR, "[FAIL] Warm reset did not take effect!\n");
        SEND_STDOUT_CTRL(0x01);
        while(1);
    } else if (boot_count == 1) {
        // Boot 1: Issue firmware update reset -- will re-enter main()
        VPRINTF(LOW, "%s: Boot 1 checks passed, issuing FW update reset...\n", bp);
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET,
                     SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK);
        // Should not reach here -- reset takes effect
        VPRINTF(ERROR, "[FAIL] FW update reset did not take effect!\n");
        SEND_STDOUT_CTRL(0x01);
        while(1);
    } else {
        // Boot 2: All checks passed across all three boot cycles
        VPRINTF(LOW, "============================================\n");
        VPRINTF(LOW, " All checks passed -- cold + warm + fw update\n");
        VPRINTF(LOW, "============================================\n");
        SEND_STDOUT_CTRL(0xff);
    }
}
