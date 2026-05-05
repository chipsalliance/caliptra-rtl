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
//   ICCM region register test for KV boot flow monitor, including shadow
//   register fault-hardening verification. The boot flow monitor is enabled
//   once on cold boot and remains active for all subsequent iterations.
//   Every iteration populates DICE key slots so the monitor can verify
//   dest_valid at transitions.
//
//   Shadow registers require a 2-phase write protocol: each address register
//   must be written twice with the same value before the shadow checker sets
//   its "committed" flag. The boot flow monitor's effective lock requires
//   BOTH the lock register AND all 4 shadow committed flags to be set.
//
//   Iter 0 (cold boot):
//     - Enable boot flow monitor (once, persists across resets)
//     - Populate DICE key slots, copy FMC/RT code to ICCM
//     - Program ICCM region registers (2-phase) and lock
//     - Verify lock blocks further address writes
//     - Jump to FMC -- monitor passes, FMC verifies lock blocks writes
//     - FMC populates RT slots, jumps to RT -- monitor passes
//     - RT issues warm reset
//
//   Iter 1 (warm reset):
//     - Verify all 4 address registers and lock reset to 0
//     - Re-populate DICE key slots (needed for monitor check)
//     - Reprogram regions (2-phase) and lock, run through FMC/RT normally
//     - RT issues firmware update reset
//
//   Iter 2 (fw update reset):
//     - Verify ICCM region registers and lock PERSIST (non-core domain)
//     - Shadow committed flags also persist (same reset domain)
//     - Verify lock still blocks writes
//     - Run through FMC/RT normally
//     - RT issues warm reset
//
//   Iter 3 (warm reset):
//     - Verify registers reset to 0
//     - Do NOT program regions or set lock
//     - Jump to ICCM -- boot_flow_error fires (ICCM fetch without lock)
//     - kv_error set, FMC confirms and issues warm reset
//
//   Iter 4 (warm reset):
//     - Set lock=1 WITHOUT programming addresses (all default to 0)
//     - Shadow committed=0 (no swmod fired) -> effective_lock=0
//     - Jump to ICCM -- boot_flow_error fires (fetch without effective lock)
//     - kv_error set, FMC confirms and issues warm reset
//
//   Iter 5 (warm reset):
//     - Write each address register ONCE only (shadow phase 0)
//     - Shadow staged captures ~value but committed stays 0
//     - Set lock=1, effective_lock still 0 (committed=0)
//     - Jump to ICCM -- boot_flow_error fires
//     - kv_error set, FMC confirms and issues warm reset
//
//   Iter 6 (warm reset):
//     - Write FMC_START with value A (phase 0), then different value B (phase 1)
//     - Shadow mismatch -> shadow_update_err fires in CPTRA_HW_ERROR_NON_FATAL
//     - Verify shadow_update_err, W1C clear it
//     - Set lock=1, committed still 0 (mismatch prevented commit)
//     - Jump to ICCM -- boot_flow_error fires
//     - kv_error set, FMC confirms and issues warm reset
//
//   Iter 7 (warm reset):
//     - Stale kv_error from iter 6 confirmed and cleared
//     - All scenarios passed

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "riscv_hw_if.h"

volatile uint32_t* stdout = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Iteration counter -- persists across warm and fw update resets
volatile uint32_t iter __attribute__((section(".dccm.persistent"))) = 0;

// FMC function: placed in .data_iccm0 section
extern uintptr_t iccm_code0_start, iccm_code0_end;
void fmc_entry(void) __attribute__((aligned(4), section(".data_iccm0")));

// RT function: placed in .data_iccm1 section
extern uintptr_t iccm_code1_start, iccm_code1_end;
void rt_entry(void) __attribute__((aligned(4), section(".data_iccm1")));

// ICCM region addresses (absolute)
#define FMC_ICCM_ADDR  RV_ICCM_SADR
#define RT_ICCM_ADDR   (RV_ICCM_SADR + 0x8000)

// ICCM region addresses (18-bit ICCM-relative, for region registers)
#define FMC_ICCM_START_REL 0x00000
#define FMC_ICCM_END_REL   0x07FFF
#define RT_ICCM_START_REL  0x08000
#define RT_ICCM_END_REL    0x3C7FF

// TB commands
#define TB_CMD_ENABLE_KV_BOOT_FLOW_MONITOR 0xbb
#define TB_CMD_WARM_RESET                  0xf6

#define NUM_ITERATIONS 7

// Shadow register error masks (bit positions from soc_ifc_external_reg.rdl)
// These will be in caliptra_reg.h once the C header is regenerated.
#define SHADOW_STORAGE_ERR_MASK (1 << 5)  // CPTRA_HW_ERROR_FATAL bit 5
#define SHADOW_UPDATE_ERR_MASK  (1 << 3)  // CPTRA_HW_ERROR_NON_FATAL bit 3

// KV slot assignments
#define KV_SLOT_SI_IDEV      0
#define KV_SLOT_SI_LDEV      1
#define KV_SLOT_KEY_LADDER   2
#define KV_SLOT_FMC_CDI      6
#define KV_SLOT_FMC_ECDSA    7
#define KV_SLOT_FMC_MLDSA    8
#define KV_SLOT_RT_CDI       4
#define KV_SLOT_RT_ECDSA     5
#define KV_SLOT_RT_MLDSA     9

// dest_valid bit masks
#define DV_HMAC_KEY    HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK
#define DV_MLDSA_SEED  HMAC_REG_HMAC512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK
#define DV_ECC_PKEY    HMAC_REG_HMAC512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK
#define DV_ECC_SEED    HMAC_REG_HMAC512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK
#define DV_AES_KEY     HMAC_REG_HMAC512_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK
#define DV_CDI         (DV_HMAC_KEY | DV_MLDSA_SEED | DV_ECC_SEED)

// Verify a register reads back a specific value
void check_reg(const char *name, uint32_t addr, uint32_t expected) {
    uint32_t val = lsu_read_32(addr);
    if (val != expected) {
        VPRINTF(ERROR, "[FAIL] %s: got=0x%08x expected=0x%08x\n", name, val, expected);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  CHECK OK: %s = 0x%08x\n", name, val);
}

// Program all 4 ICCM region registers with 2-phase shadow protocol and set the lock
void program_iccm_regions(void) {
    // Phase 0: first write (captured in shadow staged register)
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, FMC_ICCM_START_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR,   FMC_ICCM_END_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_START_ADDR,  RT_ICCM_START_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_END_ADDR,    RT_ICCM_END_REL);
    // Phase 1: second write (commits shadow registers)
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, FMC_ICCM_START_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR,   FMC_ICCM_END_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_START_ADDR,  RT_ICCM_START_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_END_ADDR,    RT_ICCM_END_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_REGION_LOCK,    0x1);
}

// Verify all region registers are zero (after warm reset)
void verify_regs_reset(void) {
    check_reg("FMC_START", CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, 0);
    check_reg("FMC_END",   CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR,   0);
    check_reg("RT_START",  CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_START_ADDR,  0);
    check_reg("RT_END",    CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_END_ADDR,    0);
    check_reg("LOCK",      CLP_SOC_IFC_REG_INTERNAL_ICCM_REGION_LOCK,    0);
}

// Verify region registers have the expected programmed values
void verify_regs_programmed(void) {
    check_reg("FMC_START", CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, FMC_ICCM_START_REL);
    check_reg("FMC_END",   CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR,   FMC_ICCM_END_REL);
    check_reg("RT_START",  CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_START_ADDR,  RT_ICCM_START_REL);
    check_reg("RT_END",    CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_END_ADDR,    RT_ICCM_END_REL);
    check_reg("LOCK",      CLP_SOC_IFC_REG_INTERNAL_ICCM_REGION_LOCK,    1);
}

// Verify kv_error is NOT set
void check_no_kv_error(const char *phase) {
    uint32_t hw_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
    if (hw_err & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK) {
        VPRINTF(ERROR, "[FAIL] %s: unexpected kv_error (0x%08x)\n", phase, hw_err);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
}

// Verify kv_error IS set and W1C clear it
void check_and_clear_kv_error(const char *phase) {
    uint32_t hw_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
    if (!(hw_err & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK)) {
        VPRINTF(ERROR, "[FAIL] %s: expected kv_error but got 0x%08x\n", phase, hw_err);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: kv_error confirmed (0x%08x) -- W1C clearing\n", phase, hw_err);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL,
                 SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK);
}

// Run a dummy HMAC384 and write result to a KV slot with given dest_valid
void hmac_write_kv_slot(uint8_t slot, uint32_t dest_valid_mask) {
    uint32_t *reg;

    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_KEY_0;
    for (int i = 0; i <= (CLP_HMAC_REG_HMAC512_KEY_11 - CLP_HMAC_REG_HMAC512_KEY_0) / 4; i++)
        lsu_write_32((uintptr_t)(reg + i), 0xDEADBE00 + i);

    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0;
    for (int i = 0; i <= (CLP_HMAC_REG_HMAC512_BLOCK_31 - CLP_HMAC_REG_HMAC512_BLOCK_0) / 4; i++)
        lsu_write_32((uintptr_t)(reg + i), 0xCAFE0000 + i);

    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_LFSR_SEED_0;
    for (int i = 0; i <= (CLP_HMAC_REG_HMAC512_LFSR_SEED_11 - CLP_HMAC_REG_HMAC512_LFSR_SEED_0) / 4; i++)
        lsu_write_32((uintptr_t)(reg + i), 0xA5A50000 + i);

    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL,
        HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
        ((slot << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
         HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK) |
        dest_valid_mask);

    cptra_intr_rcv.hmac_notif = 0;

    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL,
        HMAC_REG_HMAC512_CTRL_INIT_MASK |
        (HMAC384_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));

    while (cptra_intr_rcv.hmac_notif == 0) {
        __asm__ volatile ("wfi");
    }
}

// Populate all ROM-phase DICE key slots with correct dest_valid and write counts
void populate_dice_slots(void) {
    hmac_write_kv_slot(KV_SLOT_SI_IDEV,    DV_AES_KEY);
    hmac_write_kv_slot(KV_SLOT_SI_LDEV,    DV_AES_KEY);
    hmac_write_kv_slot(KV_SLOT_KEY_LADDER, DV_HMAC_KEY);
    // Slot 6: 4 writes (IDevID CDI, LDEV intermediate, LDEV CDI, FMC Alias CDI)
    hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);
    hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);
    hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED);
    hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_HMAC_KEY);
    hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);
    hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);
    hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED);
    hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);
}

// Populate RT-phase key slots (called from FMC)
void populate_rt_slots(void) {
    hmac_write_kv_slot(KV_SLOT_RT_CDI,   DV_CDI);
    hmac_write_kv_slot(KV_SLOT_RT_ECDSA, DV_ECC_PKEY);
    hmac_write_kv_slot(KV_SLOT_RT_MLDSA, DV_MLDSA_SEED);
}

// ============================================================
// FMC entry point
// ============================================================
void fmc_entry(void) {
    uint32_t current_iter = iter - 1;
    VPRINTF(LOW, "FMC[%d]: Entered\n", current_iter);

    if (current_iter == 0) {
        // Iter 0: Verify lock persists in FMC -- try to clear lock and overwrite address
        check_no_kv_error("FMC[0]");
        VPRINTF(LOW, "FMC[0]: Attempting to clear lock (should fail)\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_REGION_LOCK, 0x0);
        check_reg("LOCK after clear attempt", CLP_SOC_IFC_REG_INTERNAL_ICCM_REGION_LOCK, 1);

        VPRINTF(LOW, "FMC[0]: Attempting to overwrite FMC_START (should fail)\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, 0x3DEAD);
        check_reg("FMC_START after overwrite", CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, FMC_ICCM_START_REL);
    } else if (current_iter == 1 || current_iter == 2) {
        // Iters 1-2: Normal boot -- verify monitor passed
        check_no_kv_error("FMC[1-2]");
    } else if (current_iter == 3) {
        // Iter 3: Jumped to ICCM without lock -- boot_flow_error should have fired
        check_and_clear_kv_error("FMC[3] unlocked fetch");
        VPRINTF(LOW, "FMC[3]: boot_flow_error confirmed -- issuing warm reset\n");
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        while(1);
    } else if (current_iter == 4) {
        // Iter 4: Lock without addresses -- shadow committed=0 -> boot_flow_error
        check_and_clear_kv_error("FMC[4] no shadow commit");
        VPRINTF(LOW, "FMC[4]: boot_flow_error confirmed -- issuing warm reset\n");
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        while(1);
    } else if (current_iter == 5) {
        // Iter 5: Single-write shadow -- committed=0 -> boot_flow_error
        check_and_clear_kv_error("FMC[5] uncommitted shadow");
        VPRINTF(LOW, "FMC[5]: boot_flow_error confirmed -- issuing warm reset\n");
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        while(1);
    } else if (current_iter == 6) {
        // Iter 6: Mismatched shadow write -- committed=0 -> boot_flow_error
        check_and_clear_kv_error("FMC[6] mismatch shadow");
        VPRINTF(LOW, "FMC[6]: boot_flow_error confirmed -- issuing warm reset\n");
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        while(1);
    }

    // Populate RT key slots and jump to RT (iters 0, 1, 2 only)
    VPRINTF(LOW, "FMC[%d]: Populating RT slots\n", current_iter);
    populate_rt_slots();

    VPRINTF(LOW, "FMC[%d]: Jumping to RT\n", current_iter);
    void (*rt_fn)(void) = (void (*)(void))RT_ICCM_ADDR;
    rt_fn();
}

// ============================================================
// RT entry point
// ============================================================
void rt_entry(void) {
    uint32_t current_iter = iter - 1;
    VPRINTF(LOW, "RT[%d]: Entered\n", current_iter);

    if (current_iter == 0) {
        check_no_kv_error("RT[0]");
        VPRINTF(LOW, "RT[0]: Issuing warm reset\n");
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        while(1);
    } else if (current_iter == 1) {
        check_no_kv_error("RT[1]");
        VPRINTF(LOW, "RT[1]: Issuing FW update reset\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET,
                     SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK);
        while(1);
    } else if (current_iter == 2) {
        check_no_kv_error("RT[2]");
        VPRINTF(LOW, "RT[2]: Issuing warm reset\n");
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        while(1);
    }

    VPRINTF(ERROR, "[FAIL] RT: unexpected iter %d\n", current_iter);
    SEND_STDOUT_CTRL(0x01);
    while(1);
}

// ============================================================
// ROM entry point (main)
// ============================================================
void main() {
    init_interrupts();

    VPRINTF(LOW, "============================================\n");
    VPRINTF(LOW, " ICCM Region Register Test -- iter %d\n", iter);
    VPRINTF(LOW, "============================================\n");

    // Enable boot flow monitor once on cold boot (iter 0).
    // The monitor persists across all subsequent resets.
    if (iter == 0) {
        SEND_STDOUT_CTRL(TB_CMD_ENABLE_KV_BOOT_FLOW_MONITOR);
    }

    // Handle kv_error state from previous iterations.
    // CPTRA_HW_ERROR_FATAL persists across warm and fw update resets.
    uint32_t hw_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
    uint32_t has_stale_kv_error = hw_err & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK;

    if (iter <= 3) {
        // Iters 0-3: no kv_error expected from previous iteration
        if (has_stale_kv_error) {
            VPRINTF(ERROR, "[FAIL] iter %d: unexpected stale kv_error=0x%08x\n", iter, hw_err);
            SEND_STDOUT_CTRL(0x01);
            while(1);
        }
    } else {
        // Iters 4+: previous iteration produced deliberate kv_error
        if (!has_stale_kv_error) {
            VPRINTF(ERROR, "[FAIL] iter %d: expected stale kv_error but got 0x%08x\n", iter, hw_err);
            SEND_STDOUT_CTRL(0x01);
            while(1);
        }
        VPRINTF(LOW, "  Iter %d: stale kv_error confirmed (0x%08x) -- W1C clearing\n", iter, hw_err);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL,
                     SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK);
    }

    // Clear any stale shadow_update_err from a previous iteration
    {
        uint32_t nf_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL);
        if (nf_err & SHADOW_UPDATE_ERR_MASK) {
            VPRINTF(LOW, "  Iter %d: clearing stale shadow_update_err (NON_FATAL=0x%08x)\n", iter, nf_err);
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL, SHADOW_UPDATE_ERR_MASK);
        }
    }

    if (iter >= NUM_ITERATIONS) {
        VPRINTF(LOW, "============================================\n");
        VPRINTF(LOW, " All %d ICCM region test iterations passed\n", NUM_ITERATIONS);
        VPRINTF(LOW, "============================================\n");
        SEND_STDOUT_CTRL(0xff);
        return;
    }

    uint32_t current_iter = iter;
    iter++;

    switch (current_iter) {
    case 0:
        // ============================================================
        // Iter 0: Cold boot -- populate slots, program regions, lock
        // ============================================================
        VPRINTF(LOW, "ROM[0]: Copying FMC/RT code to ICCM\n");
        {
            uint32_t *fmc_dest = (uint32_t *)FMC_ICCM_ADDR;
            uint32_t *code_word = (uint32_t *)&iccm_code0_start;
            while (code_word < (uint32_t *)&iccm_code0_end)
                *fmc_dest++ = *code_word++;
            uint32_t *rt_dest = (uint32_t *)RT_ICCM_ADDR;
            code_word = (uint32_t *)&iccm_code1_start;
            while (code_word < (uint32_t *)&iccm_code1_end)
                *rt_dest++ = *code_word++;
        }

        VPRINTF(LOW, "ROM[0]: Populating DICE key slots\n");
        populate_dice_slots();

        VPRINTF(LOW, "ROM[0]: Programming ICCM regions\n");
        program_iccm_regions();
        verify_regs_programmed();

        VPRINTF(LOW, "ROM[0]: Attempting overwrite after lock\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR, 0x3FFFF);
        check_reg("FMC_END after locked overwrite", CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR, FMC_ICCM_END_REL);
        break;

    case 1:
        // ============================================================
        // Iter 1: Warm reset clears region registers -- reprogram
        // ============================================================
        VPRINTF(LOW, "ROM[1]: Verifying registers cleared by warm reset\n");
        verify_regs_reset();
        VPRINTF(LOW, "ROM[1]: Re-populating DICE key slots\n");
        populate_dice_slots();
        VPRINTF(LOW, "ROM[1]: Reprogramming ICCM regions\n");
        program_iccm_regions();
        break;

    case 2:
        // ============================================================
        // Iter 2: FW update reset preserves region registers
        // ============================================================
        VPRINTF(LOW, "ROM[2]: Verifying registers persist across FW update reset\n");
        verify_regs_programmed();
        VPRINTF(LOW, "ROM[2]: Verifying lock still blocks writes\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR, 0x3FFFF);
        check_reg("FMC_END after locked overwrite", CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR, FMC_ICCM_END_REL);
        // DICE keys persist across FW update reset -- no re-derivation needed
        break;

    case 3:
        // ============================================================
        // Iter 3: Jump to ICCM without lock -- expect boot_flow_error
        // ============================================================
        VPRINTF(LOW, "ROM[3]: Verifying registers cleared by warm reset\n");
        verify_regs_reset();
        // Populate DICE slots so monitor state is valid (boot_flow_error
        // fires independently from lock=0, before dest_valid is checked)
        VPRINTF(LOW, "ROM[3]: Populating DICE key slots\n");
        populate_dice_slots();
        VPRINTF(LOW, "ROM[3]: Jumping to ICCM WITHOUT lock -- expect boot_flow_error\n");
        break;

    case 4:
        // ============================================================
        // Iter 4: Lock WITHOUT programming addresses (all default 0)
        // No address register writes means shadow committed=0 for all.
        // effective_lock = lock(1) & committed(0) = 0.
        // Jump to ICCM -> boot_flow_error (fetch without effective lock).
        // ============================================================
        VPRINTF(LOW, "ROM[4]: Verifying registers cleared by warm reset\n");
        verify_regs_reset();
        VPRINTF(LOW, "ROM[4]: Populating DICE key slots\n");
        populate_dice_slots();
        VPRINTF(LOW, "ROM[4]: Setting lock without programming addresses\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_REGION_LOCK, 0x1);
        break;

    case 5:
        // ============================================================
        // Iter 5: Single-write shadow (no commit) + lock
        // Write each address register only once (phase 0 only).
        // Shadow staged register captures ~value but committed stays 0.
        // effective_lock = lock(1) & committed(0) = 0.
        // Jump to ICCM -> boot_flow_error (fetch without effective lock).
        // ============================================================
        VPRINTF(LOW, "ROM[5]: Verifying registers cleared by warm reset\n");
        verify_regs_reset();
        VPRINTF(LOW, "ROM[5]: Populating DICE key slots\n");
        populate_dice_slots();
        VPRINTF(LOW, "ROM[5]: Single-write shadow (phase 0 only, no commit)\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, FMC_ICCM_START_REL);
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR,   FMC_ICCM_END_REL);
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_START_ADDR,  RT_ICCM_START_REL);
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_END_ADDR,    RT_ICCM_END_REL);
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_REGION_LOCK,    0x1);
        break;

    case 6:
        // ============================================================
        // Iter 6: Mismatched 2-phase write -> shadow_update_err
        // Write FMC_START with value A (phase 0), then different value B
        // (phase 1 mismatch -> err_update -> CPTRA_HW_ERROR_NON_FATAL).
        // committed=0 because mismatch prevents commit.
        // Also verifies boot_flow_error fires (effective_lock=0).
        // ============================================================
        VPRINTF(LOW, "ROM[6]: Verifying registers cleared by warm reset\n");
        verify_regs_reset();
        VPRINTF(LOW, "ROM[6]: Populating DICE key slots\n");
        populate_dice_slots();
        VPRINTF(LOW, "ROM[6]: Mismatched shadow write on FMC_START\n");
        // Phase 0: write correct value
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, FMC_ICCM_START_REL);
        // Phase 1: write DIFFERENT value -> shadow_update_err
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, 0x3DEAD);
        // Verify shadow_update_err fired in NON_FATAL
        {
            uint32_t nf_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL);
            if (!(nf_err & SHADOW_UPDATE_ERR_MASK)) {
                VPRINTF(ERROR, "[FAIL] iter 6: shadow_update_err not set (NON_FATAL=0x%08x)\n", nf_err);
                SEND_STDOUT_CTRL(0x01);
                while(1);
            }
            VPRINTF(LOW, "  shadow_update_err confirmed (NON_FATAL=0x%08x)\n", nf_err);
            // W1C clear -- we've verified the fault detection works
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL, SHADOW_UPDATE_ERR_MASK);
        }
        // Set lock -- committed still 0 (mismatch prevented commit)
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_REGION_LOCK, 0x1);
        break;
    }

    // Jump to FMC
    VPRINTF(LOW, "ROM[%d]: Jumping to FMC\n", current_iter);
    void (*fmc_fn)(void) = (void (*)(void))FMC_ICCM_ADDR;
    fmc_fn();
}
