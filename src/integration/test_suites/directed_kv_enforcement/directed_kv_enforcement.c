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
//   Enforcement behavior test for KV boot flow transitions. Verifies that
//   enforcement actions (lock_wr, lock_use, slot clears, DOE lockdown)
//   actually prevent unintended operations:
//
//   FMC phase (after ROM-to-FMC):
//     1. lock_wr prevents overwrite of slot 0 (UDS) via HMAC write
//     2. Cleared slots (3,4,5,9) have dest_valid=0
//     3. ROM callback: FMC calls ROM-resident function, returns,
//        boot_flow_fmc doesn't re-trigger (no kv_error)
//     4. DOE lockdown rejects commands
//
//   RT phase (after FMC-to-RT):
//     5. lock_wr prevents overwrite of slot 4 (RT_CDI) via HMAC write
//     6. lock_use prevents reading slot 6 (FMC_CDI) as HMAC key
//     7. DOE lockdown still active

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "riscv_hw_if.h"
#include "hmac.h"
#include "kv_boot_flow.h"

volatile uint32_t* stdout = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// FMC function: placed in .data_iccm0 section, will be copied to FMC region
extern uintptr_t iccm_code0_start, iccm_code0_end;
void fmc_entry(void) __attribute__((aligned(4), section(".data_iccm0")));

// RT function: placed in .data_iccm1 section, will be copied to RT region
extern uintptr_t iccm_code1_start, iccm_code1_end;
void rt_entry(void) __attribute__((aligned(4), section(".data_iccm1")));

//
// Test: lock_wr prevents overwrite. Attempts to write a different dest_valid
// to a locked slot and verifies the original dest_valid is preserved.
//
void test_lock_wr_blocks_write(uint8_t slot, uint32_t expected_dv, const char *phase) {
    uint32_t ctrl_before = lsu_read_32(KV_KEY_CTRL(slot));
    uint32_t dv_before = (ctrl_before & KV_DEST_VALID_MASK) >> KV_DEST_VALID_LOW;

    VPRINTF(LOW, "  %s: Attempting HMAC write to locked slot %d (dest_valid=0x%03x)...\n",
            phase, slot, dv_before);

    // Write with a DIFFERENT dest_valid to detect if the write takes effect
    uint32_t poison_dv = (expected_dv == DV_HMAC_KEY) ? DV_AES_KEY : DV_HMAC_KEY;
    hmac_write_kv_slot(slot, poison_dv);

    // Check KV_WR_STATUS -- expect VALID=1 with possible error from lock_wr rejection
    uint32_t wr_status = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_STATUS);
    VPRINTF(LOW, "  %s: KV_WR_STATUS=0x%08x\n", phase, wr_status);

    // Read back and verify dest_valid is unchanged
    uint32_t ctrl_after = lsu_read_32(KV_KEY_CTRL(slot));
    uint32_t dv_after = (ctrl_after & KV_DEST_VALID_MASK) >> KV_DEST_VALID_LOW;

    if (dv_after != dv_before) {
        VPRINTF(ERROR, "[FAIL] %s: slot %d dest_valid changed! before=0x%03x after=0x%03x\n",
                phase, slot, dv_before, dv_after);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }

    // Zeroize HMAC to ensure clean state for subsequent operations
    hmac_zeroize();

    VPRINTF(LOW, "  %s: slot %d lock_wr blocked write (dest_valid=0x%03x unchanged) -- OK\n",
            phase, slot, dv_after);
}

//
// Test: lock_use prevents key read. Attempts to read a locked slot into
// HMAC key register and verifies the KV read status shows a fault.
//
void test_lock_use_blocks_read(uint8_t slot, const char *phase) {
    VPRINTF(LOW, "  %s: Attempting KV key read from lock_use'd slot %d...\n", phase, slot);

    // Trigger KV key read into HMAC engine
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL,
        HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
        ((slot << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) &
         HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

    // Poll for VALID or ERROR (matching library pattern from hmac.c line 70)
    uint32_t status;
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS) &
            (HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK |
             HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_MASK)) == 0) {
    }
    status = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS);

    // Check for read fault (error=non-zero indicates lock_use blocked the read)
    uint32_t err = (status & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_MASK)
                   >> HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_LOW;
    if (err == 0) {
        VPRINTF(ERROR, "[FAIL] %s: KV read from lock_use'd slot %d succeeded (status=0x%08x)\n",
                phase, slot, status);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }

    // Verify HMAC engine is still READY (KV read error should not start engine)
    uint32_t hmac_status = lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS);
    if (!(hmac_status & HMAC_REG_HMAC512_STATUS_READY_MASK)) {
        VPRINTF(ERROR, "[FAIL] %s: HMAC engine not ready after KV read fault\n", phase);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }

    // Zeroize HMAC to clear error state for subsequent operations
    hmac_zeroize();

    VPRINTF(LOW, "  %s: slot %d lock_use blocked read (err_code=0x%02x) -- OK\n", phase, slot, err);
}

//
// ROM-resident helper function for callback test.
// This lives in .text (ROM address space). When FMC calls this, the PC
// briefly leaves ICCM. The monitor must NOT re-trigger enter_fmc on return.
//
__attribute__((noinline))
uint32_t rom_callback_helper(uint32_t x) {
    return x + 1;
}

void main() {
    init_interrupts();

    // Enable boot flow monitoring
    SEND_STDOUT_CTRL(TB_CMD_ENABLE_KV_BOOT_FLOW_MONITOR);

    VPRINTF(LOW, "============================================\n");
    VPRINTF(LOW, " KV Enforcement Behavior Test\n");
    VPRINTF(LOW, "============================================\n");

    // --- ROM phase: Standard DICE derivation ---
    // Verify enforcement has NOT fired yet (slots unlocked during ROM)
    // This covers RFC item: "Enforcement fires on first FMC fetch"
    uint32_t rom_ctrl0 = lsu_read_32(KV_KEY_CTRL(KV_SLOT_SI_IDEV));
    if (rom_ctrl0 & KV_LOCK_WR_MASK) {
        VPRINTF(ERROR, "[FAIL] ROM: slot 0 lock_wr=1 before FMC jump -- premature enforcement!\n");
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "ROM: Pre-enforcement check -- slot 0 lock_wr=0 (no premature enforcement) -- OK\n");

    VPRINTF(LOW, "ROM: Populating DICE key slots...\n");
    populate_dice_slots();

    // Copy FMC and RT code to ICCM
    VPRINTF(LOW, "ROM: Copying FMC code to ICCM\n");
    copy_to_iccm(FMC_ICCM_ADDR,
                  (uint32_t *)&iccm_code0_start,
                  (uint32_t *)&iccm_code0_end);
    VPRINTF(LOW, "ROM: Copying RT code to ICCM\n");
    copy_to_iccm(RT_ICCM_ADDR,
                  (uint32_t *)&iccm_code1_start,
                  (uint32_t *)&iccm_code1_end);

    // Program ICCM region registers with 2-phase shadow protocol
    program_iccm_regions();

    // Jump to FMC -- triggers ROM-to-FMC enforcement
    VPRINTF(LOW, "ROM: Jumping to FMC...\n");
    void (*fmc_fn)(void) = (void (*)(void))FMC_ICCM_ADDR;
    fmc_fn();
}

// ============================================================
// FMC entry point -- runs from ICCM FMC region
// ============================================================
void fmc_entry(void) {
    VPRINTF(LOW, "FMC: Executing from ICCM FMC region\n");

    // Baseline: monitor passed at ROM-to-FMC
    check_no_kv_error("FMC");

    // --- Test 1: lock_wr prevents overwrite ---
    VPRINTF(LOW, "FMC: Test 1 -- lock_wr prevents overwrite\n");
    check_lock_wr(KV_SLOT_SI_IDEV, "FMC");
    test_lock_wr_blocks_write(KV_SLOT_SI_IDEV, DV_AES_KEY, "FMC");
    // Also verify no kv_error from the blocked write
    check_no_kv_error("FMC post-lock_wr");

    // --- Test 2: Cleared slots have dest_valid=0 ---
    VPRINTF(LOW, "FMC: Test 2 -- cleared slots inaccessible\n");
    check_slot_cleared(KV_SLOT_TMP, "FMC");
    check_slot_cleared(KV_SLOT_RT_CDI, "FMC");
    check_slot_cleared(KV_SLOT_RT_ECDSA, "FMC");
    check_slot_cleared(KV_SLOT_RT_MLDSA, "FMC");
    for (int i = 10; i < KV_NUM_KEYS; i++) {
        check_slot_cleared(i, "FMC");
    }

    // --- Test 3: ROM callback does not regress layer ---
    VPRINTF(LOW, "FMC: Test 3 -- ROM callback non-regression\n");
    volatile uint32_t result = rom_callback_helper(42);
    if (result != 43) {
        VPRINTF(ERROR, "[FAIL] ROM callback returned wrong value: %d\n", result);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    // The key check: PC went to ROM .text and back -- no kv_error should fire
    check_no_kv_error("FMC post-ROM-callback");
    VPRINTF(LOW, "  FMC: ROM callback returned correctly, no re-trigger -- OK\n");

    // --- Test 4: DOE lockdown ---
    VPRINTF(LOW, "FMC: Test 4 -- DOE lockdown\n");
    check_doe_locked("FMC");

    // Populate RT key slots (needed for FMC-to-RT transition)
    VPRINTF(LOW, "FMC: Populating RT key slots...\n");
    populate_rt_slots();

    // Jump to RT -- triggers FMC-to-RT enforcement
    VPRINTF(LOW, "FMC: Jumping to RT...\n");
    void (*rt_fn)(void) = (void (*)(void))RT_ICCM_ADDR;
    rt_fn();

    // Should not return
    VPRINTF(ERROR, "[FAIL] RT returned to FMC\n");
    SEND_STDOUT_CTRL(0x01);
    while(1);
}

// ============================================================
// RT entry point -- runs from ICCM RT region
// ============================================================
void rt_entry(void) {
    VPRINTF(LOW, "RT: Executing from ICCM RT region\n");

    // Baseline: monitor passed at FMC-to-RT
    check_no_kv_error("RT");

    // --- Test 5: lock_wr prevents RT slot overwrite ---
    // (Must run before lock_use test -- the KV_RD_KEY error from lock_use
    //  leaves the HMAC key-read client in a state that blocks new operations)
    VPRINTF(LOW, "RT: Test 5 -- lock_wr prevents RT slot overwrite\n");
    check_lock_wr(KV_SLOT_RT_CDI, "RT");
    test_lock_wr_blocks_write(KV_SLOT_RT_CDI, DV_CDI, "RT");
    check_no_kv_error("RT post-lock_wr");

    // --- Test 6: lock_use prevents FMC key access ---
    VPRINTF(LOW, "RT: Test 6 -- lock_use prevents FMC key read\n");
    check_lock_use(KV_SLOT_FMC_CDI, "RT");
    test_lock_use_blocks_read(KV_SLOT_FMC_CDI, "RT");
    // lock_use read failure should not cause kv_error (it's expected behavior)
    check_no_kv_error("RT post-lock_use");

    // --- Test 7: DOE still locked ---
    VPRINTF(LOW, "RT: Test 7 -- DOE lockdown persists\n");
    check_doe_locked("RT");

    // All tests passed
    VPRINTF(LOW, "============================================\n");
    VPRINTF(LOW, " All enforcement tests passed\n");
    VPRINTF(LOW, "============================================\n");
    SEND_STDOUT_CTRL(0xff);
}
