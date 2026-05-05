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

// ICCM region addresses (absolute)
#define FMC_ICCM_ADDR  RV_ICCM_SADR            // 0x40000000
#define RT_ICCM_ADDR   (RV_ICCM_SADR + 0x8000) // 0x40008000

// ICCM region addresses (18-bit ICCM-relative, for region registers)
#define FMC_ICCM_START_REL 0x00000
#define FMC_ICCM_END_REL   0x07FFF
#define RT_ICCM_START_REL  0x08000
#define RT_ICCM_END_REL    0x3C7FF

// TB command to enable KV boot flow monitoring
#define TB_CMD_ENABLE_KV_BOOT_FLOW_MONITOR 0xa1

// KV KEY_CTRL register access helpers
#define KV_KEY_CTRL(slot) (CLP_KV_REG_KEY_CTRL_0 + ((slot) * 4))
#define KV_LOCK_WR_MASK   KV_REG_KEY_CTRL_0_LOCK_WR_MASK
#define KV_LOCK_USE_MASK  KV_REG_KEY_CTRL_0_LOCK_USE_MASK
#define KV_DEST_VALID_MASK KV_REG_KEY_CTRL_0_DEST_VALID_MASK
#define KV_DEST_VALID_LOW  KV_REG_KEY_CTRL_0_DEST_VALID_LOW

// KV slot assignments
#define KV_SLOT_SI_IDEV      0
#define KV_SLOT_SI_LDEV      1
#define KV_SLOT_KEY_LADDER   2
#define KV_SLOT_TMP          3
#define KV_SLOT_RT_CDI       4
#define KV_SLOT_RT_ECDSA     5
#define KV_SLOT_FMC_CDI      6
#define KV_SLOT_FMC_ECDSA    7
#define KV_SLOT_FMC_MLDSA    8
#define KV_SLOT_RT_MLDSA     9

// dest_valid bit masks
#define DV_HMAC_KEY    HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK
#define DV_MLDSA_SEED  HMAC_REG_HMAC512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK
#define DV_ECC_PKEY    HMAC_REG_HMAC512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK
#define DV_ECC_SEED    HMAC_REG_HMAC512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK
#define DV_AES_KEY     HMAC_REG_HMAC512_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK
#define DV_CDI         (DV_HMAC_KEY | DV_MLDSA_SEED | DV_ECC_SEED)

// Number of KV entries
#define KV_NUM_KEYS 16

//
// Verify that CPTRA_HW_ERROR_FATAL.kv_error is NOT set
//
void check_no_kv_error(const char *phase) {
    uint32_t hw_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
    if (hw_err & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK) {
        VPRINTF(ERROR, "[FAIL] %s: kv_error=1 (reg=0x%08x)\n", phase, hw_err);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: kv_error=0 -- OK\n", phase);
}

//
// Verify lock_wr is set on the given slot
//
void check_lock_wr(uint8_t slot, const char *phase) {
    uint32_t ctrl = lsu_read_32(KV_KEY_CTRL(slot));
    if (!(ctrl & KV_LOCK_WR_MASK)) {
        VPRINTF(ERROR, "[FAIL] %s: slot %d lock_wr not set (ctrl=0x%08x)\n", phase, slot, ctrl);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: slot %d lock_wr=1 -- OK\n", phase, slot);
}

//
// Verify lock_use is set on the given slot
//
void check_lock_use(uint8_t slot, const char *phase) {
    uint32_t ctrl = lsu_read_32(KV_KEY_CTRL(slot));
    if (!(ctrl & KV_LOCK_USE_MASK)) {
        VPRINTF(ERROR, "[FAIL] %s: slot %d lock_use not set (ctrl=0x%08x)\n", phase, slot, ctrl);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: slot %d lock_use=1 -- OK\n", phase, slot);
}

//
// Verify a slot was cleared (dest_valid == 0)
//
void check_slot_cleared(uint8_t slot, const char *phase) {
    uint32_t ctrl = lsu_read_32(KV_KEY_CTRL(slot));
    uint32_t dv = (ctrl & KV_DEST_VALID_MASK) >> KV_DEST_VALID_LOW;
    if (dv != 0) {
        VPRINTF(ERROR, "[FAIL] %s: slot %d not cleared (dest_valid=0x%03x)\n", phase, slot, dv);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: slot %d cleared (dest_valid=0) -- OK\n", phase, slot);
}

//
// Verify DOE is locked: write a command and confirm it doesn't execute
//
void check_doe_locked(const char *phase) {
    lsu_write_32(CLP_DOE_REG_DOE_CTRL,
                 (1 << DOE_REG_DOE_CTRL_CMD_LOW) |
                 (0 << DOE_REG_DOE_CTRL_DEST_LOW));
    uint32_t status = lsu_read_32(CLP_DOE_REG_DOE_STATUS);
    if (!(status & DOE_REG_DOE_STATUS_READY_MASK)) {
        VPRINTF(ERROR, "[FAIL] %s: DOE went busy after locked cmd\n", phase);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    if (status & DOE_REG_DOE_STATUS_VALID_MASK) {
        VPRINTF(ERROR, "[FAIL] %s: DOE produced result after locked cmd\n", phase);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    uint32_t ctrl = lsu_read_32(CLP_DOE_REG_DOE_CTRL);
    if (ctrl & DOE_REG_DOE_CTRL_CMD_MASK) {
        VPRINTF(ERROR, "[FAIL] %s: DOE cmd not cleared by hwclr\n", phase);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: DOE cmd rejected (ready=1 valid=0 cmd=0) -- OK\n", phase);
}

//
// Run a dummy HMAC384 operation and write the result to a KV slot.
// Waits for either hmac_notif or hmac_error (matching library pattern).
//
void hmac_write_kv_slot(uint8_t slot, uint32_t dest_valid_mask) {
    uint32_t *reg;

    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_KEY_0;
    for (int i = 0; i <= (CLP_HMAC_REG_HMAC512_KEY_11 - CLP_HMAC_REG_HMAC512_KEY_0) / 4; i++) {
        lsu_write_32((uintptr_t)(reg + i), 0xDEADBE00 + i);
    }

    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0;
    for (int i = 0; i <= (CLP_HMAC_REG_HMAC512_BLOCK_31 - CLP_HMAC_REG_HMAC512_BLOCK_0) / 4; i++) {
        lsu_write_32((uintptr_t)(reg + i), 0xCAFE0000 + i);
    }

    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_LFSR_SEED_0;
    for (int i = 0; i <= (CLP_HMAC_REG_HMAC512_LFSR_SEED_11 - CLP_HMAC_REG_HMAC512_LFSR_SEED_0) / 4; i++) {
        lsu_write_32((uintptr_t)(reg + i), 0xA5A50000 + i);
    }

    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL,
        HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
        ((slot << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
         HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK) |
        dest_valid_mask);

    cptra_intr_rcv.hmac_notif = 0;
    cptra_intr_rcv.hmac_error = 0;

    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL,
        HMAC_REG_HMAC512_CTRL_INIT_MASK |
        (HMAC384_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));

    // Wait for either notif (success) or error (KV write rejected)
    while ((cptra_intr_rcv.hmac_notif == 0) && (cptra_intr_rcv.hmac_error == 0)) {
        __asm__ volatile ("wfi");
    }
}

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

    VPRINTF(LOW, "  %s: slot %d lock_use blocked read (error=0x%02x) -- OK\n", phase, slot, err);
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
    hmac_write_kv_slot(KV_SLOT_SI_IDEV,    DV_AES_KEY);
    hmac_write_kv_slot(KV_SLOT_SI_LDEV,    DV_AES_KEY);
    hmac_write_kv_slot(KV_SLOT_KEY_LADDER, DV_HMAC_KEY);
    // Slot 6: 4 writes
    hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);
    hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);
    hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED);
    hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_HMAC_KEY);
    hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);
    hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);
    hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED);
    hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);

    // Copy FMC and RT code to ICCM
    uint32_t *fmc_dest = (uint32_t *)FMC_ICCM_ADDR;
    uint32_t *code_word = (uint32_t *)&iccm_code0_start;
    VPRINTF(LOW, "ROM: Copying FMC code to ICCM\n");
    while (code_word < (uint32_t *)&iccm_code0_end) {
        *fmc_dest++ = *code_word++;
    }
    uint32_t *rt_dest = (uint32_t *)RT_ICCM_ADDR;
    code_word = (uint32_t *)&iccm_code1_start;
    VPRINTF(LOW, "ROM: Copying RT code to ICCM\n");
    while (code_word < (uint32_t *)&iccm_code1_end) {
        *rt_dest++ = *code_word++;
    }

    // Program ICCM region registers with 2-phase shadow protocol
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, FMC_ICCM_START_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR,   FMC_ICCM_END_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_START_ADDR,  RT_ICCM_START_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_END_ADDR,    RT_ICCM_END_REL);
    // Phase 1: second write commits shadow registers
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, FMC_ICCM_START_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR,   FMC_ICCM_END_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_START_ADDR,  RT_ICCM_START_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_END_ADDR,    RT_ICCM_END_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_REGION_LOCK,    0x1);

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
    hmac_write_kv_slot(KV_SLOT_RT_CDI,   DV_CDI);
    hmac_write_kv_slot(KV_SLOT_RT_ECDSA, DV_ECC_PKEY);
    hmac_write_kv_slot(KV_SLOT_RT_MLDSA, DV_MLDSA_SEED);

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
