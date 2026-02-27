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
// =============================================================================
// smoke_test_kv_swwe_lock.c
//
// PURPOSE:
//   Validates the KV SWWE (Software Write Enable) lock fix across crypto engines.
//   Tests that KV read/write control registers cannot be modified while the
//   engine is busy (busy_o high), and can be modified once the engine is idle.
//
// WHAT THIS TESTS:
//   1. HMAC KV WR_CTRL: write_entry and dest_valid are locked while busy
//   2. HMAC KV RD_KEY_CTRL: read_entry is locked while busy
//   3. ECC KV WR_PKEY_CTRL: write_entry and dest_valid are locked while busy
//   4. pcr_hash_extend SWWE = 0: field cannot be set for KV operations
//   5. Post-operation writability: regs are writable after engine goes idle
//
// DIAGNOSTIC PRINTS:
//   Each step logs register values before/after attempted writes so that
//   log analysis can confirm SWWE protection is active.
// =============================================================================

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "hmac.h"
#include "caliptra_rtl_lib.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// ---- Helper: check register value unchanged after a write attempt ----
// Returns 1 if the register held its original value (SWWE blocked the write)
static int check_swwe_blocked(uint32_t reg_addr, uint32_t original_val,
                               uint32_t attack_val, const char *reg_name) {
    VPRINTF(LOW, "[SWWE_CHECK] %s: original=0x%08x, attempting write=0x%08x\n",
            reg_name, original_val, attack_val);
    lsu_write_32(reg_addr, attack_val);
    uint32_t readback = lsu_read_32(reg_addr);
    VPRINTF(LOW, "[SWWE_CHECK] %s: readback=0x%08x (expected=0x%08x)\n",
            reg_name, readback, original_val);
    if (readback != original_val) {
        VPRINTF(ERROR, "[SWWE_FAIL] %s: register modified while engine busy! "
                       "got=0x%08x expected=0x%08x\n", reg_name, readback, original_val);
        return 0;
    }
    VPRINTF(LOW, "[SWWE_PASS] %s: write correctly blocked\n", reg_name);
    return 1;
}

// ---- Helper: check register value changed after a write attempt ----
// Returns 1 if the register accepted the new value (SWWE allowed the write)
static int check_swwe_allowed(uint32_t reg_addr, uint32_t new_val,
                               const char *reg_name) {
    VPRINTF(LOW, "[SWWE_WRITABLE] %s: attempting write=0x%08x\n", reg_name, new_val);
    lsu_write_32(reg_addr, new_val);
    uint32_t readback = lsu_read_32(reg_addr);
    VPRINTF(LOW, "[SWWE_WRITABLE] %s: readback=0x%08x (expected=0x%08x)\n",
            reg_name, readback, new_val);
    if (readback != new_val) {
        VPRINTF(ERROR, "[SWWE_WRITABLE_FAIL] %s: register NOT writable when engine idle! "
                       "got=0x%08x expected=0x%08x\n", reg_name, readback, new_val);
        return 0;
    }
    VPRINTF(LOW, "[SWWE_WRITABLE_PASS] %s: write correctly accepted\n", reg_name);
    return 1;
}

// ---- Helper: wait for HMAC to complete via interrupt ----
static void wait_for_hmac_complete(void) {
    VPRINTF(LOW, "[WAIT] Waiting for HMAC completion interrupt...\n");
    while ((cptra_intr_rcv.hmac_error == 0) && (cptra_intr_rcv.hmac_notif == 0)) {
        __asm__ volatile ("wfi");
        for (uint16_t slp = 0; slp < 100; slp++) {
            __asm__ volatile ("nop");
        }
    }
    VPRINTF(LOW, "[WAIT] HMAC done: notif=%d, error=%d\n",
            cptra_intr_rcv.hmac_notif, cptra_intr_rcv.hmac_error);
}

// ---- Helper: wait for ECC to complete via interrupt ----
static void wait_for_ecc_complete(void) {
    VPRINTF(LOW, "[WAIT] Waiting for ECC completion interrupt...\n");
    while ((cptra_intr_rcv.ecc_error == 0) && (cptra_intr_rcv.ecc_notif == 0)) {
        __asm__ volatile ("wfi");
        for (uint16_t slp = 0; slp < 100; slp++) {
            __asm__ volatile ("nop");
        }
    }
    VPRINTF(LOW, "[WAIT] ECC done: notif=%d, error=%d\n",
            cptra_intr_rcv.ecc_notif, cptra_intr_rcv.ecc_error);
}


// =============================================================================
// TEST 1: HMAC KV SWWE Lock During Operation
//
// Strategy: pre-load KV ctrl regs with non-zero entry/dest (enable=0), run
// HMAC using direct register writes (no KV read/write), then immediately try
// to overwrite the ctrl regs (including setting enable=1) while the engine is
// busy.  Readback must equal the pre-loaded values.  No KV access plumbing
// needed — SWWE=0 is driven purely by core_ready=0 during computation.
// =============================================================================
static int test_hmac_kv_swwe_lock(void) {
    int pass = 1;
    volatile uint32_t *reg_ptr;

    VPRINTF(LOW, "\n============================================================\n");
    VPRINTF(LOW, " TEST 1: HMAC KV SWWE Lock During Operation\n");
    VPRINTF(LOW, "============================================================\n");

    // Wait for HMAC ready
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);
    VPRINTF(LOW, "[HMAC] Engine ready\n");

    // ------------------------------------------------------------------
    // Step 1: Pre-configure KV ctrl regs with non-zero values, enable=0.
    //         These values act as the "original" reference we compare
    //         against after the failed attack writes.
    // ------------------------------------------------------------------
    uint32_t wr_ctrl_orig = ((5 << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
                              HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK) |
                             HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK;
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL, wr_ctrl_orig);
    wr_ctrl_orig = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL);  // capture actual reset-masked value

    uint32_t rd_key_orig = ((2 << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) &
                             HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK);
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, rd_key_orig);
    rd_key_orig = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL);

    uint32_t rd_block_orig = ((3 << HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW) &
                               HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_MASK);
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL, rd_block_orig);
    rd_block_orig = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL);

    VPRINTF(LOW, "[HMAC] KV ctrl pre-load: WR=0x%08x RD_KEY=0x%08x RD_BLOCK=0x%08x\n",
            wr_ctrl_orig, rd_key_orig, rd_block_orig);

    // ------------------------------------------------------------------
    // Step 2: Load key, block, and LFSR seed directly (no KV read).
    // ------------------------------------------------------------------
    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_0;
    while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_15)
        *reg_ptr++ = 0x0b0b0b0b;

    lsu_write_32(CLP_HMAC_REG_HMAC512_BLOCK_0,          0x48692054);
    lsu_write_32(CLP_HMAC_REG_HMAC512_BLOCK_1,          0x68657265);
    lsu_write_32(CLP_HMAC_REG_HMAC512_BLOCK_2,          0x80000000);
    for (uint32_t i = 3; i < 31; i++)
        lsu_write_32(CLP_HMAC_REG_HMAC512_BLOCK_0 + (i * 4), 0x00000000);
    lsu_write_32(CLP_HMAC_REG_HMAC512_BLOCK_0 + (31 * 4), 0x00000440);

    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC512_LFSR_SEED_0;
    while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_LFSR_SEED_11)
        *reg_ptr++ = 0xDEADBEEF;

    // ------------------------------------------------------------------
    // Step 3: Start HMAC, then IMMEDIATELY attempt attack writes.
    //         No VPRINTFs or polls between INIT and the attacks — HMAC
    //         completes in hundreds of cycles; extra AHB ops burn that
    //         budget and let the engine go idle (SWWE re-opens) before
    //         our attack arrives.
    //
    //         Attack includes: new entry, new dest_valid, AND enable=1.
    //         All must be blocked while core_ready=0.
    // ------------------------------------------------------------------
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_INIT_MASK |
                                            (HMAC512_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));

    uint32_t attack_wr = HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
                         ((10 << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
                          HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK) |
                         HMAC_REG_HMAC512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK;
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL, attack_wr);
    uint32_t wr_ctrl_after = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL);

    uint32_t attack_rd_key = HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                             ((7 << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) &
                              HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK);
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, attack_rd_key);
    uint32_t rd_key_after = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL);

    uint32_t attack_rd_block = HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_EN_MASK |
                               ((8 << HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW) &
                                HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_MASK);
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL, attack_rd_block);
    uint32_t rd_block_after = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL);

    // ------------------------------------------------------------------
    // Step 4: Wait for HMAC to finish (poll STATUS.READY — no WFI/interrupt
    //         dependency).  All logging happens after the timing window.
    // ------------------------------------------------------------------
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);
    cptra_intr_rcv.hmac_error = 0;
    cptra_intr_rcv.hmac_notif = 0;

    // ------------------------------------------------------------------
    // Step 5: Log and evaluate SWWE check results.
    // ------------------------------------------------------------------
    VPRINTF(LOW, "\n[HMAC] === SWWE lock results ===\n");

    VPRINTF(LOW, "[SWWE_CHECK] KV_WR_CTRL:    orig=0x%08x  attack=0x%08x  after=0x%08x\n",
            wr_ctrl_orig, attack_wr, wr_ctrl_after);
    if (wr_ctrl_after != wr_ctrl_orig) {
        VPRINTF(ERROR, "[SWWE_FAIL] KV_WR_CTRL modified while engine busy!\n");
        pass = 0;
    } else {
        VPRINTF(LOW, "[SWWE_PASS] KV_WR_CTRL correctly blocked\n");
    }

    VPRINTF(LOW, "[SWWE_CHECK] KV_RD_KEY_CTRL:   orig=0x%08x  attack=0x%08x  after=0x%08x\n",
            rd_key_orig, attack_rd_key, rd_key_after);
    if (rd_key_after != rd_key_orig) {
        VPRINTF(ERROR, "[SWWE_FAIL] KV_RD_KEY_CTRL modified while engine busy!\n");
        pass = 0;
    } else {
        VPRINTF(LOW, "[SWWE_PASS] KV_RD_KEY_CTRL correctly blocked\n");
    }

    VPRINTF(LOW, "[SWWE_CHECK] KV_RD_BLOCK_CTRL: orig=0x%08x  attack=0x%08x  after=0x%08x\n",
            rd_block_orig, attack_rd_block, rd_block_after);
    if (rd_block_after != rd_block_orig) {
        VPRINTF(ERROR, "[SWWE_FAIL] KV_RD_BLOCK_CTRL modified while engine busy!\n");
        pass = 0;
    } else {
        VPRINTF(LOW, "[SWWE_PASS] KV_RD_BLOCK_CTRL correctly blocked\n");
    }

    // ------------------------------------------------------------------
    // Step 6: Verify registers are writable after engine goes idle.
    //         Write new entry/dest values (no enable) and confirm they
    //         stick.  enable is hwclr so we exclude it from the readback
    //         comparison.
    // ------------------------------------------------------------------
    VPRINTF(LOW, "\n[HMAC] === Verifying registers writable after idle ===\n");

    hmac_zeroize();
    cptra_intr_rcv.hmac_error = 0;
    cptra_intr_rcv.hmac_notif = 0;
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    uint32_t new_wr_ctrl = ((15 << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
                             HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK) |
                            HMAC_REG_HMAC512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK;
    if (!check_swwe_allowed(CLP_HMAC_REG_HMAC512_KV_WR_CTRL, new_wr_ctrl,
                            "KV_WR_CTRL (post-idle)"))
        pass = 0;

    uint32_t new_rd_key = ((9 << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) &
                            HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK);
    if (!check_swwe_allowed(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, new_rd_key,
                            "KV_RD_KEY_CTRL (post-idle)"))
        pass = 0;

    hmac_zeroize();
    cptra_intr_rcv.hmac_error = 0;
    cptra_intr_rcv.hmac_notif = 0;

    return pass;
}

// =============================================================================
// TEST 2: ECC KV SWWE Lock During Operation
//
// Strategy: same as TEST 1 — pre-load KV ctrl regs (no enable), run ECC
// keygen using direct register writes, immediately attack while busy.
// No KV read/write or TB injection needed.
// =============================================================================
static int test_ecc_kv_swwe_lock(void) {
    int pass = 1;
    volatile uint32_t *reg_ptr;

    VPRINTF(LOW, "\n============================================================\n");
    VPRINTF(LOW, " TEST 2: ECC KV SWWE Lock During Operation\n");
    VPRINTF(LOW, "============================================================\n");

    // Wait for ECC ready
    while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
    VPRINTF(LOW, "[ECC] Engine ready\n");

    // ------------------------------------------------------------------
    // Step 1: Pre-configure KV ctrl regs with non-zero values, enable=0.
    // ------------------------------------------------------------------
    uint32_t wr_pkey_orig = ((3 << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) &
                              ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK) |
                             ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK;
    lsu_write_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, wr_pkey_orig);
    wr_pkey_orig = lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL);

    uint32_t rd_seed_orig = ((1 << ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW) &
                              ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_MASK);
    lsu_write_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL, rd_seed_orig);
    rd_seed_orig = lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL);

    VPRINTF(LOW, "[ECC] KV ctrl pre-load: WR_PKEY=0x%08x  RD_SEED=0x%08x\n",
            wr_pkey_orig, rd_seed_orig);

    // ------------------------------------------------------------------
    // Step 2: Load seed, nonce, and IV directly (no KV read).
    // ------------------------------------------------------------------
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SEED_0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SEED_11)
        *reg_ptr++ = 0xDEADBEEF;

    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_NONCE_0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_NONCE_11)
        *reg_ptr++ = 0xCAFEBABE;

    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11)
        *reg_ptr++ = 0x12345678;

    // ------------------------------------------------------------------
    // Step 3: Start ECC keygen then IMMEDIATELY attempt attack writes.
    // ------------------------------------------------------------------
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, 0x1); // KEYGEN command

    uint32_t attack_wr_pkey = ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                              ((20 << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) &
                               ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK) |
                              ECC_REG_ECC_KV_WR_PKEY_CTRL_HMAC_KEY_DEST_VALID_MASK;
    lsu_write_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, attack_wr_pkey);
    uint32_t wr_pkey_after = lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL);

    uint32_t attack_rd_seed = ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK |
                              ((15 << ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW) &
                               ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_MASK);
    lsu_write_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL, attack_rd_seed);
    uint32_t rd_seed_after = lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL);

    // ------------------------------------------------------------------
    // Step 4: Wait for ECC to complete (poll STATUS.READY).
    // ------------------------------------------------------------------
    while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
    cptra_intr_rcv.ecc_error = 0;
    cptra_intr_rcv.ecc_notif = 0;

    // ------------------------------------------------------------------
    // Step 5: Log and evaluate SWWE check results.
    // ------------------------------------------------------------------
    VPRINTF(LOW, "\n[ECC] === SWWE lock results ===\n");

    VPRINTF(LOW, "[SWWE_CHECK] KV_WR_PKEY_CTRL: orig=0x%08x  attack=0x%08x  after=0x%08x\n",
            wr_pkey_orig, attack_wr_pkey, wr_pkey_after);
    if (wr_pkey_after != wr_pkey_orig) {
        VPRINTF(ERROR, "[SWWE_FAIL] KV_WR_PKEY_CTRL modified while engine busy!\n");
        pass = 0;
    } else {
        VPRINTF(LOW, "[SWWE_PASS] KV_WR_PKEY_CTRL correctly blocked\n");
    }

    VPRINTF(LOW, "[SWWE_CHECK] KV_RD_SEED_CTRL: orig=0x%08x  attack=0x%08x  after=0x%08x\n",
            rd_seed_orig, attack_rd_seed, rd_seed_after);
    if (rd_seed_after != rd_seed_orig) {
        VPRINTF(ERROR, "[SWWE_FAIL] KV_RD_SEED_CTRL modified while engine busy!\n");
        pass = 0;
    } else {
        VPRINTF(LOW, "[SWWE_PASS] KV_RD_SEED_CTRL correctly blocked\n");
    }

    // ------------------------------------------------------------------
    // Step 6: Verify registers are writable after engine goes idle.
    // ------------------------------------------------------------------
    VPRINTF(LOW, "\n[ECC] === Verifying registers writable after idle ===\n");

    lsu_write_32(CLP_ECC_REG_ECC_CTRL, (1 << ECC_REG_ECC_CTRL_ZEROIZE_LOW) &
                                        ECC_REG_ECC_CTRL_ZEROIZE_MASK);
    cptra_intr_rcv.ecc_error = 0;
    cptra_intr_rcv.ecc_notif = 0;
    while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    uint32_t new_wr_pkey = ((8 << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) &
                             ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK) |
                            ECC_REG_ECC_KV_WR_PKEY_CTRL_AES_KEY_DEST_VALID_MASK;
    if (!check_swwe_allowed(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, new_wr_pkey,
                            "KV_WR_PKEY_CTRL (post-idle)"))
        pass = 0;

    lsu_write_32(CLP_ECC_REG_ECC_CTRL, (1 << ECC_REG_ECC_CTRL_ZEROIZE_LOW) &
                                        ECC_REG_ECC_CTRL_ZEROIZE_MASK);
    cptra_intr_rcv.ecc_error = 0;
    cptra_intr_rcv.ecc_notif = 0;

    return pass;
}

// =============================================================================
// TEST 3: pcr_hash_extend SWWE = 0 (always locked for KV operations)
// =============================================================================
static int test_pcr_hash_extend_locked(void) {
    int pass = 1;

    VPRINTF(LOW, "\n============================================================\n");
    VPRINTF(LOW, " TEST 3: pcr_hash_extend SWWE = 0 (always locked)\n");
    VPRINTF(LOW, "============================================================\n");

    // Wait for HMAC ready
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    // Read current KV RD KEY CTRL
    uint32_t rd_key_before = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL);
    VPRINTF(LOW, "[PCR_EXT] HMAC KV_RD_KEY_CTRL before = 0x%08x\n", rd_key_before);

    // Try to set pcr_hash_extend bit (bit 6 in HMAC KV_RD_KEY_CTRL)
    uint32_t with_pcr_extend = rd_key_before | HMAC_REG_HMAC512_KV_RD_KEY_CTRL_PCR_HASH_EXTEND_MASK;
    VPRINTF(LOW, "[PCR_EXT] Attempting to set pcr_hash_extend: write=0x%08x\n", with_pcr_extend);
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, with_pcr_extend);

    uint32_t rd_key_after = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL);
    VPRINTF(LOW, "[PCR_EXT] HMAC KV_RD_KEY_CTRL after = 0x%08x\n", rd_key_after);

    // The pcr_hash_extend bit should NOT be set (SWWE=0)
    if (rd_key_after & HMAC_REG_HMAC512_KV_RD_KEY_CTRL_PCR_HASH_EXTEND_MASK) {
        VPRINTF(ERROR, "[PCR_EXT_FAIL] pcr_hash_extend bit was set! SWWE=0 not enforced\n");
        pass = 0;
    } else {
        VPRINTF(LOW, "[PCR_EXT_PASS] pcr_hash_extend correctly blocked (SWWE=0)\n");
    }

    // Also check HMAC KV_RD_BLOCK_CTRL
    uint32_t rd_block_before = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL);
    uint32_t with_pcr_block = rd_block_before | HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_PCR_HASH_EXTEND_MASK;
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL, with_pcr_block);
    uint32_t rd_block_after = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL);
    VPRINTF(LOW, "[PCR_EXT] HMAC KV_RD_BLOCK_CTRL: before=0x%08x, wrote=0x%08x, after=0x%08x\n",
            rd_block_before, with_pcr_block, rd_block_after);

    if (rd_block_after & HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_PCR_HASH_EXTEND_MASK) {
        VPRINTF(ERROR, "[PCR_EXT_FAIL] pcr_hash_extend in BLOCK CTRL was set!\n");
        pass = 0;
    } else {
        VPRINTF(LOW, "[PCR_EXT_PASS] pcr_hash_extend in BLOCK CTRL correctly blocked\n");
    }

    // Check ECC seed ctrl pcr_hash_extend
    while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
    uint32_t ecc_seed_before = lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL);
    uint32_t ecc_seed_with_pcr = ecc_seed_before | ECC_REG_ECC_KV_RD_SEED_CTRL_PCR_HASH_EXTEND_MASK;
    lsu_write_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL, ecc_seed_with_pcr);
    uint32_t ecc_seed_after = lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL);
    VPRINTF(LOW, "[PCR_EXT] ECC KV_RD_SEED_CTRL: before=0x%08x, wrote=0x%08x, after=0x%08x\n",
            ecc_seed_before, ecc_seed_with_pcr, ecc_seed_after);

    if (ecc_seed_after & ECC_REG_ECC_KV_RD_SEED_CTRL_PCR_HASH_EXTEND_MASK) {
        VPRINTF(ERROR, "[PCR_EXT_FAIL] pcr_hash_extend in ECC SEED CTRL was set!\n");
        pass = 0;
    } else {
        VPRINTF(LOW, "[PCR_EXT_PASS] pcr_hash_extend in ECC SEED CTRL correctly blocked\n");
    }

    // Check AES key ctrl pcr_hash_extend
    uint32_t aes_key_before = lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL);
    uint32_t aes_key_with_pcr = aes_key_before | AES_CLP_REG_AES_KV_RD_KEY_CTRL_PCR_HASH_EXTEND_MASK;
    lsu_write_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL, aes_key_with_pcr);
    uint32_t aes_key_after = lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL);
    VPRINTF(LOW, "[PCR_EXT] AES KV_RD_KEY_CTRL: before=0x%08x, wrote=0x%08x, after=0x%08x\n",
            aes_key_before, aes_key_with_pcr, aes_key_after);

    if (aes_key_after & AES_CLP_REG_AES_KV_RD_KEY_CTRL_PCR_HASH_EXTEND_MASK) {
        VPRINTF(ERROR, "[PCR_EXT_FAIL] pcr_hash_extend in AES KEY CTRL was set!\n");
        pass = 0;
    } else {
        VPRINTF(LOW, "[PCR_EXT_PASS] pcr_hash_extend in AES KEY CTRL correctly blocked\n");
    }

    return pass;
}



// =============================================================================
// MAIN
// =============================================================================
void main() {
    int all_pass = 1;

    VPRINTF(LOW, "============================================================\n");
    VPRINTF(LOW, " KV SWWE Lock Smoke Test\n");
    VPRINTF(LOW, " Tests that KV control registers are locked while busy_o=1\n");
    VPRINTF(LOW, "============================================================\n");

    // Initialize interrupts
    init_interrupts();

    // ---- TEST 1: HMAC KV SWWE Lock ----
    if (!test_hmac_kv_swwe_lock()) {
        VPRINTF(ERROR, "\n*** TEST 1 FAILED: HMAC KV SWWE Lock ***\n");
        all_pass = 0;
    } else {
        VPRINTF(LOW, "\n*** TEST 1 PASSED: HMAC KV SWWE Lock ***\n");
    }

    // ---- TEST 2: ECC KV SWWE Lock ----
    if (!test_ecc_kv_swwe_lock()) {
        VPRINTF(ERROR, "\n*** TEST 2 FAILED: ECC KV SWWE Lock ***\n");
        all_pass = 0;
    } else {
        VPRINTF(LOW, "\n*** TEST 2 PASSED: ECC KV SWWE Lock ***\n");
    }

    // ---- TEST 3: pcr_hash_extend SWWE=0 ----
    if (!test_pcr_hash_extend_locked()) {
        VPRINTF(ERROR, "\n*** TEST 3 FAILED: pcr_hash_extend SWWE=0 ***\n");
        all_pass = 0;
    } else {
        VPRINTF(LOW, "\n*** TEST 3 PASSED: pcr_hash_extend SWWE=0 ***\n");
    }

    // ---- Final verdict ----
    if (all_pass) {
        VPRINTF(LOW, "\n============================================================\n");
        VPRINTF(LOW, " ALL KV SWWE LOCK TESTS PASSED\n");
        VPRINTF(LOW, "============================================================\n");
        SEND_STDOUT_CTRL(0xff);
    } else {
        VPRINTF(ERROR, "\n============================================================\n");
        VPRINTF(ERROR, " ONE OR MORE KV SWWE LOCK TESTS FAILED\n");
        VPRINTF(ERROR, "============================================================\n");
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
}
