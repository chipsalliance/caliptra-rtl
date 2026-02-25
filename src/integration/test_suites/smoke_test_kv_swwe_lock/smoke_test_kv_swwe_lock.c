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
// =============================================================================
static int test_hmac_kv_swwe_lock(void) {
    int pass = 1;
    uint32_t reg_val, readback;

    VPRINTF(LOW, "\n============================================================\n");
    VPRINTF(LOW, " TEST 1: HMAC KV SWWE Lock During Operation\n");
    VPRINTF(LOW, "============================================================\n");

    // Wait for HMAC ready
    VPRINTF(LOW, "[HMAC] Waiting for HMAC ready...\n");
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);
    VPRINTF(LOW, "[HMAC] Engine is ready (idle)\n");

    // ------------------------------------------------------------------
    // Step 1: Configure KV write control to write result to KV slot 5
    // ------------------------------------------------------------------
    uint32_t kv_wr_ctrl_val = HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
                              ((5 << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
                               HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK) |
                              HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK;

    VPRINTF(LOW, "[HMAC] Setting KV_WR_CTRL = 0x%08x (slot=5, hmac_key_dest=1)\n", kv_wr_ctrl_val);
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL, kv_wr_ctrl_val);
    readback = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL);
    VPRINTF(LOW, "[HMAC] KV_WR_CTRL readback = 0x%08x\n", readback);

    // ------------------------------------------------------------------
    // Step 2: Load key and block data directly (no KV read)
    // ------------------------------------------------------------------
    VPRINTF(LOW, "[HMAC] Loading key and block data via APB...\n");
    volatile uint32_t *reg_ptr;

    // Load a simple key pattern (all 0x0b)
    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_0;
    while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_15) {
        *reg_ptr++ = 0x0b0b0b0b;
    }

    // Load a simple block (Hi There + padding)
    lsu_write_32(CLP_HMAC_REG_HMAC512_BLOCK_0, 0x48692054);
    lsu_write_32(CLP_HMAC_REG_HMAC512_BLOCK_1, 0x68657265);
    lsu_write_32(CLP_HMAC_REG_HMAC512_BLOCK_2, 0x80000000);
    for (uint32_t i = 3; i < 31; i++) {
        lsu_write_32(CLP_HMAC_REG_HMAC512_BLOCK_0 + (i * 4), 0x00000000);
    }
    lsu_write_32(CLP_HMAC_REG_HMAC512_BLOCK_0 + (31 * 4), 0x00000440);

    // Load LFSR seed
    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC512_LFSR_SEED_0;
    while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_LFSR_SEED_11) {
        *reg_ptr++ = 0xDEADBEEF;
    }

    // ------------------------------------------------------------------
    // Step 3: Kick off HMAC (engine goes busy)
    // ------------------------------------------------------------------
    VPRINTF(LOW, "[HMAC] Starting HMAC512 INIT...\n");
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_INIT_MASK |
                                            (HMAC512_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));

    // Wait until engine is actually busy (STATUS.READY goes low)
    // busy_o takes 1-2 cycles to propagate after INIT; FW writes can race it
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) != 0);
    VPRINTF(LOW, "[HMAC] Engine is now busy (STATUS.READY=0)\n");

    // Re-read WR_CTRL since write_en.hwclr may have cleared write_en
    kv_wr_ctrl_val = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL);
    VPRINTF(LOW, "[HMAC] KV_WR_CTRL after busy = 0x%08x (write_en may be hwclr'd)\n", kv_wr_ctrl_val);

    // ------------------------------------------------------------------
    // Step 4: Try to modify KV WR_CTRL while engine is busy
    //         The SWWE should block these writes.
    // ------------------------------------------------------------------
    VPRINTF(LOW, "\n[HMAC] === Attempting KV WR_CTRL modification while busy ===\n");

    // 4a: Try to change write_entry from 5 to 10
    uint32_t attack_wr_ctrl = HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
                              ((10 << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
                               HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK) |
                              HMAC_REG_HMAC512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK;

    if (!check_swwe_blocked(CLP_HMAC_REG_HMAC512_KV_WR_CTRL, kv_wr_ctrl_val,
                            attack_wr_ctrl, "HMAC_KV_WR_CTRL"))
        pass = 0;

    // 4b: Try to modify KV RD_KEY_CTRL while busy
    VPRINTF(LOW, "\n[HMAC] === Attempting KV RD_KEY_CTRL modification while busy ===\n");
    uint32_t rd_ctrl_before = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL);
    uint32_t attack_rd_ctrl = HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                              ((7 << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) &
                               HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK);

    if (!check_swwe_blocked(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, rd_ctrl_before,
                            attack_rd_ctrl, "HMAC_KV_RD_KEY_CTRL"))
        pass = 0;

    // 4c: Try to modify KV RD_BLOCK_CTRL while busy
    VPRINTF(LOW, "\n[HMAC] === Attempting KV RD_BLOCK_CTRL modification while busy ===\n");
    uint32_t rd_block_before = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL);
    uint32_t attack_rd_block = HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_EN_MASK |
                               ((3 << HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW) &
                                HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_MASK);

    if (!check_swwe_blocked(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL, rd_block_before,
                            attack_rd_block, "HMAC_KV_RD_BLOCK_CTRL"))
        pass = 0;

    // ------------------------------------------------------------------
    // Step 5: Wait for HMAC to finish
    // ------------------------------------------------------------------
    wait_for_hmac_complete();

    // Wait for KV write to complete (bounded poll to prevent infinite hang)
    VPRINTF(LOW, "[HMAC] Waiting for KV WR STATUS valid...\n");
    uint32_t kv_wr_timeout = 0;
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_STATUS) &
            HMAC_REG_HMAC512_KV_WR_STATUS_VALID_MASK) == 0) {
        if (++kv_wr_timeout > 20000) {
            VPRINTF(ERROR, "[HMAC] KV WR STATUS timeout! STATUS=0x%08x, WR_CTRL=0x%08x, busy=%d\n",
                    lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_STATUS),
                    lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL),
                    (lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);
            pass = 0;
            break;
        }
    }
    VPRINTF(LOW, "[HMAC] KV WR STATUS = 0x%08x\n",
            lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_STATUS));

    // ------------------------------------------------------------------
    // Step 6: Verify registers are writable after engine goes idle
    // ------------------------------------------------------------------
    VPRINTF(LOW, "\n[HMAC] === Verifying registers writable after idle ===\n");

    // Zeroize HMAC to clear state
    hmac_zeroize();
    cptra_intr_rcv.hmac_error = 0;
    cptra_intr_rcv.hmac_notif = 0;

    // Wait for ready again
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    // Try to write new KV WR_CTRL value — should succeed now
    uint32_t new_wr_ctrl = HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
                           ((15 << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
                            HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK) |
                           HMAC_REG_HMAC512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK;

    if (!check_swwe_allowed(CLP_HMAC_REG_HMAC512_KV_WR_CTRL, new_wr_ctrl,
                            "HMAC_KV_WR_CTRL (post-idle)"))
        pass = 0;

    // Zeroize again to reset write_en
    hmac_zeroize();
    cptra_intr_rcv.hmac_error = 0;
    cptra_intr_rcv.hmac_notif = 0;

    return pass;
}


// =============================================================================
// TEST 2: ECC KV SWWE Lock During Operation
// =============================================================================
static int test_ecc_kv_swwe_lock(void) {
    int pass = 1;
    uint32_t readback;

    VPRINTF(LOW, "\n============================================================\n");
    VPRINTF(LOW, " TEST 2: ECC KV SWWE Lock During Operation\n");
    VPRINTF(LOW, "============================================================\n");

    // Wait for ECC ready
    VPRINTF(LOW, "[ECC] Waiting for ECC ready...\n");
    while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
    VPRINTF(LOW, "[ECC] Engine is ready (idle)\n");

    // ------------------------------------------------------------------
    // Step 1: Configure KV write control to write pkey to KV slot 3
    // ------------------------------------------------------------------
    uint32_t kv_wr_ctrl_val = ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                              ((3 << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) &
                               ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK) |
                              ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK;

    VPRINTF(LOW, "[ECC] Setting KV_WR_PKEY_CTRL = 0x%08x (slot=3, ecc_pkey_dest=1)\n", kv_wr_ctrl_val);
    lsu_write_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, kv_wr_ctrl_val);
    readback = lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL);
    VPRINTF(LOW, "[ECC] KV_WR_PKEY_CTRL readback = 0x%08x\n", readback);

    // ------------------------------------------------------------------
    // Step 2: Load seed via KV read from slot 0 (inject in TB)
    // ------------------------------------------------------------------
    // Inject seed to KV slot 0 via TB mechanism
    lsu_write_32(STDOUT, (0 << 8) | 0xa5);

    // Program ECC seed read from KV slot 0
    lsu_write_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL, ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK |
                 ((0 << ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW) &
                  ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_MASK));

    // Wait for seed loaded
    while ((lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_STATUS) &
            ECC_REG_ECC_KV_RD_SEED_STATUS_VALID_MASK) == 0);
    VPRINTF(LOW, "[ECC] Seed loaded from KV, status=0x%08x\n",
            lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_STATUS));

    // ------------------------------------------------------------------
    // Step 3: Start ECC keygen (engine goes busy)
    // ------------------------------------------------------------------
    // Write msg hash (required for signing, but keygen only needs seed)
    for (uint32_t i = 0; i < 12; i++) {
        lsu_write_32(CLP_ECC_REG_ECC_MSG_0 + (i * 4), 0xABCD1234 + i);
    }

    VPRINTF(LOW, "[ECC] Starting ECC keygen (CTRL=1)...\n");
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, 0x1); // KEYGEN command

    // Wait until engine is actually busy (STATUS.READY goes low)
    while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) != 0);
    VPRINTF(LOW, "[ECC] Engine is now busy (STATUS.READY=0)\n");

    // Re-read WR_PKEY_CTRL since write_en.hwclr may have cleared write_en
    kv_wr_ctrl_val = lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL);
    VPRINTF(LOW, "[ECC] KV_WR_PKEY_CTRL after busy = 0x%08x (write_en may be hwclr'd)\n", kv_wr_ctrl_val);

    // ------------------------------------------------------------------
    // Step 4: Try to modify KV WR_PKEY_CTRL while busy
    // ------------------------------------------------------------------
    VPRINTF(LOW, "\n[ECC] === Attempting KV WR_PKEY_CTRL modification while busy ===\n");

    // Try to redirect to slot 20 with different dest_valid
    uint32_t attack_wr_ctrl = ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                              ((20 << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) &
                               ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK) |
                              ECC_REG_ECC_KV_WR_PKEY_CTRL_HMAC_KEY_DEST_VALID_MASK;

    if (!check_swwe_blocked(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, kv_wr_ctrl_val,
                            attack_wr_ctrl, "ECC_KV_WR_PKEY_CTRL"))
        pass = 0;

    // Try to modify KV RD_SEED_CTRL while busy
    VPRINTF(LOW, "\n[ECC] === Attempting KV RD_SEED_CTRL modification while busy ===\n");
    uint32_t rd_seed_before = lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL);
    uint32_t attack_rd_seed = ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK |
                              ((15 << ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW) &
                               ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_MASK);

    if (!check_swwe_blocked(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL, rd_seed_before,
                            attack_rd_seed, "ECC_KV_RD_SEED_CTRL"))
        pass = 0;

    // ------------------------------------------------------------------
    // Step 5: Wait for ECC to finish
    // ------------------------------------------------------------------
    wait_for_ecc_complete();

    // Check if KV write completed (bounded poll)
    VPRINTF(LOW, "[ECC] Waiting for KV WR PKEY STATUS valid...\n");
    uint32_t ecc_kv_timeout = 0;
    while ((lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_STATUS) &
            ECC_REG_ECC_KV_WR_PKEY_STATUS_VALID_MASK) == 0) {
        if (++ecc_kv_timeout > 20000) {
            VPRINTF(ERROR, "[ECC] KV WR PKEY STATUS timeout! STATUS=0x%08x, WR_CTRL=0x%08x\n",
                    lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_STATUS),
                    lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL));
            pass = 0;
            break;
        }
    }
    VPRINTF(LOW, "[ECC] KV WR PKEY STATUS = 0x%08x\n",
            lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_STATUS));

    // ------------------------------------------------------------------
    // Step 6: Verify registers are writable after engine goes idle
    // ------------------------------------------------------------------
    VPRINTF(LOW, "\n[ECC] === Verifying registers writable after idle ===\n");

    // Zeroize to clear state
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, (1 << ECC_REG_ECC_CTRL_ZEROIZE_LOW) &
                                        ECC_REG_ECC_CTRL_ZEROIZE_MASK);
    cptra_intr_rcv.ecc_error = 0;
    cptra_intr_rcv.ecc_notif = 0;

    // Wait for ready
    while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    // Try to write new KV WR_PKEY_CTRL — should succeed now
    uint32_t new_wr_ctrl = ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                           ((8 << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) &
                            ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK) |
                           ECC_REG_ECC_KV_WR_PKEY_CTRL_AES_KEY_DEST_VALID_MASK;

    if (!check_swwe_allowed(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, new_wr_ctrl,
                            "ECC_KV_WR_PKEY_CTRL (post-idle)"))
        pass = 0;

    // Zeroize to reset
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
// TEST 4: KV lock_use Error Code Capture (kv_read_client fix)
//
// Validates the kv_read_client.sv error_code priority fix:
//   - Write a key to KV slot via TB injection
//   - Set lock_use on that slot (prevents all reads)
//   - Attempt HMAC KV read from locked slot
//   - Verify KV_RD_STATUS reports error (KV_READ_FAIL = 0x01)
//   - Clear lock_use, re-read, verify success
// =============================================================================
static int test_kv_lock_use_error(void) {
    int pass = 1;
    uint32_t status;
    uint8_t test_slot = 2;  // Use KV slot 2 for lock_use test

    VPRINTF(LOW, "\n============================================================\n");
    VPRINTF(LOW, " TEST 4: KV lock_use Error Code Capture\n");
    VPRINTF(LOW, "============================================================\n");

    // Wait for HMAC ready
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    // ------------------------------------------------------------------
    // Step 1: Inject a key into KV slot via TB mechanism
    // ------------------------------------------------------------------
    VPRINTF(LOW, "[LOCK_USE] Injecting key into KV slot %d via TB...\n", test_slot);
    lsu_write_32(STDOUT, (test_slot << 8) | 0xa9);

    // ------------------------------------------------------------------
    // Step 2: Set lock_use on the slot (sticky until reset)
    //         KEY_CTRL address = CLP_KV_REG_KEY_CTRL_0 + (slot * 4)
    //         lock_use = bit 1
    // ------------------------------------------------------------------
    uint32_t key_ctrl_addr = CLP_KV_REG_KEY_CTRL_0 + (test_slot * 4);
    uint32_t key_ctrl_val = lsu_read_32(key_ctrl_addr);
    VPRINTF(LOW, "[LOCK_USE] KEY_CTRL[%d] before lock_use = 0x%08x\n", test_slot, key_ctrl_val);

    // Set lock_use bit
    key_ctrl_val |= KV_REG_KEY_CTRL_0_LOCK_USE_MASK;
    lsu_write_32(key_ctrl_addr, key_ctrl_val);
    uint32_t key_ctrl_readback = lsu_read_32(key_ctrl_addr);
    VPRINTF(LOW, "[LOCK_USE] KEY_CTRL[%d] after lock_use set = 0x%08x\n",
            test_slot, key_ctrl_readback);

    if (!(key_ctrl_readback & KV_REG_KEY_CTRL_0_LOCK_USE_MASK)) {
        VPRINTF(ERROR, "[LOCK_USE_FAIL] lock_use bit not set!\n");
        pass = 0;
    }

    // ------------------------------------------------------------------
    // Step 3: Attempt HMAC KV read from locked slot — should get error
    // ------------------------------------------------------------------
    VPRINTF(LOW, "[LOCK_USE] Attempting HMAC KV key read from locked slot %d...\n", test_slot);
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL,
                 HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                 ((test_slot << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) &
                  HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

    // Wait for valid
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS) &
            HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK) == 0);

    status = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS);
    uint32_t error_field = (status & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_MASK) >>
                           HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_LOW;
    VPRINTF(LOW, "[LOCK_USE] HMAC KV_RD_KEY_STATUS = 0x%08x (error_field = 0x%02x)\n",
            status, error_field);

    if (error_field == 0) {
        VPRINTF(ERROR, "[LOCK_USE_FAIL] Expected KV_READ_FAIL error but got success! "
                       "error_code not captured for lock_use violation\n");
        pass = 0;
    } else {
        VPRINTF(LOW, "[LOCK_USE_PASS] KV read from lock_use slot correctly returned error=0x%02x\n",
                error_field);
    }

    // Zeroize HMAC to clear state
    hmac_zeroize();
    cptra_intr_rcv.hmac_error = 0;
    cptra_intr_rcv.hmac_notif = 0;

    // ------------------------------------------------------------------
    // Step 4: Also verify ECC read from locked slot returns error
    // ------------------------------------------------------------------
    while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    VPRINTF(LOW, "[LOCK_USE] Attempting ECC KV seed read from locked slot %d...\n", test_slot);
    lsu_write_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL,
                 ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK |
                 ((test_slot << ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW) &
                  ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_MASK));

    // Wait for valid
    while ((lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_STATUS) &
            ECC_REG_ECC_KV_RD_SEED_STATUS_VALID_MASK) == 0);

    status = lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_STATUS);
    error_field = (status & ECC_REG_ECC_KV_RD_SEED_STATUS_ERROR_MASK) >>
                  ECC_REG_ECC_KV_RD_SEED_STATUS_ERROR_LOW;
    VPRINTF(LOW, "[LOCK_USE] ECC KV_RD_SEED_STATUS = 0x%08x (error_field = 0x%02x)\n",
            status, error_field);

    if (error_field == 0) {
        VPRINTF(ERROR, "[LOCK_USE_FAIL] Expected ECC KV_READ_FAIL for lock_use slot!\n");
        pass = 0;
    } else {
        VPRINTF(LOW, "[LOCK_USE_PASS] ECC read from lock_use slot correctly returned error=0x%02x\n",
                error_field);
    }

    // Zeroize ECC
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, (1 << ECC_REG_ECC_CTRL_ZEROIZE_LOW) &
                                        ECC_REG_ECC_CTRL_ZEROIZE_MASK);
    cptra_intr_rcv.ecc_error = 0;
    cptra_intr_rcv.ecc_notif = 0;

    // ------------------------------------------------------------------
    // Step 5: Verify AES read from locked slot also returns error
    // ------------------------------------------------------------------
    VPRINTF(LOW, "[LOCK_USE] Attempting AES KV key read from locked slot %d...\n", test_slot);
    lsu_write_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL,
                 AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_EN_MASK |
                 ((test_slot << AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_LOW) &
                  AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

    // Wait for valid
    while ((lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS) &
            AES_CLP_REG_AES_KV_RD_KEY_STATUS_VALID_MASK) == 0);

    status = lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS);
    error_field = (status & AES_CLP_REG_AES_KV_RD_KEY_STATUS_ERROR_MASK) >>
                  AES_CLP_REG_AES_KV_RD_KEY_STATUS_ERROR_LOW;
    VPRINTF(LOW, "[LOCK_USE] AES KV_RD_KEY_STATUS = 0x%08x (error_field = 0x%02x)\n",
            status, error_field);

    if (error_field == 0) {
        VPRINTF(ERROR, "[LOCK_USE_FAIL] Expected AES KV_READ_FAIL for lock_use slot!\n");
        pass = 0;
    } else {
        VPRINTF(LOW, "[LOCK_USE_PASS] AES read from lock_use slot correctly returned error=0x%02x\n",
                error_field);
    }

    // ------------------------------------------------------------------
    // Step 6: Verify lock_use is sticky (cannot be cleared by SW)
    // ------------------------------------------------------------------
    VPRINTF(LOW, "[LOCK_USE] Attempting to clear lock_use via SW (should fail — sticky)...\n");
    uint32_t clear_val = lsu_read_32(key_ctrl_addr) & ~KV_REG_KEY_CTRL_0_LOCK_USE_MASK;
    lsu_write_32(key_ctrl_addr, clear_val);
    key_ctrl_readback = lsu_read_32(key_ctrl_addr);
    VPRINTF(LOW, "[LOCK_USE] KEY_CTRL[%d] after clear attempt = 0x%08x\n",
            test_slot, key_ctrl_readback);

    if (key_ctrl_readback & KV_REG_KEY_CTRL_0_LOCK_USE_MASK) {
        VPRINTF(LOW, "[LOCK_USE_PASS] lock_use is sticky — cannot be cleared by SW\n");
    } else {
        VPRINTF(ERROR, "[LOCK_USE_FAIL] lock_use was cleared by SW! Not sticky!\n");
        pass = 0;
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

    // ---- TEST 4: KV lock_use Error Code Capture ----
    if (!test_kv_lock_use_error()) {
        VPRINTF(ERROR, "\n*** TEST 4 FAILED: KV lock_use Error Code ***\n");
        all_pass = 0;
    } else {
        VPRINTF(LOW, "\n*** TEST 4 PASSED: KV lock_use Error Code ***\n");
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
