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

// ICCM region addresses (absolute)
#define FMC_ICCM_ADDR  RV_ICCM_SADR            // 0x40000000
#define RT_ICCM_ADDR   (RV_ICCM_SADR + 0x8000) // 0x40008000

// ICCM region addresses (18-bit ICCM-relative, for region registers)
#define FMC_ICCM_START_REL 0x00000
#define FMC_ICCM_END_REL   0x07FFF
#define RT_ICCM_START_REL  0x08000
#define RT_ICCM_END_REL    0x3C7FF

// TB command to enable KV boot flow monitoring
#define TB_CMD_ENABLE_KV_BOOT_FLOW_MONITOR 0xbb
// TB command to issue warm reset
#define TB_CMD_WARM_RESET 0xf6

// KV KEY_CTRL register access helpers (4-byte stride per entry)
#define KV_KEY_CTRL(slot) (CLP_KV_REG_KEY_CTRL_0 + ((slot) * 4))
#define KV_LOCK_WR_MASK   KV_REG_KEY_CTRL_0_LOCK_WR_MASK
#define KV_LOCK_USE_MASK  KV_REG_KEY_CTRL_0_LOCK_USE_MASK
#define KV_DEST_VALID_MASK KV_REG_KEY_CTRL_0_DEST_VALID_MASK
#define KV_DEST_VALID_LOW  KV_REG_KEY_CTRL_0_DEST_VALID_LOW

// KV slot assignments (from caliptra-sw KeyId)
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

// dest_valid bit masks matching KV_DEST_IDX_* in kv_defines_pkg.sv
#define DV_HMAC_KEY    HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK
#define DV_MLDSA_SEED  HMAC_REG_HMAC512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK
#define DV_ECC_PKEY    HMAC_REG_HMAC512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK
#define DV_ECC_SEED    HMAC_REG_HMAC512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK
#define DV_AES_KEY     HMAC_REG_HMAC512_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK

// Expected dest_valid combos per slot (must match KV_EXPECTED_DV_* in kv.sv)
#define DV_CDI         (DV_HMAC_KEY | DV_MLDSA_SEED | DV_ECC_SEED)

// Number of KV entries
#define KV_NUM_KEYS 16

//
// Verify that CPTRA_HW_ERROR_FATAL.kv_error is NOT set
//
void check_no_kv_error(const char *phase) {
    uint32_t hw_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
    if (hw_err & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK) {
        VPRINTF(ERROR, "[FAIL] %s: CPTRA_HW_ERROR_FATAL.kv_error=1 (reg=0x%08x)\n", phase, hw_err);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: CPTRA_HW_ERROR_FATAL kv_error=0 -- OK (reg=0x%08x)\n", phase, hw_err);
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
        VPRINTF(ERROR, "[FAIL] %s: slot %d not cleared (dest_valid=0x%03x, ctrl=0x%08x)\n", phase, slot, dv, ctrl);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: slot %d cleared -- OK\n", phase, slot);
}

//
// Verify DOE is locked: write a command and confirm it doesn't execute
//
void check_doe_locked(const char *phase) {
    // Attempt to issue a DOE UDS decrypt command (cmd=1, dest=KV slot 0)
    lsu_write_32(CLP_DOE_REG_DOE_CTRL,
                 (1 << DOE_REG_DOE_CTRL_CMD_LOW) |
                 (0 << DOE_REG_DOE_CTRL_DEST_LOW));

    // If doe_cmd_lock is working, the hwclr zeroes the cmd immediately.
    // Engine should remain idle: ready=1 (never started), valid=0 (no result).
    uint32_t status = lsu_read_32(CLP_DOE_REG_DOE_STATUS);
    if (!(status & DOE_REG_DOE_STATUS_READY_MASK)) {
        VPRINTF(ERROR, "[FAIL] %s: DOE went busy after locked cmd write (status=0x%08x)\n", phase, status);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    if (status & DOE_REG_DOE_STATUS_VALID_MASK) {
        VPRINTF(ERROR, "[FAIL] %s: DOE produced result after locked cmd write (status=0x%08x)\n", phase, status);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }

    // Confirm the cmd register itself was cleared by hwclr
    uint32_t ctrl = lsu_read_32(CLP_DOE_REG_DOE_CTRL);
    if (ctrl & DOE_REG_DOE_CTRL_CMD_MASK) {
        VPRINTF(ERROR, "[FAIL] %s: DOE cmd not cleared by hwclr (ctrl=0x%08x)\n", phase, ctrl);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: DOE cmd rejected (ready=1 valid=0 cmd=0) -- OK\n", phase);
}

//
// Run a dummy HMAC384 operation and write the result to a KV slot
// with the specified dest_valid bits.
//
void hmac_write_kv_slot(uint8_t slot, uint32_t dest_valid_mask) {
    uint32_t *reg;

    // Wait for HMAC ready
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    // Write dummy key (12 dwords for HMAC384)
    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_KEY_0;
    for (int i = 0; i <= (CLP_HMAC_REG_HMAC512_KEY_11 - CLP_HMAC_REG_HMAC512_KEY_0) / 4; i++) {
        lsu_write_32((uintptr_t)(reg + i), 0xDEADBE00 + i);
    }

    // Write dummy block (32 dwords)
    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0;
    for (int i = 0; i <= (CLP_HMAC_REG_HMAC512_BLOCK_31 - CLP_HMAC_REG_HMAC512_BLOCK_0) / 4; i++) {
        lsu_write_32((uintptr_t)(reg + i), 0xCAFE0000 + i);
    }

    // Write LFSR seed
    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_LFSR_SEED_0;
    for (int i = 0; i <= (CLP_HMAC_REG_HMAC512_LFSR_SEED_11 - CLP_HMAC_REG_HMAC512_LFSR_SEED_0) / 4; i++) {
        lsu_write_32((uintptr_t)(reg + i), 0xA5A50000 + i);
    }

    // Configure KV write: target slot + specific dest_valid bits
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL,
        HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
        ((slot << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
         HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK) |
        dest_valid_mask);

    // Clear any previous HMAC notif
    cptra_intr_rcv.hmac_notif = 0;

    // Kick off HMAC384 INIT
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL,
        HMAC_REG_HMAC512_CTRL_INIT_MASK |
        (HMAC384_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));

    // Wait for HMAC completion via interrupt
    while (cptra_intr_rcv.hmac_notif == 0) {
        __asm__ volatile ("wfi");
    }

    VPRINTF(LOW, "  KV slot %d populated (dest_valid_mask=0x%x)\n", slot, dest_valid_mask);
}

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

        // Mimic ROM DICE derivation -- populate KV slots with correct dest_valid
        // Must match real ROM write counts for write counter monitor:
        //   Slot 6: 4 writes (IDevID CDI, LDEV intermediate, LDEV CDI, FMC Alias CDI)
        //   Slot 7: 2 writes (IDevID ECC keygen, FMC Alias ECC keygen)
        //   Slot 8: 2 writes (IDevID MLDSA keygen, FMC Alias MLDSA keygen)
        VPRINTF(LOW, "ROM: Populating DICE key slots...\n");
        hmac_write_kv_slot(KV_SLOT_SI_IDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_SI_LDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_KEY_LADDER, DV_HMAC_KEY);
        // Slot 6 write 1: IDevID CDI
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);
        // Slot 7 write 1: IDevID ECC keygen
        hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);
        // Slot 8 write 1: IDevID MLDSA keygen
        hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED);
        // Slot 6 write 2: LDEV intermediate (HMAC_KEY only)
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_HMAC_KEY);
        // Slot 6 write 3: LDEV CDI
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);
        // Slot 7 write 2: FMC Alias ECC keygen
        hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);
        // Slot 8 write 2: FMC Alias MLDSA keygen
        hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED);
        // Slot 6 write 4: FMC Alias CDI
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);

        // Copy FMC function to FMC region of ICCM
        uint32_t *fmc_dest = (uint32_t *)FMC_ICCM_ADDR;
        uint32_t *code_word = (uint32_t *)&iccm_code0_start;
        VPRINTF(LOW, "ROM: Copying FMC code to 0x%x\n", (uintptr_t)fmc_dest);
        while (code_word < (uint32_t *)&iccm_code0_end) {
            *fmc_dest++ = *code_word++;
        }

        // Copy RT function to RT region of ICCM
        uint32_t *rt_dest = (uint32_t *)RT_ICCM_ADDR;
        code_word = (uint32_t *)&iccm_code1_start;
        VPRINTF(LOW, "ROM: Copying RT code to 0x%x\n", (uintptr_t)rt_dest);
        while (code_word < (uint32_t *)&iccm_code1_end) {
            *rt_dest++ = *code_word++;
        }
    } else if (is_warm) {
        // ============================================================
        // Boot 1: Warm reset -- full DICE re-derivation required
        // ============================================================
        boot_count = 1;
        VPRINTF(LOW, "============================================\n");
        VPRINTF(LOW, " Boot 1: Warm Reset\n");
        VPRINTF(LOW, "============================================\n");

        // Warm reset: KV slots persist but enforcement clears locks.
        // Write counters persist (hard_reset_b only resets them).
        // ROM must re-derive DICE keys to exercise the full boot flow.
        VPRINTF(LOW, "ROM: Warm reset -- re-deriving DICE keys...\n");
        hmac_write_kv_slot(KV_SLOT_SI_IDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_SI_LDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_KEY_LADDER, DV_HMAC_KEY);
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);
        hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);
        hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED);
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_HMAC_KEY);
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);
        hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);
        hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED);
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);

        // ICCM content persists across warm reset -- re-copy for safety
        uint32_t *fmc_dest = (uint32_t *)FMC_ICCM_ADDR;
        uint32_t *code_word = (uint32_t *)&iccm_code0_start;
        VPRINTF(LOW, "ROM: Re-copying FMC code to ICCM\n");
        while (code_word < (uint32_t *)&iccm_code0_end) {
            *fmc_dest++ = *code_word++;
        }
        uint32_t *rt_dest = (uint32_t *)RT_ICCM_ADDR;
        code_word = (uint32_t *)&iccm_code1_start;
        VPRINTF(LOW, "ROM: Re-copying RT code to ICCM\n");
        while (code_word < (uint32_t *)&iccm_code1_end) {
            *rt_dest++ = *code_word++;
        }
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

    // Program ICCM region registers with 2-phase shadow protocol.
    // Each address register must be written twice (same value) to commit the
    // shadow checker. The boot flow monitor requires all shadows committed
    // before the effective lock is recognized.
    VPRINTF(LOW, "ROM: Programming ICCM region registers (phase 0)\n");
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, FMC_ICCM_START_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR,   FMC_ICCM_END_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_START_ADDR,  RT_ICCM_START_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_END_ADDR,    RT_ICCM_END_REL);
    VPRINTF(LOW, "ROM: Programming ICCM region registers (phase 1 -- commit)\n");
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, FMC_ICCM_START_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR,   FMC_ICCM_END_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_START_ADDR,  RT_ICCM_START_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_END_ADDR,    RT_ICCM_END_REL);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_REGION_LOCK,    0x1);

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
    hmac_write_kv_slot(KV_SLOT_RT_CDI,   DV_CDI);
    hmac_write_kv_slot(KV_SLOT_RT_ECDSA, DV_ECC_PKEY);
    hmac_write_kv_slot(KV_SLOT_RT_MLDSA, DV_MLDSA_SEED);

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
