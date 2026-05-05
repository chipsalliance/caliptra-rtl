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
//   Negative test for KV boot flow monitor. Each iteration deliberately
//   injects one fault (dest_valid or write count) and verifies the monitor fires:
//
//   Iteration 0: Skip slot 0 (UDS) -- leave empty
//   Iteration 1: Slot 0 with wrong dest_valid (HMAC_KEY instead of AES_KEY)
//   Iteration 2: Skip slot 6 (FMC_CDI) -- leave empty
//   Iteration 3: Slot 2 (Key Ladder) with wrong dest_valid (AES_KEY instead of HMAC_KEY)
//   Iteration 4: FMC-to-RT fault -- skip slot 4 (RT_CDI)
//   Iteration 5: FMC-to-RT fault -- slot 9 (RT_MLDSA) wrong dest_valid
//   Iteration 6: Slot 7 write count too low (1 instead of >=2, skip FMC Alias ECC)
//   Iteration 7: Slot 8 write count too low (1 instead of >=2, skip FMC Alias MLDSA)
//
//   Each iteration:
//     1. Populate slots (with one deliberate fault)
//     2. Jump to FMC (or FMC jumps to RT for iterations 4-5)
//     3. Monitor fires -> kv_error set, KV flushed
//     4. Read back CPTRA_HW_ERROR_FATAL to confirm kv_error
//     5. Issue warm reset via TB service (clears cptra_error_fatal)
//     6. After reset: W1C the sticky kv_error bit, continue to next iteration

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

// Iteration counter -- persists across warm resets (DCCM not cleared)
volatile uint32_t iter __attribute__((section(".dccm.persistent"))) = 0;
// Flag set by FMC to tell RT to inject its fault and jump
volatile uint32_t fmc_to_rt_fault __attribute__((section(".dccm.persistent"))) = 0;

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
#define TB_CMD_ENABLE_KV_BOOT_FLOW_MONITOR 0xa1
#define TB_CMD_WARM_RESET                  0xf6

// KV KEY_CTRL register access
#define KV_KEY_CTRL(slot) (CLP_KV_REG_KEY_CTRL_0 + ((slot) * 4))

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

#define NUM_ITERATIONS 8

//
// Run a dummy HMAC384 operation and write the result to a KV slot
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

    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL,
        HMAC_REG_HMAC512_CTRL_INIT_MASK |
        (HMAC384_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));

    while (cptra_intr_rcv.hmac_notif == 0) {
        __asm__ volatile ("wfi");
    }
}

//
// Populate ROM-phase KV slots for the given iteration.
// Must produce the correct write counts for slots 6/7/8 (4/2/2) except
// when the fault specifically targets those slots.
// Returns 1 if the fault is injected at ROM-to-FMC, 0 if at FMC-to-RT.
//
// Helper: perform the full DICE write sequence for slots 6/7/8
static void dice_writes_slot678(void) {
    // Slot 6 write 1: IDevID CDI
    hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);
    // Slot 7 write 1: IDevID ECC keygen
    hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);
    // Slot 8 write 1: IDevID MLDSA keygen
    hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED);
    // Slot 6 write 2: LDEV intermediate
    hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_HMAC_KEY);
    // Slot 6 write 3: LDEV CDI
    hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);
    // Slot 7 write 2: FMC Alias ECC keygen
    hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);
    // Slot 8 write 2: FMC Alias MLDSA keygen
    hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED);
    // Slot 6 write 4: FMC Alias CDI
    hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);
}

int populate_rom_slots(uint32_t iteration) {
    switch (iteration) {
    case 0:
        // Skip slot 0 (UDS) entirely -- monitor expects AES_KEY
        VPRINTF(LOW, "  Fault: skipping slot 0 (UDS)\n");
        /* slot 0 omitted */
        hmac_write_kv_slot(KV_SLOT_SI_LDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_KEY_LADDER, DV_HMAC_KEY);
        dice_writes_slot678();
        return 1;

    case 1:
        // Slot 0 with wrong dest_valid (HMAC_KEY instead of AES_KEY)
        VPRINTF(LOW, "  Fault: slot 0 wrong dest_valid (HMAC_KEY)\n");
        hmac_write_kv_slot(KV_SLOT_SI_IDEV,    DV_HMAC_KEY);  // WRONG
        hmac_write_kv_slot(KV_SLOT_SI_LDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_KEY_LADDER, DV_HMAC_KEY);
        dice_writes_slot678();
        return 1;

    case 2:
        // Skip slot 6 (FMC_CDI) -- monitor expects CDI dest_valid AND write count >= 4
        VPRINTF(LOW, "  Fault: skipping slot 6 (FMC_CDI)\n");
        hmac_write_kv_slot(KV_SLOT_SI_IDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_SI_LDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_KEY_LADDER, DV_HMAC_KEY);
        /* slot 6 omitted -- write count stays 0 */
        hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);
        hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED);
        hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);
        hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED);
        return 1;

    case 3:
        // Slot 2 (Key Ladder) with wrong dest_valid (AES_KEY instead of HMAC_KEY)
        VPRINTF(LOW, "  Fault: slot 2 wrong dest_valid (AES_KEY)\n");
        hmac_write_kv_slot(KV_SLOT_SI_IDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_SI_LDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_KEY_LADDER, DV_AES_KEY);   // WRONG
        dice_writes_slot678();
        return 1;

    case 4:
    case 5:
        // FMC-to-RT faults: ROM slots are correct, fault injected in FMC
        VPRINTF(LOW, "  ROM slots correct -- fault at FMC-to-RT\n");
        hmac_write_kv_slot(KV_SLOT_SI_IDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_SI_LDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_KEY_LADDER, DV_HMAC_KEY);
        dice_writes_slot678();
        return 0;

    case 6:
        // Slot 7 write count=1 (skip FMC Alias ECC keygen, expect >=2)
        VPRINTF(LOW, "  Fault: slot 7 write count=1 (skip FMC Alias ECC)\n");
        hmac_write_kv_slot(KV_SLOT_SI_IDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_SI_LDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_KEY_LADDER, DV_HMAC_KEY);
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);        // slot 6 write 1
        hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);   // slot 7 write 1
        hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED); // slot 8 write 1
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_HMAC_KEY);   // slot 6 write 2
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);        // slot 6 write 3
        /* slot 7 write 2 SKIPPED -- count stays at 1 */
        hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED); // slot 8 write 2
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);        // slot 6 write 4
        return 1;

    case 7:
        // Slot 8 write count=1 (skip FMC Alias MLDSA keygen, expect >=2)
        VPRINTF(LOW, "  Fault: slot 8 write count=1 (skip FMC Alias MLDSA)\n");
        hmac_write_kv_slot(KV_SLOT_SI_IDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_SI_LDEV,    DV_AES_KEY);
        hmac_write_kv_slot(KV_SLOT_KEY_LADDER, DV_HMAC_KEY);
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);        // slot 6 write 1
        hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);   // slot 7 write 1
        hmac_write_kv_slot(KV_SLOT_FMC_MLDSA, DV_MLDSA_SEED); // slot 8 write 1
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_HMAC_KEY);   // slot 6 write 2
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);        // slot 6 write 3
        hmac_write_kv_slot(KV_SLOT_FMC_ECDSA, DV_ECC_PKEY);   // slot 7 write 2
        /* slot 8 write 2 SKIPPED -- count stays at 1 */
        hmac_write_kv_slot(KV_SLOT_FMC_CDI,   DV_CDI);        // slot 6 write 4
        return 1;

    default:
        return 1;
    }
}

//
// Check that kv_error IS set (expected violation) and issue warm reset
//
void confirm_violation_and_reset(const char *phase, uint32_t iteration) {
    uint32_t hw_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
    if (!(hw_err & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK)) {
        VPRINTF(ERROR, "[FAIL] iter %d %s: kv_error NOT set (reg=0x%08x)\n", iteration, phase, hw_err);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  iter %d %s: kv_error=1 confirmed (reg=0x%08x) -- issuing warm reset\n",
            iteration, phase, hw_err);

    // Issue warm reset via TB service -- clears cptra_error_fatal
    SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
    // Should not reach here
    while(1);
}

void main() {
    init_interrupts();

    // Enable boot flow monitoring (needed after every reset)
    SEND_STDOUT_CTRL(TB_CMD_ENABLE_KV_BOOT_FLOW_MONITOR);

    VPRINTF(LOW, "============================================\n");
    VPRINTF(LOW, " KV Monitor Negative Test -- iter %d of %d\n", iter, NUM_ITERATIONS);
    VPRINTF(LOW, "============================================\n");

    // After warm reset, the sticky kv_error bit persists (resets on cptra_pwrgood only).
    // W1C it so that a stale bit from the previous iteration doesn't confuse us.
    uint32_t stale_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
    if (stale_err & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK) {
        VPRINTF(LOW, "  Clearing stale kv_error from previous iteration\n");
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL,
                     SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK);
    }

    if (iter >= NUM_ITERATIONS) {
        // All iterations passed
        VPRINTF(LOW, "============================================\n");
        VPRINTF(LOW, " All %d negative iterations passed\n", NUM_ITERATIONS);
        VPRINTF(LOW, "============================================\n");
        SEND_STDOUT_CTRL(0xff);
        return;
    }

    // Determine if this is first boot (need to copy ICCM) or subsequent
    if (iter == 0) {
        // First iteration: copy FMC and RT code to ICCM
        uint32_t *fmc_dest = (uint32_t *)FMC_ICCM_ADDR;
        uint32_t *code_word = (uint32_t *)&iccm_code0_start;
        while (code_word < (uint32_t *)&iccm_code0_end) {
            *fmc_dest++ = *code_word++;
        }
        uint32_t *rt_dest = (uint32_t *)RT_ICCM_ADDR;
        code_word = (uint32_t *)&iccm_code1_start;
        while (code_word < (uint32_t *)&iccm_code1_end) {
            *rt_dest++ = *code_word++;
        }
    }

    // Populate ROM-phase slots with the iteration's fault injected
    VPRINTF(LOW, "ROM: Populating slots for iter %d\n", iter);
    int fault_at_rom_to_fmc = populate_rom_slots(iter);

    // Set flag for FMC-to-RT fault iterations
    fmc_to_rt_fault = fault_at_rom_to_fmc ? 0 : 1;

    // Advance iteration counter BEFORE jumping (in case monitor fires and we reset)
    uint32_t current_iter = iter;
    iter++;

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

    // Jump to FMC -- if fault is at ROM-to-FMC, the monitor fires on this transition
    VPRINTF(LOW, "ROM: Jumping to FMC (iter %d)...\n", current_iter);
    void (*fmc_fn)(void) = (void (*)(void))FMC_ICCM_ADDR;
    fmc_fn();

    // If we get here on a ROM-to-FMC fault iteration, the monitor didn't fire
    if (fault_at_rom_to_fmc) {
        VPRINTF(ERROR, "[FAIL] iter %d: monitor did not fire at ROM-to-FMC\n", current_iter);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
}

// FMC entry point
void fmc_entry(void) {
    uint32_t current_iter = iter - 1;  // iter was pre-incremented

    if (fmc_to_rt_fault) {
        // ROM-to-FMC passed (correct). Now inject fault for FMC-to-RT.
        VPRINTF(LOW, "FMC: ROM-to-FMC monitor passed (correct for iter %d)\n", current_iter);

        // Populate RT slots with the appropriate fault
        switch (current_iter) {
        case 4:
            // Skip slot 4 (RT_CDI)
            VPRINTF(LOW, "  FMC fault: skipping slot 4 (RT_CDI)\n");
            /* slot 4 omitted */
            hmac_write_kv_slot(KV_SLOT_RT_ECDSA, DV_ECC_PKEY);
            hmac_write_kv_slot(KV_SLOT_RT_MLDSA, DV_MLDSA_SEED);
            break;
        case 5:
            // Slot 9 (RT_MLDSA) wrong dest_valid
            VPRINTF(LOW, "  FMC fault: slot 9 wrong dest_valid (AES_KEY)\n");
            hmac_write_kv_slot(KV_SLOT_RT_CDI,   DV_CDI);
            hmac_write_kv_slot(KV_SLOT_RT_ECDSA, DV_ECC_PKEY);
            hmac_write_kv_slot(KV_SLOT_RT_MLDSA, DV_AES_KEY);  // WRONG
            break;
        }

        // Jump to RT -- monitor should fire at FMC-to-RT
        VPRINTF(LOW, "FMC: Jumping to RT (iter %d)...\n", current_iter);
        void (*rt_fn)(void) = (void (*)(void))RT_ICCM_ADDR;
        rt_fn();

        // If we return here, the monitor didn't fire
        VPRINTF(ERROR, "[FAIL] iter %d: monitor did not fire at FMC-to-RT\n", current_iter);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    } else {
        // ROM-to-FMC fault: we should have gotten kv_error already
        // (The monitor fires on the transition, but CPU keeps running)
        VPRINTF(LOW, "FMC: Checking for ROM-to-FMC violation (iter %d)\n", current_iter);
        confirm_violation_and_reset("ROM-to-FMC", current_iter);
    }
}

// RT entry point
void rt_entry(void) {
    uint32_t current_iter = iter - 1;
    // FMC-to-RT fault: check for violation
    VPRINTF(LOW, "RT: Checking for FMC-to-RT violation (iter %d)\n", current_iter);
    confirm_violation_and_reset("FMC-to-RT", current_iter);
}
