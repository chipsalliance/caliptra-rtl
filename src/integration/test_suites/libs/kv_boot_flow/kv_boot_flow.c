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
//   Implementation of shared KV boot flow monitor test helpers.

#include "kv_boot_flow.h"
#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"
#include "printf.h"

//
// Run a dummy HMAC384 operation and write the result to a KV slot
// with the specified dest_valid bits. Polls STATUS.VALID for completion.
//
void hmac_write_kv_slot(uint8_t slot, uint32_t dest_valid_mask) {
    uint32_t *reg;

    // Wait for HMAC ready
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) &
            HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    // Write dummy key (12 dwords for HMAC384)
    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_KEY_0;
    for (int i = 0;
         i <= (CLP_HMAC_REG_HMAC512_KEY_11 - CLP_HMAC_REG_HMAC512_KEY_0) / 4;
         i++) {
        lsu_write_32((uintptr_t)(reg + i), 0xDEADBE00 + i);
    }

    // Write dummy block (32 dwords)
    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0;
    for (int i = 0;
         i <= (CLP_HMAC_REG_HMAC512_BLOCK_31 - CLP_HMAC_REG_HMAC512_BLOCK_0) / 4;
         i++) {
        lsu_write_32((uintptr_t)(reg + i), 0xCAFE0000 + i);
    }

    // Write LFSR seed
    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_LFSR_SEED_0;
    for (int i = 0;
         i <= (CLP_HMAC_REG_HMAC512_LFSR_SEED_5 - CLP_HMAC_REG_HMAC512_LFSR_SEED_0) / 4;
         i++) {
        lsu_write_32((uintptr_t)(reg + i), 0xA5A50000 + i);
    }

    // Configure KV write: target slot + specific dest_valid bits
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL,
        HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
        ((slot << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
         HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK) |
        dest_valid_mask);

    // Kick off HMAC384 INIT
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL,
        HMAC_REG_HMAC512_CTRL_INIT_MASK |
        (HMAC384_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));

    // Poll for HMAC completion (STATUS.VALID)
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) &
            HMAC_REG_HMAC512_STATUS_VALID_MASK) == 0);

    VPRINTF(LOW, "  KV slot %d populated (dest_valid_mask=0x%x)\n",
            slot, dest_valid_mask);
}

//
// Populate all ROM-phase DICE key slots with correct dest_valid and write counts.
//   Slot 6: 4 writes (IDevID CDI, LDEV intermediate, LDEV CDI, FMC Alias CDI)
//   Slot 7: 2 writes (IDevID ECC keygen, FMC Alias ECC keygen)
//   Slot 8: 2 writes (IDevID MLDSA keygen, FMC Alias MLDSA keygen)
//
void populate_dice_slots(void) {
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
}

//
// Populate RT-phase key slots (called from FMC).
//
void populate_rt_slots(void) {
    hmac_write_kv_slot(KV_SLOT_RT_CDI,   DV_CDI);
    hmac_write_kv_slot(KV_SLOT_RT_ECDSA, DV_ECC_PKEY);
    hmac_write_kv_slot(KV_SLOT_RT_MLDSA, DV_MLDSA_SEED);
}

//
// Program all 4 ICCM region registers with 2-phase shadow protocol and set lock.
//
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

//
// Verify a register reads back a specific value.
//
void check_reg(const char *name, uint32_t addr, uint32_t expected) {
    uint32_t val = lsu_read_32(addr);
    if (val != expected) {
        VPRINTF(ERROR, "[FAIL] %s: got=0x%08x expected=0x%08x\n",
                name, val, expected);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  CHECK OK: %s = 0x%08x\n", name, val);
}

//
// Verify all ICCM region registers are zero (after warm reset).
//
void verify_regs_reset(void) {
    check_reg("FMC_START", CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR, 0);
    check_reg("FMC_END",   CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR,   0);
    check_reg("RT_START",  CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_START_ADDR,  0);
    check_reg("RT_END",    CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_END_ADDR,    0);
    check_reg("LOCK",      CLP_SOC_IFC_REG_INTERNAL_ICCM_REGION_LOCK,    0);
}

//
// Verify ICCM region registers have the expected programmed values.
//
void verify_regs_programmed(void) {
    check_reg("FMC_START", CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_START_ADDR,
              FMC_ICCM_START_REL);
    check_reg("FMC_END",   CLP_SOC_IFC_REG_INTERNAL_ICCM_FMC_END_ADDR,
              FMC_ICCM_END_REL);
    check_reg("RT_START",  CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_START_ADDR,
              RT_ICCM_START_REL);
    check_reg("RT_END",    CLP_SOC_IFC_REG_INTERNAL_ICCM_RT_END_ADDR,
              RT_ICCM_END_REL);
    check_reg("LOCK",      CLP_SOC_IFC_REG_INTERNAL_ICCM_REGION_LOCK, 1);
}

//
// Verify CPTRA_HW_ERROR_FATAL.kv_error is NOT set.
//
void check_no_kv_error(const char *phase) {
    uint32_t hw_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
    if (hw_err & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK) {
        VPRINTF(ERROR, "[FAIL] %s: CPTRA_HW_ERROR_FATAL.kv_error=1 "
                "(reg=0x%08x)\n", phase, hw_err);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: kv_err=0 -- OK (reg=0x%08x)\n", phase, hw_err);
}

//
// Verify CPTRA_HW_ERROR_FATAL.kv_error IS set and W1C clear it.
//
void check_and_clear_kv_error(const char *phase) {
    uint32_t hw_err = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL);
    if (!(hw_err & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK)) {
        VPRINTF(ERROR, "[FAIL] %s: expected kv_error but got 0x%08x\n",
                phase, hw_err);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: kv fault confirmed (0x%08x) -- W1C clearing\n",
            phase, hw_err);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL,
                 SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK);
}

//
// Verify lock_wr is set on the given slot.
//
void check_lock_wr(uint8_t slot, const char *phase) {
    uint32_t ctrl = lsu_read_32(KV_KEY_CTRL(slot));
    if (!(ctrl & KV_LOCK_WR_MASK)) {
        VPRINTF(ERROR, "[FAIL] %s: slot %d lock_wr not set (ctrl=0x%08x)\n",
                phase, slot, ctrl);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: slot %d lock_wr=1 -- OK\n", phase, slot);
}

//
// Verify lock_use is set on the given slot.
//
void check_lock_use(uint8_t slot, const char *phase) {
    uint32_t ctrl = lsu_read_32(KV_KEY_CTRL(slot));
    if (!(ctrl & KV_LOCK_USE_MASK)) {
        VPRINTF(ERROR, "[FAIL] %s: slot %d lock_use not set (ctrl=0x%08x)\n",
                phase, slot, ctrl);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: slot %d lock_use=1 -- OK\n", phase, slot);
}

//
// Verify a slot was cleared (dest_valid == 0).
//
void check_slot_cleared(uint8_t slot, const char *phase) {
    uint32_t ctrl = lsu_read_32(KV_KEY_CTRL(slot));
    uint32_t dv = (ctrl & KV_DEST_VALID_MASK) >> KV_DEST_VALID_LOW;
    if (dv != 0) {
        VPRINTF(ERROR, "[FAIL] %s: slot %d not cleared "
                "(dest_valid=0x%03x, ctrl=0x%08x)\n", phase, slot, dv, ctrl);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: slot %d cleared -- OK\n", phase, slot);
}

//
// Verify DOE is locked: write a command and confirm it doesn't execute.
// Note: DOE_STATUS.VALID may be 1 from boot-time DOE flows (UDS/FE decrypt),
// which is expected and not checked here.
//
void check_doe_locked(const char *phase) {
    // Attempt to issue a DOE UDS decrypt command (cmd=1, dest=KV slot 0)
    lsu_write_32(CLP_DOE_REG_DOE_CTRL,
                 (1 << DOE_REG_DOE_CTRL_CMD_LOW) |
                 (0 << DOE_REG_DOE_CTRL_DEST_LOW));

    // Engine should remain idle: ready=1 (swwel blocked the write)
    uint32_t status = lsu_read_32(CLP_DOE_REG_DOE_STATUS);
    if (!(status & DOE_REG_DOE_STATUS_READY_MASK)) {
        VPRINTF(ERROR, "[FAIL] %s: DOE went busy after locked cmd write "
                "(status=0x%08x)\n", phase, status);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }

    // Confirm the cmd register itself was cleared by hwclr
    uint32_t ctrl = lsu_read_32(CLP_DOE_REG_DOE_CTRL);
    if (ctrl & DOE_REG_DOE_CTRL_CMD_MASK) {
        VPRINTF(ERROR, "[FAIL] %s: DOE cmd not cleared by hwclr "
                "(ctrl=0x%08x)\n", phase, ctrl);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: DOE cmd rejected (ready=1 cmd=0) -- OK\n", phase);
}

//
// Copy code from LMA storage to an ICCM destination address.
//
void copy_to_iccm(uint32_t dest, uint32_t *lma_start, uint32_t *lma_end) {
    uint32_t *dst = (uint32_t *)dest;
    uint32_t *src = lma_start;
    while (src < lma_end) {
        *dst++ = *src++;
    }
}

//
// Read CPTRA_HW_CONFIG and SS_STRAP_GENERIC_3 to determine conditional enables.
// Mirrors the RTL logic in soc_ifc_top.sv:
//   stable_owner_key_en = SUBSYSTEM_MODE_en & ~OCP_LOCK_MODE_en & SS_STRAP_GENERIC_3[0]
//   ocp_lock_mode_en = OCP_LOCK_MODE_en (only meaningful when SUBSYSTEM_MODE_en)
//
void compute_conditional_enables(uint32_t *stable_owner_key_en, uint32_t *ocp_lock_mode_en) {
    uint32_t hw_config = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
    uint32_t ss_mode = (hw_config & SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK) != 0;
    uint32_t ocp_lock = (hw_config & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK) != 0;
    uint32_t strap3 = lsu_read_32(CLP_SOC_IFC_REG_SS_STRAP_GENERIC_3);
    uint32_t strap3_bit0 = strap3 & 0x1;

    *ocp_lock_mode_en = ocp_lock;
    *stable_owner_key_en = ss_mode && !ocp_lock && strap3_bit0;

    VPRINTF(LOW, "  Conditional enables: ss_mode=%d ocp_lock=%d strap3[0]=%d "
            "=> stable_owner_key_en=%d ocp_lock_mode_en=%d\n",
            ss_mode, ocp_lock, strap3_bit0, *stable_owner_key_en, *ocp_lock_mode_en);
}

//
// Populate conditional slots for preservation testing.
// Writes HMAC results to: slot 15 (stable owner), 16 (MDK), 22 (HEK), 23 (MEK),
// and canary slots 10 (standard) and 17 (OCP range).
//
void populate_conditional_slots(void) {
    VPRINTF(LOW, "  Populating conditional + canary slots...\n");
    hmac_write_kv_slot(KV_SLOT_CANARY_STD,   DV_AES_KEY);
    hmac_write_kv_slot(KV_SLOT_STABLE_OWNER, DV_AES_KEY);
    hmac_write_kv_slot(KV_SLOT_MDK,          DV_AES_KEY);
    hmac_write_kv_slot(KV_SLOT_CANARY_OCP,   DV_AES_KEY);
    hmac_write_kv_slot(KV_SLOT_HEK,          DV_AES_KEY);
    hmac_write_kv_slot(KV_SLOT_MEK,          DV_AES_KEY);
}

//
// Verify a slot was preserved (dest_valid != 0).
//
void check_slot_preserved(uint8_t slot, const char *phase) {
    uint32_t ctrl = lsu_read_32(KV_KEY_CTRL(slot));
    uint32_t dv = (ctrl & KV_DEST_VALID_MASK) >> KV_DEST_VALID_LOW;
    if (dv == 0) {
        VPRINTF(FATAL, "[FAIL] %s: slot %d was cleared but should be preserved "
                "(ctrl=0x%08x)\n", phase, slot, ctrl);
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "  %s: slot %d preserved (dest_valid=0x%03x) -- OK\n", phase, slot, dv);
}

//
// Check conditional slot preservation/clearing after a boot transition.
//
void check_conditional_slots(uint32_t stable_owner_key_en, uint32_t ocp_lock_mode_en,
                             const char *phase) {
    VPRINTF(LOW, "%s: Checking conditional slots (stable_owner=%d, ocp_lock=%d)\n",
            phase, stable_owner_key_en, ocp_lock_mode_en);

    // Slot 15 (Stable Owner Key)
    if (stable_owner_key_en) {
        check_slot_preserved(KV_SLOT_STABLE_OWNER, phase);
    } else {
        check_slot_cleared(KV_SLOT_STABLE_OWNER, phase);
    }

    // Slots 16 (MDK) and 22 (HEK) -- OCP Lock slots
    if (ocp_lock_mode_en) {
        check_slot_preserved(KV_SLOT_MDK, phase);
        check_slot_preserved(KV_SLOT_HEK, phase);
    } else {
        check_slot_cleared(KV_SLOT_MDK, phase);
        check_slot_cleared(KV_SLOT_HEK, phase);
    }

    // Slot 23 (MEK) -- ALWAYS cleared regardless of ocp_lock
    check_slot_cleared(KV_SLOT_MEK, phase);

    // Canary slots -- ALWAYS cleared
    check_slot_cleared(KV_SLOT_CANARY_STD, phase);
    check_slot_cleared(KV_SLOT_CANARY_OCP, phase);

    VPRINTF(LOW, "%s: Conditional slot checks passed\n", phase);
}
