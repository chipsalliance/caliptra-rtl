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
//   Shared library for KV boot flow monitor tests. Provides common defines,
//   helper functions, and DICE slot population routines used across the
//   smoke test, enforcement test, ICCM region test, and negative test.

#ifndef KV_BOOT_FLOW_H
#define KV_BOOT_FLOW_H

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"
#include <stdint.h>

// ============================================================
// KV slot assignments (from caliptra-sw KeyId)
// ============================================================
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

// Conditional slots (preserved only when corresponding mode is active)
#define KV_SLOT_STABLE_OWNER 15
#define KV_SLOT_MDK          16   // OCP Lock RT obfuscation key
#define KV_SLOT_HEK          22   // OCP Lock HEK seed
#define KV_SLOT_MEK          23   // OCP Lock key release (always cleared)
#define KV_SLOT_CANARY_STD   10   // Standard-range canary (always cleared)
#define KV_SLOT_CANARY_OCP   17   // OCP-range canary (always cleared)

// ============================================================
// dest_valid bit masks (from HMAC KV_WR_CTRL register fields)
// ============================================================
#define DV_HMAC_KEY    HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK
#define DV_MLDSA_SEED  HMAC_REG_HMAC512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK
#define DV_ECC_PKEY    HMAC_REG_HMAC512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK
#define DV_ECC_SEED    HMAC_REG_HMAC512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK
#define DV_AES_KEY     HMAC_REG_HMAC512_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK

// Expected dest_valid combos per slot (must match KV_EXPECTED_DV_* in kv.sv)
#define DV_CDI         (DV_HMAC_KEY | DV_MLDSA_SEED | DV_ECC_SEED)

// ============================================================
// KV KEY_CTRL register access helpers
// ============================================================
#define KV_KEY_CTRL(slot)  (CLP_KV_REG_KEY_CTRL_0 + ((slot) * 4))
#define KV_LOCK_WR_MASK    KV_REG_KEY_CTRL_0_LOCK_WR_MASK
#define KV_LOCK_USE_MASK   KV_REG_KEY_CTRL_0_LOCK_USE_MASK
#define KV_DEST_VALID_MASK KV_REG_KEY_CTRL_0_DEST_VALID_MASK
#define KV_DEST_VALID_LOW  KV_REG_KEY_CTRL_0_DEST_VALID_LOW

// Number of KV entries
#define KV_NUM_KEYS       16
#define KV_NUM_KEYS_TOTAL 24

// ============================================================
// ICCM region addresses
// ============================================================

// Absolute addresses
#define FMC_ICCM_ADDR  RV_ICCM_SADR            // 0x40000000
#define RT_ICCM_ADDR   (RV_ICCM_SADR + 0x8000) // 0x40008000

// 18-bit ICCM-relative addresses (for region registers)
#define FMC_ICCM_START_REL 0x00000
#define FMC_ICCM_END_REL   0x07FFF
#define RT_ICCM_START_REL  0x08000
#define RT_ICCM_END_REL    0x3C7FF

// ============================================================
// TB service commands
// ============================================================
#define TB_CMD_ENABLE_KV_BOOT_FLOW_MONITOR 0xbb
#define TB_CMD_COLD_RESET                  0xf5
#define TB_CMD_WARM_RESET                  0xf6

// ============================================================
// Shadow register error masks
// (bit positions from soc_ifc_external_reg.rdl)
// ============================================================
#define SHADOW_STORAGE_ERR_MASK (1 << 5)  // CPTRA_HW_ERROR_FATAL bit 5
#define SHADOW_UPDATE_ERR_MASK  (1 << 3)  // CPTRA_HW_ERROR_NON_FATAL bit 3

// ============================================================
// Function prototypes
// ============================================================

// Run a dummy HMAC384 operation and write the result to a KV slot
// with the specified dest_valid bits. Polls for completion (no ISR needed).
void hmac_write_kv_slot(uint8_t slot, uint32_t dest_valid_mask);

// Populate all ROM-phase DICE key slots with correct dest_valid
// and write counts (slot 6: 4 writes, slot 7: 2, slot 8: 2).
void populate_dice_slots(void);

// Populate RT-phase key slots (called from FMC).
void populate_rt_slots(void);

// Program all 4 ICCM region registers with 2-phase shadow protocol
// and set the lock.
void program_iccm_regions(void);

// 2-phase commit only (no lock). Use when you need to write after commit.
void commit_iccm_shadows(void);

// Set the ICCM region lock register.
void lock_iccm_region(void);

// Verify a register reads back a specific value.
void check_reg(const char *name, uint32_t addr, uint32_t expected);

// Verify all 4 ICCM address registers and lock are zero (after warm reset).
void verify_regs_reset(void);

// Verify ICCM region registers have the expected programmed values.
void verify_regs_programmed(void);

// Verify CPTRA_HW_ERROR_FATAL.kv_error is NOT set.
void check_no_kv_error(const char *phase);

// Verify CPTRA_HW_ERROR_FATAL.kv_error IS set and W1C clear it.
void check_and_clear_kv_error(const char *phase);

// Verify lock_wr is set on the given slot.
void check_lock_wr(uint8_t slot, const char *phase);

// Verify lock_use is set on the given slot.
void check_lock_use(uint8_t slot, const char *phase);

// Verify a slot was cleared (dest_valid == 0).
void check_slot_cleared(uint8_t slot, const char *phase);

// Verify DOE is locked: write a command and confirm it doesn't execute.
void check_doe_locked(const char *phase);

// Copy code from LMA storage to an ICCM destination address.
void copy_to_iccm(uint32_t dest, uint32_t *lma_start, uint32_t *lma_end);

// Read CPTRA_HW_CONFIG and SS_STRAP_GENERIC_3 to compute stable_owner_key_en
// and ocp_lock_mode_en at runtime.
void compute_conditional_enables(uint32_t *stable_owner_key_en, uint32_t *ocp_lock_mode_en);

// Populate conditional slots: stable owner (15), OCP Lock (16, 22, 23),
// and canary slots (10, 17) for clear verification.
void populate_conditional_slots(void);

// Check conditional slot preservation/clearing after a boot transition.
// phase: "FMC" or "RT" for logging.
void check_conditional_slots(uint32_t stable_owner_key_en, uint32_t ocp_lock_mode_en,
                             const char *phase);

// Verify a slot was preserved (dest_valid != 0).
void check_slot_preserved(uint8_t slot, const char *phase);

#endif // KV_BOOT_FLOW_H
