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

#include "ifc_reg.h"
#include "caliptra_reg.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "string.h"
#include "stdint.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

#define ADDRESS_BITS_FOR_INDEXING 12   // 4096 possible indices
#define BITMAP_SIZE_WORDS ((1 << ADDRESS_BITS_FOR_INDEXING) / 32)

/* Global dictionary for expected register values */
ifc_reg_exp_dict_t g_expected_data_dict  __attribute__((section(".dccm.persistent")));
static register_mask_dict_t g_mask_dict  __attribute__((section(".dccm.persistent")));
// The bitmap array for register exclusions
static uint32_t excluded_registers_bitmap[BITMAP_SIZE_WORDS] __attribute__((section(".dccm.persistent")));

// Collision table to handle hash collisions - stores full register addresses
#define MAX_EXCLUDED_REGISTERS 4
static uint32_t collision_table[MAX_EXCLUDED_REGISTERS] __attribute__((section(".dccm.persistent"))) = {0};
static uint8_t collision_count __attribute__((section(".dccm.persistent"))) = 0;

/**
 * Read a 32-bit IFC register value
 *
 * @param reg_addr Register address
 * @return The register value
 */
uint32_t ifc_reg_read(uint32_t reg_addr) {
    return lsu_read_32(reg_addr);
}

/**
 * Write a 32-bit value to an IFC register
 *
 * @param reg_addr Register address
 * @param value Value to write
 */
void ifc_reg_write(uint32_t reg_addr, uint32_t value) {
    lsu_write_32(reg_addr, value);
}

bool is_ro(ifc_register_group_t group) {
    return (group == REG_GROUP_STRAPS_RO ||
        group == REG_GROUP_STATUS_RO ||
        group == REG_GROUP_SECURITY_RO ||
        group == REG_GROUP_WATCHDOG_RO ||
        group == REG_GROUP_CONTROL_RO ||
        group == REG_GROUP_GENERIC_WIRES_RO ||
        group == REG_GROUP_FUSE_RO ||
        group == REG_GROUP_OWNER_PK_HASH_RO ||
        group == REG_GROUP_UDS_RO ||
        group == REG_GROUP_FIELD_ENTROPY_RO ||
        group == REG_GROUP_VENDOR_PK_HASH_RO ||
        group == REG_GROUP_ECC_REVOCATION_RO ||
        group == REG_GROUP_SVN_RO ||
        group == REG_GROUP_ANTI_ROLLBACK_RO ||
        group == REG_GROUP_IDEVID_RO ||
        group == REG_GROUP_MANUF_DBG_UNLOCK_RO ||
        group == REG_GROUP_SOC_STEPPING_RO ||
        group == REG_GROUP_KEY_TYPE_RO ||
        group == REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO ||
        group == REG_GROUP_INTERRUPT_ERROR_COUNTERS_INCR_RO ||
        group == REG_GROUP_INTERRUPT_NOTIF_COUNTERS_INCR_RO);
}

uint32_t report_mismatch(ifc_register_group_t group, uint32_t id, uint32_t reg_addr, uint32_t read_data, uint32_t exp_data) {
    VPRINTF_LOW("No match: %s[%d] (0x%08x): Read 0x%08x, Expected 0x%08x\n", get_group_name(group), id, reg_addr, read_data, exp_data);
}

// Array of register with non-zero initial values
const ifc_reg_def_value_t reg_init_values[] = {
    {CLP_SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_L, 0xBA5EBA11},  // Set in caliptra_top_tb.sv
    {CLP_SOC_IFC_REG_CPTRA_SECURITY_STATE,    0x00000007},  // Base TB configuration is locked production
    {CLP_SOC_IFC_REG_CPTRA_FUSE_WR_DONE,      0x00000001},  // Register read post start, RO from CPTRA, RW from SoC
    {CLP_SOC_IFC_REG_FUSE_SOC_STEPPING_ID,    0x00000001},
    {CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0, 0xFFFFFFFF},
    {CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1, 0xFFFFFFFF},
    {CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2, 0xFFFFFFFF},
    {CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3, 0xFFFFFFFF},
    {CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_4, 0xFFFFFFFF},
    {CLP_SOC_IFC_REG_CPTRA_TRNG_VALID_AXI_USER,   0xFFFFFFFF},
    {CLP_SOC_IFC_REG_CPTRA_FUSE_VALID_AXI_USER,   0xFFFFFFFF},
    {CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0, 0xFFFFFFFF},
    {CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1, 0xFFFFFFFF},
    {CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0, 0xFFFFFFFF},
    {CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1, 0xFFFFFFFF},
    {CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES, 0x00000005}
};

/* Group structs*/

const ifc_register_info_t REG_GROUP_CAPABILITIES_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_HW_CAPABILITIES, REG_EXT_LOCK, false },
    { CLP_SOC_IFC_REG_CPTRA_FW_CAPABILITIES, REG_EXT_LOCK, false },
    { CLP_SOC_IFC_REG_CPTRA_CAP_LOCK, REG_SELF_LOCK_NON_ZERO, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_STRAPS_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_L, REG_EXT_LOCK_STICKY, true },
    { CLP_SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_H, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_SS_MCI_BASE_ADDR_L, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_SS_MCI_BASE_ADDR_H, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_H, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_L, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_H, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_L, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_H, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER, REG_EXT_LOCK_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_STRAPS_RO_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_SS_DEBUG_INTENT, REG_EXT_LOCK_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_STATUS_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_BOOT_STATUS, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_DBG_MANUF_SERVICE_REG, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_RSVD_REG_0, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_RSVD_REG_1, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_STATUS_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_RESET_REASON, REG_STICKY, false }, // bit 1 non sticky
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_SECURITY_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_SECURITY_STATE, REG_NOT_STICKY, true },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_ERROR_RW1C_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL, REG_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL, REG_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_ERROR_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_FW_ERROR_FATAL, REG_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_FW_ERROR_NON_FATAL, REG_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_HW_ERROR_ENC, REG_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_FW_ERROR_ENC, REG_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0, REG_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1, REG_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2, REG_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3, REG_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4, REG_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5, REG_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6, REG_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7, REG_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_ERROR_MASK_ARRAY [] = {
    { CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTERNAL_FW_ERROR_FATAL_MASK, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_WATCHDOG_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_EN, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0, REG_NOT_STICKY, true },
    { CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1, REG_NOT_STICKY, true },
    { CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_EN, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0, REG_NOT_STICKY, true },
    { CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1, REG_NOT_STICKY, true },
    { CLP_SOC_IFC_REG_CPTRA_WDT_CFG_0, REG_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_WDT_CFG_1, REG_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_WATCHDOG_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_WDT_STATUS, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_MCU_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_TIMER_CONFIG, REG_STICKY, false },
    { CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_L, REG_STICKY, false },
    { CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_H, REG_STICKY, false },
    { CLP_SOC_IFC_REG_INTERNAL_RV_MTIMECMP_L, REG_STICKY, false },
    { CLP_SOC_IFC_REG_INTERNAL_RV_MTIMECMP_H, REG_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_CONTROL_ARRAY [] = {
    { CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_CONTROL_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_CLK_GATING_EN, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_MBOX_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0, REG_EXT_LOCK, true },
    { CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1, REG_EXT_LOCK, true },
    { CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2, REG_EXT_LOCK, true },
    { CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3, REG_EXT_LOCK, true },
    { CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_4, REG_EXT_LOCK, true },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_MBOX_RW1S_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0, REG_SELF_LOCK_NON_ZERO, false },
    { CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1, REG_SELF_LOCK_NON_ZERO, false },
    { CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2, REG_SELF_LOCK_NON_ZERO, false },
    { CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3, REG_SELF_LOCK_NON_ZERO, false },
    { CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4, REG_SELF_LOCK_NON_ZERO, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_DBG_MANUF_SERVICE_ARRAY [] = {
    { CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ, REG_EXT_LOCK, false },
    { CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP, REG_EXT_LOCK, false },
    { CLP_SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_0, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_1, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_1, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_2, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_3, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_GENERIC_WIRES_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_GENERIC_WIRES_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_FW_ARRAY [] = {
    { CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES, REG_NOT_STICKY, true },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_FW_PULSE_RW1S_ARRAY [] = {
    { CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_TRNG_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_TRNG_VALID_AXI_USER, REG_EXT_LOCK, true },
    { CLP_SOC_IFC_REG_CPTRA_TRNG_STATUS, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_TRNG_RW1S_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK, REG_SELF_LOCK_NON_ZERO, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_TRNG_PULSE_RW1S_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_TRNG_CTRL, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_FUSE_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_FUSE_VALID_AXI_USER, REG_EXT_LOCK_STICKY, true },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_FUSE_RW1S_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK, REG_SELF_LOCK_NON_ZERO_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_FUSE_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, REG_EXT_LOCK_STICKY, true },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_OWNER_PK_HASH_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_1, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_2, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_3, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_4, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_5, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_6, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_7, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_8, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_9, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_10, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_11, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK, REG_SELF_LOCK_NON_ZERO_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_UDS_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_0, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_1, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_2, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_3, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_4, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_5, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_6, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_7, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_8, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_9, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_10, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_11, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_12, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_13, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_14, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_UDS_SEED_15, REG_EXT_LOCK_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_FIELD_ENTROPY_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_0, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_1, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_2, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_3, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_4, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_5, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_6, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_7, REG_EXT_LOCK_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_VENDOR_PK_HASH_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_1, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_2, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_3, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_4, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_5, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_6, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_7, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_8, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_9, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_10, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_11, REG_EXT_LOCK_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_ECC_REVOCATION_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_FUSE_ECC_REVOCATION, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_LMS_REVOCATION, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MLDSA_REVOCATION, REG_EXT_LOCK_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_SVN_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_FUSE_FMC_KEY_MANIFEST_SVN, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_RUNTIME_SVN_0, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_RUNTIME_SVN_1, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_RUNTIME_SVN_2, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_RUNTIME_SVN_3, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_0, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_1, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_2, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_3, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN, REG_EXT_LOCK_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_ANTI_ROLLBACK_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE,  REG_EXT_LOCK_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_IDEVID_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_1, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_2, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_3, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_4, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_5, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_6, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_7, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_8, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_9, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_10, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_11, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_12, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_13, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_14, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_15, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_16, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_17, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_18, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_19, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_20, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_21, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_22, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_23, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_0, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_1, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_2, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_3, REG_EXT_LOCK_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_MANUF_DBG_UNLOCK_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14, REG_EXT_LOCK_STICKY, false },
    { CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15, REG_EXT_LOCK_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_SOC_STEPPING_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_FUSE_SOC_STEPPING_ID, REG_EXT_LOCK_STICKY, true },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_KEY_TYPE_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_FUSE_PQC_KEY_TYPE, REG_EXT_LOCK_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_INTERRUPT_EN_ARRAY [] = {
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_INTERRUPT_STATUS_RW1C_ARRAY [] = {
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R, REG_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_INTERRUPT_TRIGGER_PULSE_RW1S_ARRAY [] = {
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_INTERRUPT_ERROR_COUNTERS_ARRAY [] = {
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R,           REG_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_R,            REG_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_R,           REG_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_R,           REG_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R,       REG_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R,       REG_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R, REG_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R, REG_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_INTERRUPT_NOTIF_COUNTERS_ARRAY [] = {
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R,     REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R,  REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R,  REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R,     REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_R,  REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_INTERRUPT_ERROR_COUNTERS_INCR_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};
const ifc_register_info_t REG_GROUP_INTERRUPT_NOTIF_COUNTERS_INCR_RO_ARRAY [] = {
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R, REG_NOT_STICKY, false },
    { 0, REG_NOT_STICKY, false }  // End marker
};

/* Array of register infos by group */
const ifc_register_info_t *register_groups[] = {
    REG_GROUP_CAPABILITIES_ARRAY,
    REG_GROUP_STRAPS_RO_ARRAY,
    REG_GROUP_STRAPS_RO_RO_ARRAY,
    REG_GROUP_STATUS_ARRAY,
    REG_GROUP_STATUS_RO_ARRAY,
    REG_GROUP_SECURITY_RO_ARRAY,
    REG_GROUP_ERROR_RW1C_ARRAY,
    REG_GROUP_ERROR_ARRAY,
    REG_GROUP_ERROR_MASK_ARRAY,
    REG_GROUP_WATCHDOG_ARRAY,
    REG_GROUP_WATCHDOG_RO_ARRAY,
    REG_GROUP_MCU_ARRAY,
    REG_GROUP_CONTROL_ARRAY,
    REG_GROUP_CONTROL_RO_ARRAY,
    REG_GROUP_MBOX_ARRAY,
    REG_GROUP_MBOX_RW1S_ARRAY,
    REG_GROUP_DBG_MANUF_SERVICE_ARRAY,
    REG_GROUP_GENERIC_WIRES_ARRAY,
    REG_GROUP_GENERIC_WIRES_RO_ARRAY,
    REG_GROUP_FW_ARRAY,
    REG_GROUP_FW_PULSE_RW1S_ARRAY,
    REG_GROUP_TRNG_ARRAY,
    REG_GROUP_TRNG_RW1S_ARRAY,
    REG_GROUP_TRNG_PULSE_RW1S_ARRAY,
    REG_GROUP_FUSE_ARRAY,
    REG_GROUP_FUSE_RW1S_ARRAY,
    REG_GROUP_FUSE_RO_ARRAY,
    REG_GROUP_OWNER_PK_HASH_RO_ARRAY,
    REG_GROUP_UDS_RO_ARRAY,
    REG_GROUP_FIELD_ENTROPY_RO_ARRAY,
    REG_GROUP_VENDOR_PK_HASH_RO_ARRAY,
    REG_GROUP_ECC_REVOCATION_RO_ARRAY,
    REG_GROUP_SVN_RO_ARRAY,
    REG_GROUP_ANTI_ROLLBACK_RO_ARRAY,
    REG_GROUP_IDEVID_RO_ARRAY,
    REG_GROUP_MANUF_DBG_UNLOCK_RO_ARRAY,
    REG_GROUP_SOC_STEPPING_RO_ARRAY,
    REG_GROUP_KEY_TYPE_RO_ARRAY,
    REG_GROUP_INTERRUPT_EN_ARRAY,
    REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO_ARRAY,
    REG_GROUP_INTERRUPT_STATUS_RW1C_ARRAY,
    REG_GROUP_INTERRUPT_TRIGGER_PULSE_RW1S_ARRAY,
    REG_GROUP_INTERRUPT_ERROR_COUNTERS_ARRAY,
    REG_GROUP_INTERRUPT_NOTIF_COUNTERS_ARRAY,
    REG_GROUP_INTERRUPT_ERROR_COUNTERS_INCR_RO_ARRAY,
    REG_GROUP_INTERRUPT_NOTIF_COUNTERS_INCR_RO_ARRAY
};

/* Function to get a string representation of a register group */
const char* get_group_name(ifc_register_group_t group) {
    switch(group) {
        case REG_GROUP_CAPABILITIES: return "Capabilities";
        case REG_GROUP_STRAPS_RO: return "Caliptra Straps RO";
        case REG_GROUP_STATUS: return "Status";
        case REG_GROUP_STATUS_RO: return "Status-RO";
        case REG_GROUP_SECURITY_RO: return "Security-RO";
        case REG_GROUP_ERROR_RW1C: return "Ftl/Non-Ftl err W1C";
        case REG_GROUP_ERROR: return "Ftl/Non-Ftl Err";
        case REG_GROUP_ERROR_MASK: return "Err Mask";
        case REG_GROUP_WATCHDOG: return "Watchdog";
        case REG_GROUP_WATCHDOG_RO: return "Watchdog-RO";
        case REG_GROUP_MCU: return "MCU";
        case REG_GROUP_CONTROL: return "Control";
        case REG_GROUP_CONTROL_RO: return "Control RO (Tap Access RW in Debug Mode)";
        case REG_GROUP_MBOX: return "IFC Mailbox AXI User";
        case REG_GROUP_MBOX_RW1S: return "IFC Mailbox AXI User Lock";
        case REG_GROUP_DBG_MANUF_SERVICE: return "Debug Services";
        case REG_GROUP_GENERIC_WIRES: return "Generic Wires";
        case REG_GROUP_GENERIC_WIRES_RO: return "Generic Wires - RO";
        case REG_GROUP_FW: return "FW Reset Cycles";
        case REG_GROUP_FW_PULSE_RW1S: return "FW Reset";
        case REG_GROUP_TRNG: return "TRNG control registers";
        case REG_GROUP_TRNG_RW1S: return "TRNG AXI User Lock";
        case REG_GROUP_FUSE: return "Fuse AXI User";
        case REG_GROUP_FUSE_RW1S: return "Fuse AXI User Lock";
        case REG_GROUP_FUSE_RO: return "Fuse Status - RO";
        case REG_GROUP_OWNER_PK_HASH_RO: return "Caliptra Owner PK Hash - RO";
        case REG_GROUP_UDS_RO: return "Unique Device Secret - RO";
        case REG_GROUP_FIELD_ENTROPY_RO: return "Field Entropy - RO";
        case REG_GROUP_VENDOR_PK_HASH_RO: return "Vendor PK Hash - RO";
        case REG_GROUP_ECC_REVOCATION_RO: return "ECC Revocation - RO";
        case REG_GROUP_SVN_RO: return "Security Version Number - RO";
        case REG_GROUP_ANTI_ROLLBACK_RO: return "Anti Rollback - RO";
        case REG_GROUP_IDEVID_RO: return "IDevID - RO";
        case REG_GROUP_MANUF_DBG_UNLOCK_RO: return "Manufacturing Debug Unlock Token - RO";
        case REG_GROUP_SOC_STEPPING_RO: return " SoC Stepping - RO";
        case REG_GROUP_KEY_TYPE_RO: return "PQC Key Type - RO";
        case REG_GROUP_INTERRUPT_EN: return "Intrpt Enable";
        case REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO: return "Intrpt Global Status RO";
        case REG_GROUP_INTERRUPT_STATUS_RW1C: return "Intrpt Status W1C";
        case REG_GROUP_INTERRUPT_TRIGGER_PULSE_RW1S: return "Intrpt Trigger Pulse W1S";
        case REG_GROUP_INTERRUPT_ERROR_COUNTERS: return "Err Intrpt Counters";
        case REG_GROUP_INTERRUPT_NOTIF_COUNTERS: return "Notif Intrpt Counters";
        case REG_GROUP_INTERRUPT_ERROR_COUNTERS_INCR_RO: return "Err Intrpt Counters Increment - RO";
        case REG_GROUP_INTERRUPT_NOTIF_COUNTERS_INCR_RO: return "Notif Intrpt Counters Increment - RO";
        default: return "Unknown";
    }
}

/* Get the number of registers in a group */
int get_register_count(ifc_register_group_t group) {
    int count = 0;

    if (group >= REG_GROUP_COUNT) {
        return 0;
    }

    while (register_groups[group][count].address != 0) {
        count++;
    }

    return count;
}

/* Get register information by its index within a group */
const ifc_register_info_t* get_register_info(ifc_register_group_t group, int index) {
    if (group >= REG_GROUP_COUNT) {
        return NULL;
    }

    if (index < 0 || index >= MAX_REGISTERS_PER_GROUP) {
        return NULL;
    }

    if (register_groups[group][index].address == 0) {
        return NULL;
    }

    return &register_groups[group][index];
}

/**
 * Function to find a register by address (across all groups)
 *
 * @param address Register address
 * @param group_index Pointer to store group index
 * @param reg_index Pointer to store register index
 * @return Register info pointer, or NULL if not found
 */
const ifc_register_info_t* find_register_by_address(uint32_t address,
                                                   ifc_register_group_t *group_index,
                                                   int *reg_index,
                                                   ifc_register_group_t start_index) {
    for (int group = start_index; group < REG_GROUP_COUNT; group++) {
        int count = get_register_count((ifc_register_group_t)group);

        for (int i = 0; i < count; i++) {
            const ifc_register_info_t *reg = get_register_info((ifc_register_group_t)group, i);

            if (reg && reg->address == address) {
                if (group_index) *group_index = (ifc_register_group_t)group;
                if (reg_index) *reg_index = i;
                return reg;
            }
        }
    }

    return NULL;

}

uint32_t exp_reg_group_interrupt_global_status_ro(uint32_t reg_id) {
        uint32_t exp_data;
        const ifc_register_info_t *intr0_reg;
        const ifc_register_info_t *intr1_reg;
        const ifc_register_info_t *intr0_en_reg;
        const ifc_register_info_t *intr1_en_reg;
        uint32_t read_intr0_sts;
        uint32_t read_intr1_sts;
        uint32_t read_intr0_en;
        uint32_t read_intr1_en;

        // ERROR/NOTIF global status = ERROR/NOTIF status & ERROR/NOTIF enable
        intr0_reg = get_register_info(REG_GROUP_INTERRUPT_STATUS_RW1C, reg_id);
        intr0_en_reg = get_register_info(REG_GROUP_INTERRUPT_EN, reg_id + 1); // ERROR_INTR_EN_R/NOTIF_INTR_EN_R

        read_intr0_sts = ifc_reg_read(intr0_reg->address);
        read_intr0_en = ifc_reg_read(intr0_en_reg->address);

        // Global status bit is set only if (status & enable) != 0
        if ((read_intr0_sts & read_intr0_en) != 0) {
            if (REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO_ARRAY[reg_id].address == CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R)
                exp_data = SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK;

            if (REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO_ARRAY[reg_id].address == CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R)
                exp_data = SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK;
        }

        return exp_data;
}

uint32_t exp_with_init_value(uint32_t reg_address) {
    uint32_t exp_data = 0;
    size_t init_array_size = sizeof(reg_init_values) / sizeof(reg_init_values[0]);
    for (size_t i = 0; i < init_array_size; i++) {
        if (reg_init_values[i].address == reg_address) {
            exp_data = reg_init_values[i].default_value;
            break;
        }
    }
    return exp_data;
}

/**
 * Function to calculate the total number of registers across all groups
 *
 * @return Total number of registers
 */
int get_total_register_count(void) {
    int total = 0;
    for (int group = 0; group < REG_GROUP_COUNT; group++) {
        total += get_register_count((ifc_register_group_t)group);
    }
    return total;
}

/**
 * Initialize the register expected data dictionary
 *
 * @param dict Pointer to dictionary to initialize
 */
void init_reg_exp_dict(ifc_reg_exp_dict_t *dict) {
    dict->count = 0;

    size_t init_array_size = sizeof(reg_init_values) / sizeof(reg_init_values[0]);
    // Add new entry if space available
    for (ifc_register_group_t group = 0; group < REG_GROUP_COUNT; group++) {
        int count = get_register_count(group);

        for (int i = 0; i < count; i++) {
            const ifc_register_info_t *reg = get_register_info(group, i);
            dict->entries[dict->count].address = reg->address;
            dict->entries[dict->count].expected_data = 0;
            if (reg->has_init_value) {
                dict->entries[dict->count].expected_data = exp_with_init_value(reg->address);
            }
            dict->count++;
        }
    }
}

/**
 * Add or update an entry in the register expected data dictionary
 *
 * @param dict Pointer to dictionary
 * @param address Register address (key)
 * @param value Expected data value
 * @param mask Mask to apply to the value
 * @param reg_write Write to W1C register
 * @param group_index_arg Register group index or -1, when >0 it improves speed
 * @param soc_access Access from SoC side, not Caliptra, some register become RW when accessed from SoC
 * @return 0 on success, -1 if dictionary is full
 */
 int set_reg_exp_data(ifc_reg_exp_dict_t *dict, uint32_t address, uint32_t value, uint32_t mask, bool reg_write, ifc_register_group_t group_index_arg, bool soc_access) {
    ifc_register_group_t group_index;
    int reg_index;
    const ifc_register_info_t *reg_info;
    const ifc_register_info_t *intr_glb_sts_reg;
    const ifc_register_info_t *intr_sts_reg;
    const ifc_register_info_t *axi_user_lock_reg;
    const ifc_register_info_t *cap_lock_reg;
    uint32_t glb_sts_mask;
    uint32_t intr_sts_mask;
    uint32_t err_data;
    uint32_t read_intr_sts;
    uint32_t axi_user_lock;
    uint32_t cap_lock_reg_value;
    bool ext_allowed = false;
    bool reset_reason_reg = false;
    bool update_exp_data = false;

    reg_info = find_register_by_address(address, &group_index, &reg_index, group_index_arg);
    if (group_index == REG_GROUP_ERROR_RW1C || group_index == REG_GROUP_INTERRUPT_STATUS_RW1C) {
        err_data = ifc_reg_read(address);
        if (reg_write) {
            value = err_data & ~value;
        }
    }

    if (group_index == REG_GROUP_INTERRUPT_TRIGGER_PULSE_RW1S) {
        intr_sts_reg = get_register_info(REG_GROUP_INTERRUPT_STATUS_RW1C, reg_index);
        read_intr_sts = ifc_reg_read(intr_sts_reg->address) | (value & mask);
        intr_sts_mask = get_register_mask(intr_sts_reg->address);

        if (reg_index == 0) {
            intr_glb_sts_reg = get_register_info(REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO, 0);
            glb_sts_mask = SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK;
        } else if (reg_index == 1) {
            intr_glb_sts_reg = get_register_info(REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO, 1);
            glb_sts_mask = SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK;
        }
    }

    if (group_index == REG_GROUP_MBOX) {
        axi_user_lock_reg = get_register_info(REG_GROUP_MBOX_RW1S, reg_index);
        axi_user_lock = ifc_reg_read(axi_user_lock_reg->address);
        if (axi_user_lock == 0) {
            ext_allowed = true;
        }
    }

    if (group_index == REG_GROUP_TRNG && reg_index == 0) {
        axi_user_lock_reg = get_register_info(REG_GROUP_TRNG_RW1S, reg_index);
        axi_user_lock = ifc_reg_read(axi_user_lock_reg->address);
        if (axi_user_lock == 0) {
            ext_allowed = true;
        }
    }

    if (group_index == REG_GROUP_FUSE) {
        axi_user_lock_reg = get_register_info(REG_GROUP_FUSE_RW1S, reg_index);
        axi_user_lock = ifc_reg_read(axi_user_lock_reg->address);
        if (axi_user_lock == 0) {
            ext_allowed = true;
        }
    }

    // Special case for capabilities registers - override the above conditions
    if (group_index == REG_GROUP_CAPABILITIES && reg_index <= 2) {
        cap_lock_reg = get_register_info(REG_GROUP_CAPABILITIES, 2);
        cap_lock_reg_value = ifc_reg_read(cap_lock_reg->address);
        ext_allowed = (cap_lock_reg_value == 0);
    }

    if (group_index == REG_GROUP_DBG_MANUF_SERVICE) {
        const ifc_register_info_t *debug_intent_reg = get_register_info(REG_GROUP_STRAPS_RO_RO, 0);
        bool debug_intent = ifc_reg_read(debug_intent_reg->address) & SOC_IFC_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK;
        if (reg_index == 0) {
            const ifc_register_info_t *sec_state_reg = get_register_info(REG_GROUP_SECURITY_RO, 0);
            if (debug_intent) {
                if ((ifc_reg_read(sec_state_reg->address) & SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK) == 1) {
                    mask |= 0x1;
                } else if ((ifc_reg_read(sec_state_reg->address) & SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK) == 3) {
                    mask |= 0x2;
                }
            }
            ext_allowed = true;
        } else if (reg_index == 1) {
            const ifc_register_info_t *sec_state_reg = get_register_info(REG_GROUP_SECURITY_RO, 0);
            const ifc_register_info_t *debug_rsp_reg = get_register_info(REG_GROUP_DBG_MANUF_SERVICE, 1);
            value |= (
                ifc_reg_read(debug_rsp_reg->address) & (
                    SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK |
                    SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_MASK
                )
            );
            if (debug_intent) {
                if ((ifc_reg_read(sec_state_reg->address) & SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK) == 1) {
                    mask |= 0x7;
                } else if ((ifc_reg_read(sec_state_reg->address) & SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK) == 3) {
                    mask |= 0x38;
                }
            }
            ext_allowed = true;
        } else if (debug_intent && (reg_index == 2 || reg_index == 3)) {
            ext_allowed = true;
        }
    }

    // Registers that are RW by SoC and RO by Caliptra(uC)
    if (soc_access && (
        group_index == REG_GROUP_STRAPS_RO            ||
        group_index == REG_GROUP_UDS_RO               ||
        group_index == REG_GROUP_FIELD_ENTROPY_RO     ||
        group_index == REG_GROUP_VENDOR_PK_HASH_RO    ||
        group_index == REG_GROUP_ECC_REVOCATION_RO    ||
        group_index == REG_GROUP_SVN_RO               ||
        group_index == REG_GROUP_ANTI_ROLLBACK_RO     ||
        group_index == REG_GROUP_IDEVID_RO            ||
        group_index == REG_GROUP_MANUF_DBG_UNLOCK_RO  ||
        group_index == REG_GROUP_SOC_STEPPING_RO      ||
        group_index == REG_GROUP_KEY_TYPE_RO          ||
        group_index == REG_GROUP_FUSE_RO
    )) {
        const ifc_register_info_t *fuse_locked = get_register_info(REG_GROUP_FUSE_RO, 0);
        ext_allowed = !(ifc_reg_read(fuse_locked->address) & 0x1);
    }
    if (soc_access && group_index == REG_GROUP_OWNER_PK_HASH_RO) {
        const ifc_register_info_t *fuse_locked = get_register_info(REG_GROUP_OWNER_PK_HASH_RO, 12);
        ext_allowed = !(ifc_reg_read(fuse_locked->address) & 0x1);
    }

    // Standard update condition
    if ((reg_info->is_sticky == REG_SELF_LOCK_NON_ZERO && ifc_reg_read(address) == 0) ||
        (reg_info->is_sticky == REG_SELF_LOCK_NON_ZERO_STICKY && ifc_reg_read(address) == 0) ||
        (reg_info->is_sticky != REG_CONFIG_DONE_STICKY && reg_info->is_sticky != REG_CONFIG_DONE &&
         reg_info->is_sticky != REG_SELF_LOCK_NON_ZERO_STICKY && reg_info->is_sticky != REG_EXT_LOCK_STICKY &&
         reg_info->is_sticky != REG_SELF_LOCK_NON_ZERO && reg_info->is_sticky != REG_EXT_LOCK) ||
        ext_allowed) {
        update_exp_data = true;
    }

    bool pulse_timer_reg = (address == CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL || address == CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL);
    bool pulse_intr_reg = (group_index == REG_GROUP_INTERRUPT_TRIGGER_PULSE_RW1S);

    // First check if entry already exists
    for (int i = 0; i < dict->count; i++) {
        if (dict->entries[i].address == address) {
            // Update existing entry's expected data only if sticky bit is NOT set
            if (update_exp_data) {
                if (!pulse_timer_reg && !pulse_intr_reg) {
                    dict->entries[i].expected_data = value & mask;
                } else if (pulse_timer_reg) {
                    dict->entries[i].expected_data = 0x0;
                } else {
                    dict->entries[i].expected_data = 0x0;
                    // Update expected data for corresponding interrupt status register
                    set_reg_exp_data(dict, intr_sts_reg->address, read_intr_sts, intr_sts_mask, false, 0, soc_access);
                    // Update global interrupt status register
                    set_reg_exp_data(dict, intr_glb_sts_reg->address, (1U << (glb_sts_mask - 1)), glb_sts_mask, false, 0, soc_access);
                }
            }
            // If sticky bit is set, retain previous expected value (do nothing)

            return 0; // Return after handling existing entry
        }
    }

    // Add new entry if space available
    if (dict->count < MAX_REGISTER_ENTRIES) {
        dict->entries[dict->count].address = address;
        if (!pulse_timer_reg && !pulse_intr_reg) {
            dict->entries[dict->count].expected_data = value & mask;
        } else if (pulse_timer_reg) {
            dict->entries[dict->count].expected_data = 0x0;
        }
        else {
            dict->entries[dict->count].expected_data = 0x0;
            // Update expected data for corresponding interrupt status register
            set_reg_exp_data(dict, intr_sts_reg->address, read_intr_sts, intr_sts_mask, false, 0, soc_access);
            // Update global interrupt status register
            set_reg_exp_data(dict, intr_glb_sts_reg->address, (1U << (glb_sts_mask - 1)), glb_sts_mask, false, 0, soc_access);
        }
        dict->count++;
        return 0;
    }

    return -1; // Dictionary full
}

/**
 * Get expected data for a register
 *
 * @param dict Pointer to dictionary
 * @param address Register address to lookup
 * @param value Pointer to store expected value
 * @return 0 if found, -1 if not found
 */
int get_reg_exp_data(ifc_reg_exp_dict_t *dict, uint32_t address, uint32_t *value) {
    for (int i = 0; i < dict->count; i++) {
        if (dict->entries[i].address == address) {
            if (value) {
                *value = dict->entries[i].expected_data;
            }
            return 0;
        }
    }

    return -1; // Not found
}

/**
 * Convert a register address to a bitmap index and bit position
 *
 * @param reg_addr Register address
 * @param word_index Pointer to store the word index in the bitmap
 * @param bit_position Pointer to store the bit position in the word
 */
static void address_to_bitmap_position(uint32_t reg_addr, uint32_t *word_index, uint32_t *bit_position) {
    // Use the lower bits of the address as a simple hash
    // This works because register addresses are typically aligned and spaced apart
    uint32_t hash_value = reg_addr & ((1 << ADDRESS_BITS_FOR_INDEXING) - 1);

    *word_index = hash_value / 32;
    *bit_position = hash_value % 32;
}

/**
 * Exclude a register by its address with collision handling
 *
 * @param reg_addr Register address to exclude
 * @return 0 on success, -1 if collision table is full
 */
int exclude_register(uint32_t reg_addr) {
    uint32_t word_index, bit_position;

    // Compute position in bitmap
    address_to_bitmap_position(reg_addr, &word_index, &bit_position);

    // Set the bit in the bitmap
    excluded_registers_bitmap[word_index] |= (1UL << bit_position);

    // Add to collision table
    if (collision_count < MAX_EXCLUDED_REGISTERS) {
        collision_table[collision_count++] = reg_addr;
        return 0;
    }

    // Collision table is full
    VPRINTF_WARNING("Collision table full, cannot add register 0x%08x\n", reg_addr);
    return -1;
}

/**
 * Check if a register is excluded with collision handling
 *
 * @param reg_addr Register address to check
 * @return 1 if excluded, 0 otherwise
 */
int is_register_excluded(uint32_t reg_addr) {
    uint32_t word_index, bit_position;

    // Compute position in bitmap
    address_to_bitmap_position(reg_addr, &word_index, &bit_position);

    // First, check the bit in the bitmap
    if (excluded_registers_bitmap[word_index] & (1UL << bit_position)) {
        // Potential match, verify in collision table to handle hash collisions
        for (int i = 0; i < collision_count; i++) {
            if (collision_table[i] == reg_addr) {
                return 1;  // Confirmed match in collision table
            }
        }
    }

    return 0;  // Not excluded
}

/**
 * Initialize the excluded registers bitmap
 */
void init_excluded_registers(void) {

    // Clear the bitmap and collision table
    memset(excluded_registers_bitmap, 0, sizeof(excluded_registers_bitmap));
    memset(collision_table, 0, sizeof(collision_table));
    collision_count = 0;
}


void write_random_to_register_group_and_track(ifc_register_group_t group, ifc_reg_exp_dict_t *dict) {
    int count = get_register_count(group);
    bool ro_reg = is_ro(group);

    for (int i = 0; i < count; i++) {
        const ifc_register_info_t *reg = get_register_info(group, i);

        if (!reg || is_register_excluded(reg->address)) continue;

        // Generate a unique value for each register
        uint32_t rand_value = xorshift32();

        /* Get mask for this register */
        uint32_t mask = get_register_mask(reg->address);

        // Store in dictionary
        if (!ro_reg) {
            set_reg_exp_data(dict, reg->address, rand_value, mask, true, group, false);
        }

        ifc_reg_write(reg->address, rand_value);
    }
}

void write_to_register_group_and_track(ifc_register_group_t group, uint32_t write_data, ifc_reg_exp_dict_t *dict) {
    int count = get_register_count(group);

    for (int i = 0; i < count; i++) {
        const ifc_register_info_t *reg = get_register_info(group, i);

        if (!reg || is_register_excluded(reg->address)) continue;

        /* Get mask for this register */
        uint32_t mask = get_register_mask(reg->address);

        // Store in dictionary
        set_reg_exp_data(dict, reg->address, write_data, mask, true, group, false);

        ifc_reg_write(reg->address, write_data);
    }
}

/**
 * Function to read all registers in a group and verify their values against expected data
 *
 * @param group Register group
 * @param dict Dictionary containing expected register values
 * @return Number of registers that failed verification
 */
int read_register_group_and_verify(ifc_register_group_t group, ifc_reg_exp_dict_t *dict, bool reset, reset_type_t reset_type, bool use_hw) {
    uint32_t read_data;
    int count = get_register_count(group);
    int mismatch_count = 0;
    uint32_t exp_data;
    uint32_t read_intr0_sts;
    uint32_t read_intr1_sts;
    uint32_t read_intr0_en;
    uint32_t read_intr1_en;
    const ifc_register_info_t *intr0_reg;
    const ifc_register_info_t *intr1_reg;
    const ifc_register_info_t *intr0_en_reg;
    const ifc_register_info_t *intr1_en_reg;

    bool ro_reg = is_ro(group);

    for (int i = 0; i < count; i++) {
        const ifc_register_info_t *reg = get_register_info(group, i);

        if (!reg) {
            VPRINTF_ERROR("Register index %d not found in group\n", i);
            continue;
        }

        // Skip excluded registers with collision-aware check
        if (is_register_excluded(reg->address)) {
            continue;
        }

        // Read the register value
        read_data = ifc_reg_read(reg->address);
        if (group == REG_GROUP_UDS_RO && use_hw) {
            const ifc_register_info_t *cmd_reg = get_register_info(REG_GROUP_GENERIC_WIRES, 0);
            const ifc_register_info_t *rsp_reg0 = get_register_info(REG_GROUP_GENERIC_WIRES_RO, 0);
            const ifc_register_info_t *rsp_reg1 = get_register_info(REG_GROUP_GENERIC_WIRES_RO, 1);
            ifc_reg_write(cmd_reg->address, 0x207F | ((i << 7) & 0xF00));
            read_data = i & 1 ? ifc_reg_read(rsp_reg0->address): ifc_reg_read(rsp_reg1->address);
        }
        if (group == REG_GROUP_FIELD_ENTROPY_RO && use_hw) {
            const ifc_register_info_t *cmd_reg = get_register_info(REG_GROUP_GENERIC_WIRES, 0);
            const ifc_register_info_t *rsp_reg0 = get_register_info(REG_GROUP_GENERIC_WIRES_RO, 0);
            const ifc_register_info_t *rsp_reg1 = get_register_info(REG_GROUP_GENERIC_WIRES_RO, 1);
            ifc_reg_write(cmd_reg->address, 0x307F | ((i << 7) & 0xF00));
            read_data = i & 1 ? ifc_reg_read(rsp_reg0->address): ifc_reg_read(rsp_reg1->address);
        }

        // Get expected data from dictionary
        if (reset) {
            if (reset_type == COLD_RESET) {
                if (reg->has_init_value == true) {
                    exp_data =  exp_with_init_value(reg->address);
                    if (read_data == exp_data) {
                        continue;
                    } else {
                        report_mismatch(group, i, reg->address, read_data, exp_data);
                        mismatch_count++;
                    }
                } else if (ro_reg == false) {
                    exp_data  = 0;
                    if (reg->address == CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_H || reg->address == CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_L && read_data >= exp_data) {
                        continue;
                    } else if (read_data == exp_data) {
                        continue;
                    } else if (reg->address == CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R) {
                        if (ifc_reg_read(CLP_SOC_IFC_REG_CPTRA_SECURITY_STATE) & SOC_IFC_REG_CPTRA_SECURITY_STATE_DEBUG_LOCKED_MASK) {
                            exp_data |= SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK;
                        }
                        if (ifc_reg_read(CLP_SOC_IFC_REG_CPTRA_SECURITY_STATE) & SOC_IFC_REG_CPTRA_SECURITY_STATE_SCAN_MODE_MASK) {
                            exp_data |= SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_MASK;
                        }
                        if (read_data == exp_data) {
                            continue;
                        } else {
                            mismatch_count++;
                        }
                    } else if (reg->address == CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS) {
                        exp_data |= 4 << 25; //uC out of reset, so BOOTFSM is in DONE state
                        if (read_data == exp_data) {
                            continue;
                        } else {
                            mismatch_count++;
                        }
                    } else {
                        report_mismatch(group, i, reg->address, read_data, exp_data);
                        mismatch_count++;
                    }
                } else {
                    if (get_reg_exp_data(&g_expected_data_dict, reg->address, &exp_data) == 0) {
                        if (read_data == exp_data) {
                            continue;
                        } else if (group == REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO) {
                            exp_data = exp_reg_group_interrupt_global_status_ro(i);
                            if (read_data == exp_data) {
                                continue;
                            }
                            else {
                                report_mismatch(group, i, reg->address, read_data, exp_data);
                                mismatch_count++;
                            }
                        } else {
                            report_mismatch(group, i, reg->address, read_data, exp_data);
                            mismatch_count++;
                        }
                    } else {
                        VPRINTF_ERROR("%s[%d] (0x%08x): Read 0x%08x, No expected data in dictionary\n",
                                get_group_name(group), i, reg->address, read_data);
                    }
                }
            } else if (reset_type == WARM_RESET) {
                if (reg->is_sticky == REG_STICKY || reg->is_sticky == REG_CONFIG_DONE_STICKY || reg->is_sticky == REG_SELF_LOCK_NON_ZERO_STICKY || reg->is_sticky == REG_EXT_LOCK_STICKY) {
                    if (get_reg_exp_data(&g_expected_data_dict, reg->address, &exp_data) == 0) {
                        // Compare and report
                        if (group == REG_GROUP_INTERRUPT_ERROR_COUNTERS) {
                            if ((i == 0 && (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK)) ||
                                (i == 1 && (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK)) ||
                                (i == 2 && (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK)) ||
                                (i == 3 && (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK)) ||
                                (i == 4 && (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_MASK)) ||
                                (i == 5 && (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK)) ||
                                (i == 6 && (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK)) ||
                                (i == 7 && (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK))) {
                                if (read_data >= exp_data) {
                                    continue;
                                } else {
                                    report_mismatch(group, i, reg->address, read_data, exp_data);
                                    mismatch_count++;
                                }
                            }
                        } else if (reg->address == CLP_SOC_IFC_REG_CPTRA_RESET_REASON) {
                            exp_data = exp_data | SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK; // bit 1 is not sticky
                            if (read_data == exp_data) {
                                continue;
                            } else {
                                report_mismatch(group, i, reg->address, read_data, exp_data);
                                mismatch_count++;
                            }
                        } else if (read_data == exp_data) {
                                continue;
                        } else if (read_data > exp_data && reg->address == CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_H || reg->address == CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_L) {
                                continue;
                        } else {
                            report_mismatch(group, i, reg->address, read_data, exp_data);
                            mismatch_count++;
                        }
                    } else {
                        VPRINTF_ERROR("%s[%d] (0x%08x): Read 0x%08x, No expected data in dictionary\n",
                                get_group_name(group), i, reg->address, read_data);
                    }
                } else {
                    if (reg->has_init_value == true) {
                        exp_data =  exp_with_init_value(reg->address);
                        if (read_data == exp_data) {
                            continue;
                        } else {
                            report_mismatch(group, i, reg->address, read_data, exp_data);
                            mismatch_count++;
                        }
                    } else if (ro_reg == false) {
                        exp_data  = 0;

                        if (read_data == exp_data) {
                        } else if (group == REG_GROUP_INTERRUPT_NOTIF_COUNTERS) {
                            if ((i == 0 &&  (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK)) ||
                                (i == 1 &&  (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK)) ||
                                (i == 2 &&  (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK)) ||
                                (i == 3 &&  (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_MASK)) ||
                                (i == 4 &&  (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SOC_REQ_LOCK_STS_MASK)) ||
                                (i == 5 &&  (ifc_reg_read(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK))) {
                                if (read_data >= exp_data) {
                                    continue;
                                } else {
                                    report_mismatch(group, i, reg->address, read_data, exp_data);
                                    mismatch_count++;
                                }
                            }
                        } else if (reg->address == CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS) {
                            exp_data |= 4 << 25; //uC out of reset, so BOOTFSM is in DONE state
                            if (read_data == exp_data) {
                                continue;
                            } else {
                                report_mismatch(group, i, reg->address, read_data, exp_data);
                                mismatch_count++;
                            }
                        } else {
                            report_mismatch(group, i, reg->address, read_data, exp_data);
                            mismatch_count++;
                        }
                    } else {
                        if (get_reg_exp_data(&g_expected_data_dict, reg->address, &exp_data) == 0) {
                            if (read_data == exp_data) {
                                continue;
                            } else if (group == REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO) {
                                exp_data = exp_reg_group_interrupt_global_status_ro(i);
                                if (read_data == exp_data) {
                                    continue;
                                }
                                else {
                                    report_mismatch(group, i, reg->address, read_data, exp_data);
                                    mismatch_count++;
                                }
                            } else {
                                report_mismatch(group, i, reg->address, read_data, exp_data);
                                mismatch_count++;
                            }
                        } else {
                            VPRINTF_ERROR("%s[%d] (0x%08x): Read 0x%08x, No expected data in dictionary\n", get_group_name(group), i, reg->address, read_data);
                        }
                    }
                }
            }
        } else { // Verifying after a write operation
            if (get_reg_exp_data(&g_expected_data_dict, reg->address, &exp_data) == 0) {
                // Compare and report
                if (read_data == exp_data) {
                    continue;
                } else if (read_data > exp_data && reg->address == CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_H || reg->address == CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_L) {
                    continue;
                } else if (reg->address == CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS) {
                    exp_data |= 4 << 25; //uC out of reset, so BOOTFSM is in DONE state
                    if (read_data == exp_data) {
                        continue;
                    } else {
                        report_mismatch(group, i, reg->address, read_data, exp_data);
                        mismatch_count++;
                    }
                } else if (group == REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO) {
                    exp_data = exp_reg_group_interrupt_global_status_ro(i);
                    if (read_data == exp_data) {
                        continue;
                    } else {
                        report_mismatch(group, i, reg->address, read_data, exp_data);
                        mismatch_count++;
                    }
                } else {
                    report_mismatch(group, i, reg->address, read_data, exp_data);
                    mismatch_count++;
                }
            } else {
                VPRINTF_ERROR("%s[%d] (0x%08x): Read 0x%08x, No expected data in dictionary\n", get_group_name(group), i, reg->address, read_data);
            }
        }
    }

    VPRINTF_LOW("Verification complete: %d register(s) matched, %d register(s) mismatched\n", count - mismatch_count, mismatch_count);
    return mismatch_count;
}

/**
 * Function to read all registers in a group and track their values in a dictionary
 *
 * @param group Register group
 * @param dict Dictionary to store register values
 */
void read_register_group_and_track(ifc_register_group_t group, ifc_reg_exp_dict_t *dict) {
    uint32_t read_data;
    int count = get_register_count(group);
    for (int i = 0; i < count; i++) {
        const ifc_register_info_t *reg = get_register_info(group, i);
        if (!reg) continue;

        // Check if this register should be excluded
        if (!is_register_excluded(reg->address)) {
            // Read the register value
            read_data = ifc_reg_read(reg->address);

            /* Get mask for this register */
            uint32_t mask = get_register_mask(reg->address);

            // Store in dictionary
            if (set_reg_exp_data(dict, reg->address, read_data, mask, false, group, false) != 0) {
                VPRINTF_WARNING("Could not store read data for %s[%d]\n", get_group_name(group), i);
            }
        }
    }

    VPRINTF_LOW("Register tracking complete: %d register(s) read and tracked\n", count);
}


void init_mask_dict(void) {
    g_mask_dict.count = 0;

    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_CAP_LOCK,
            SOC_IFC_REG_CPTRA_CAP_LOCK_LOCK_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS,
            SOC_IFC_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_MASK |
            SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK |
            SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK |
            SOC_IFC_REG_CPTRA_FLOW_STATUS_IDEVID_CSR_READY_MASK |
            SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_EN,
            SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_EN,
            SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK,
            SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0,
            SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1,
            SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2,
            SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3,
            SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4,
            SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4_LOCK_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS,
            SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_MASK |
            SOC_IFC_REG_CPTRA_FLOW_STATUS_IDEVID_CSR_READY_MASK |
            SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK |
            SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK |
            SOC_IFC_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES,
            SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES_WAIT_CYCLES_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK,
            SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_ICCM_ECC_UNC_MASK |
            SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_DCCM_ECC_UNC_MASK |
            SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK,
            SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_NO_LOCK_MASK |
            SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_OOO_MASK |
            SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_ECC_UNC_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_TRNG_STATUS,
            SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_REQ_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK,
            SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK_LOCK_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK,
            SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK_LOCK_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ, 0);
    add_mask_entry(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP,
            SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK |
            SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_MASK |
            SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK |
            SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_TRNG_CTRL, SOC_IFC_REG_CPTRA_TRNG_CTRL_CLEAR_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK,
            SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK_LOCK_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_FUSE_ECC_REVOCATION,
            SOC_IFC_REG_FUSE_ECC_REVOCATION_ECC_REVOCATION_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_FUSE_MLDSA_REVOCATION,
            SOC_IFC_REG_FUSE_MLDSA_REVOCATION_MLDSA_REVOCATION_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN,
            SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN_SVN_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE,
            SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_FUSE_SOC_STEPPING_ID,
            SOC_IFC_REG_FUSE_SOC_STEPPING_ID_SOC_STEPPING_ID_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_FUSE_PQC_KEY_TYPE,
            SOC_IFC_REG_FUSE_PQC_KEY_TYPE_KEY_TYPE_MASK);
    add_mask_entry(CLP_SOC_IFC_REG_CPTRA_FUSE_WR_DONE,
            SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
}

/**
 * Add an entry to the register mask dictionary
 *
 * @param address Register address
 * @param mask Combined mask for the register
 * @return 0 on success, -1 if dictionary is full
 */
int add_mask_entry(uint32_t address, uint32_t mask) {
    if (g_mask_dict.count < MAX_REGISTER_ENTRIES) {
        g_mask_dict.entries[g_mask_dict.count].address = address;
        g_mask_dict.entries[g_mask_dict.count].combined_mask = mask;
        g_mask_dict.count++;
        return 0;
    }
    return -1;
}

/**
 * Get the combined mask for a register
 *
 * @param address Register address
 * @return Combined mask, or 0xFFFFFFFF if not found
 */
uint32_t get_register_mask(uint32_t address) {
    for (int i = 0; i < g_mask_dict.count; i++) {
        if (g_mask_dict.entries[i].address == address) {
            return g_mask_dict.entries[i].combined_mask;
        }
    }

    /* Default mask for unknown registers */
    return 0xFFFFFFFF;
}

/**
 * Initialize IFC module
 */
void ifc_init(void) {
    // Initialize register mask dictionary if not already done
    static int masks_initialized = 0;
    if (!masks_initialized) {
        init_mask_dict();
        masks_initialized = 1;
    }

    // Initialize expected data dictionary
    init_reg_exp_dict(&g_expected_data_dict);

    // Initialize excluded registers
    init_excluded_registers();
}
