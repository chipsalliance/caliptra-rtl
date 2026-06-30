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


#ifndef IFC_REG_H
#define IFC_REG_H

#include <stdbool.h>
#include "stdint.h"
#include <stddef.h>
#include "caliptra_rtl_lib.h"

// IFC Register Count: 261/270
#define MAX_REGISTER_ENTRIES 270

// Maximum number of registers in any group
#define MAX_REGISTERS_PER_GROUP 29

// Enum for register sticky behavior
typedef enum {
    REG_NOT_STICKY = 0,
    REG_STICKY = 1,
    REG_CONFIG_DONE_STICKY = 2,
    REG_CONFIG_DONE = 3,
    REG_SELF_LOCK_NON_ZERO = 4,
    REG_SELF_LOCK_NON_ZERO_STICKY = 5,
    REG_EXT_LOCK = 6,
    REG_EXT_LOCK_STICKY = 7
} register_sticky_t;


// Register info struct
typedef struct {
    uint32_t address;   /* Register address */
    register_sticky_t is_sticky;        /* Flag to indicate if register is sticky */
    uint8_t has_init_value:1; /* Single bit */
} ifc_register_info_t;

// Register expected data struct
typedef struct {
    uint32_t address;         // Address of the register instead of name
    uint32_t expected_data;   // Expected data value
} ifc_register_exp_data_t;

// Dictionary of register expected values
typedef struct {
    ifc_register_exp_data_t entries[MAX_REGISTER_ENTRIES];  /* Fixed-size array of entries */
    int count;                                             /* Current number of entries */
} ifc_reg_exp_dict_t;

typedef struct {
    uint32_t address;
    uint32_t default_value;
} ifc_reg_def_value_t;

// Register mask struct
typedef struct {
    uint32_t address;        /* Register address */
    uint32_t combined_mask;  /* Combined mask of all readable/writable bits */
} register_mask_t;

// Dictionary of register mask values
typedef struct {
    register_mask_t entries[MAX_REGISTER_ENTRIES];  /* Fixed-size array of entries */
    int count;                                      /* Current number of entries */
} register_mask_dict_t;

typedef enum {
    COLD_RESET = 0,
    WARM_RESET = 1
} reset_type_t;

// Register groups
typedef enum {
    REG_GROUP_CAPABILITIES,
    REG_GROUP_STRAPS_RO,
    REG_GROUP_STRAPS_RO_RO,
    REG_GROUP_STATUS,
    REG_GROUP_STATUS_RO,
    REG_GROUP_SECURITY_RO,
    REG_GROUP_ERROR_RW1C,
    REG_GROUP_ERROR,
    REG_GROUP_ERROR_MASK,
    REG_GROUP_WATCHDOG,
    REG_GROUP_WATCHDOG_RO,
    REG_GROUP_MCU,
    REG_GROUP_CONTROL,
    REG_GROUP_CONTROL_RO,
    REG_GROUP_MBOX,
    REG_GROUP_MBOX_RW1S,
    REG_GROUP_DBG_MANUF_SERVICE,
    REG_GROUP_GENERIC_WIRES,
    REG_GROUP_GENERIC_WIRES_RO,
    REG_GROUP_FW,
    REG_GROUP_FW_PULSE_RW1S,
    REG_GROUP_TRNG,
    REG_GROUP_TRNG_RW1S,
    REG_GROUP_TRNG_PULSE_RW1S,
    REG_GROUP_FUSE,
    REG_GROUP_FUSE_RW1S,
    REG_GROUP_FUSE_RO,
    REG_GROUP_OWNER_PK_HASH_RO,
    // FUSES
    REG_GROUP_UDS_RO,
    REG_GROUP_FIELD_ENTROPY_RO,
    REG_GROUP_VENDOR_PK_HASH_RO,
    REG_GROUP_ECC_REVOCATION_RO,
    REG_GROUP_SVN_RO,
    REG_GROUP_ANTI_ROLLBACK_RO,
    REG_GROUP_IDEVID_RO,
    REG_GROUP_MANUF_DBG_UNLOCK_RO,
    REG_GROUP_SOC_STEPPING_RO,
    REG_GROUP_KEY_TYPE_RO,
    // INTR
    REG_GROUP_INTERRUPT_EN,
    REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO,
    REG_GROUP_INTERRUPT_STATUS_RW1C,
    REG_GROUP_INTERRUPT_TRIGGER_PULSE_RW1S,
    REG_GROUP_INTERRUPT_ERROR_COUNTERS,
    REG_GROUP_INTERRUPT_NOTIF_COUNTERS,
    REG_GROUP_INTERRUPT_ERROR_COUNTERS_INCR_RO,
    REG_GROUP_INTERRUPT_NOTIF_COUNTERS_INCR_RO,
    REG_GROUP_COUNT
} ifc_register_group_t;

extern const ifc_register_info_t *register_groups[];

// Global dictionary
extern ifc_reg_exp_dict_t g_expected_data_dict;

uint32_t ifc_reg_read(uint32_t reg_addr);
void ifc_reg_write(uint32_t reg_addr, uint32_t value);
bool is_ro(ifc_register_group_t group);
uint32_t report_mismatch(ifc_register_group_t group, uint32_t id, uint32_t reg_addr, uint32_t read_data, uint32_t exp_data);

const ifc_register_info_t* find_register_by_address(uint32_t address, ifc_register_group_t *group_index, int *reg_index, ifc_register_group_t start_index);
uint32_t exp_reg_group_interrupt_global_status_ro(uint32_t reg_id);
uint32_t exp_with_init_value(uint32_t reg_address);
int get_total_register_count(void);
void init_reg_exp_dict(ifc_reg_exp_dict_t *dict);
int set_reg_exp_data(ifc_reg_exp_dict_t *dict, uint32_t address, uint32_t value, uint32_t mask, bool reg_write, ifc_register_group_t group_index_arg, bool soc_access);
int get_reg_exp_data(ifc_reg_exp_dict_t *dict, uint32_t address, uint32_t *value);
void init_mask_dict(void);
const ifc_register_info_t* get_register_info(ifc_register_group_t group, int index);
int get_register_count(ifc_register_group_t group);
uint32_t get_register_mask(uint32_t address);
const char* get_group_name(ifc_register_group_t group);
int add_mask_entry(uint32_t address, uint32_t mask);
void write_random_to_register_group_and_track(ifc_register_group_t group, ifc_reg_exp_dict_t *dict);
void write_to_register_group_and_track(ifc_register_group_t group, uint32_t write_data, ifc_reg_exp_dict_t *dict);
int read_register_group_and_verify(ifc_register_group_t group, ifc_reg_exp_dict_t *dict, bool reset, reset_type_t reset_type, bool use_hw);
void read_register_group_and_track(ifc_register_group_t group, ifc_reg_exp_dict_t *dict);
static void address_to_bitmap_position(uint32_t reg_addr, uint32_t *word_index, uint32_t *bit_position);
int exclude_register(uint32_t reg_addr);
int is_register_excluded(uint32_t reg_addr);
void init_excluded_registers(void);

/* Initialization */
void ifc_init(void);

#endif /* IFC_REG_H */
