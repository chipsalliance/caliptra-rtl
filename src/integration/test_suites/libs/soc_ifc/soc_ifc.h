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

#ifndef SOC_IFC_H
  #define SOC_IFC_H
  
#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "stdint.h"
#include "riscv_hw_if.h"

/* --------------- symbols/typedefs --------------- */
enum mbox_status_e {
    CMD_BUSY      = 0,
    DATA_READY    = 1,
    CMD_COMPLETE  = 2,
    CMD_FAILURE   = 3
};
enum mbox_fsm_e {
    MBOX_IDLE         = 0x0,
    MBOX_RDY_FOR_CMD  = 0x1,
    MBOX_RDY_FOR_DATA = 0x2,
    MBOX_RDY_FOR_DLEN = 0x3,
    MBOX_EXECUTE_UC   = 0x6,
    MBOX_EXECUTE_SOC  = 0x4
};

/**
* Decode:
*   [31]: Firmware command
*   [30]: Response required (if set)
*/
enum {
    MBOX_CMD_FIELD_FW_LOW   = 31,
    MBOX_CMD_FIELD_RESP_LOW = 30
};

enum {
    MBOX_CMD_FIELD_FW_MASK   = 1 << MBOX_CMD_FIELD_FW_LOW  ,
    MBOX_CMD_FIELD_RESP_MASK = 1 << MBOX_CMD_FIELD_RESP_LOW
};

enum mbox_cmd_e {
    MBOX_CMD_RESP_BASIC = 0x40000000,
    MBOX_CMD_FMC_UPDATE = 0xba5eba11,
    MBOX_CMD_RT_UPDATE  = 0xbabecafe
};

// Boundaries against which the incoming remote FW images are aligned
enum mbox_fw_offsets_e {
    MBOX_ICCM_OFFSET_FMC = 0x00000,
    MBOX_DCCM_OFFSET_FMC = 0x00000,
    MBOX_ICCM_OFFSET_RT  = 0x10000,
    MBOX_DCCM_OFFSET_RT  = 0x10000,
};

typedef struct {
    uint32_t dlen;
    enum mbox_cmd_e cmd;
} mbox_op_s;

/* --------------- Function Prototypes --------------- */
// Simple reg accesses
inline uint32_t soc_ifc_mbox_read_dataout_single() {
    return lsu_read_32((uint32_t*) CLP_MBOX_CSR_MBOX_DATAOUT);
}
void soc_ifc_clear_execute_reg();
void soc_ifc_set_mbox_status_field(enum mbox_status_e field);
void soc_ifc_set_flow_status_field(uint32_t field);
void soc_ifc_clr_flow_status_field(uint32_t field);
void soc_ifc_set_fw_update_reset();
inline void soc_ifc_set_iccm_lock() {
    lsu_write_32((uint32_t *) (CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK), SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK);
}
// Mailbox command flows
mbox_op_s soc_ifc_read_mbox_cmd();
void soc_ifc_mbox_fw_flow(mbox_op_s op);
void soc_ifc_fw_update(mbox_op_s op);

#endif
