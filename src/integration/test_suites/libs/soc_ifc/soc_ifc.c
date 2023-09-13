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

#include "caliptra_defines.h"
#include "soc_ifc.h"
#include "printf.h"

void soc_ifc_clear_execute_reg() {
    VPRINTF(MEDIUM,"SOC_IFC: Clear execute reg");
    uint32_t reg;
    reg = lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE);
    reg = (reg & ~MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);
    lsu_write_32(CLP_MBOX_CSR_MBOX_EXECUTE,reg);
}

// Return 0 if the MBOX_FSM_PS field reports MBOX_EXECUTE_UC, as expected
// Return 1 if the MBOX_FSM_PS field reports MBOX_IDLE, indicating mailbox was already force-unlocked (after receiving a cmd_avail interrupt)
// Return F if the MBOX_FSM_PS field reports MBOX_ERROR (to which this routine responds with a force-unlock)
// Return FF if the MBOX_FSM_PS field reports any other state, which should never happen when this is called
uint8_t soc_ifc_chk_execute_uc() {
    enum mbox_fsm_e state;
    VPRINTF(HIGH,"SOC_IFC: Check mbox_status.mbox_fsm_ps\n");
    state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    if (state == MBOX_EXECUTE_UC) {
        VPRINTF(HIGH,"SOC_IFC: Check mbox_status.mbox_fsm_ps found MBOX_EXECUTE_UC\n");
        return 0;
    } else if (state == MBOX_IDLE) {
        VPRINTF(WARNING,"SOC_IFC: Check mbox_status.mbox_fsm_ps found MBOX_IDLE\n");
        return 1;
    } else if (state == MBOX_ERROR) {
        VPRINTF(ERROR,"SOC_IFC: Check mbox_status.mbox_fsm_ps found MBOX_ERROR, executing mailbox force-unlock\n");
        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
        return 0xF;
    } else {
        VPRINTF(FATAL,"SOC_IFC: Check mbox_status.mbox_fsm_ps found unexpected state 0x%x\n", state);
        return 0xFF;
    }
}

void soc_ifc_set_mbox_status_field(enum mbox_status_e field) {
    VPRINTF(MEDIUM,"SOC_IFC: Set mbox_status field: 0x%x\n", field);
    uint32_t reg;
    reg = lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS);
    reg = (reg & ~MBOX_CSR_MBOX_STATUS_STATUS_MASK) | (field << MBOX_CSR_MBOX_STATUS_STATUS_LOW);
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS,reg);
}

void soc_ifc_set_flow_status_field(uint32_t field) {
    VPRINTF(MEDIUM,"SOC_IFC: Set flow_status field: 0x%x\n", field);
    uint32_t reg;
    reg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS);
    if (field & SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_MASK) {
        reg = (reg & ~SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_MASK) | field;
    } else {
        reg |= field;
    }
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS,reg);
}

// This function as implemented will clear all the bits in the register on writing '1; 
// In future, if this register has additional bits that cannot be cleared on writing '1, 
// then this function also needs an update in addition to the RTL itself
void soc_ifc_w1clr_sha_lock_field(uint32_t field) {
    VPRINTF(MEDIUM,"SOC_IFC: Clear SHA accelerator lock by writing '1: 0x%x\n", field);
    uint32_t reg;
    reg = lsu_read_32(CLP_SHA512_ACC_CSR_LOCK);
    if (field & ~SHA512_ACC_CSR_LOCK_LOCK_MASK) {
       VPRINTF(FATAL, "SOC_IFC: Bad field value");
       SEND_STDOUT_CTRL(0x1); 
    } 
    else if (reg & ~SHA512_ACC_CSR_LOCK_LOCK_MASK) {
       VPRINTF(FATAL, "SOC_IFC: Bad field value");
       SEND_STDOUT_CTRL(0x1); 
    }
    if (field & SHA512_ACC_CSR_LOCK_LOCK_MASK) {
        reg = (reg & ~SHA512_ACC_CSR_LOCK_LOCK_MASK) | field;
    } else {
        reg |= field;
    }
    lsu_write_32(CLP_SHA512_ACC_CSR_LOCK,reg);
}

void soc_ifc_clr_flow_status_field(uint32_t field) {
    VPRINTF(MEDIUM,"SOC_IFC: Clear flow_status field: 0x%x\n", field);
    uint32_t reg;
    reg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS);
    // Clear entire multi-bit status field if any constituent bit is set in arg
    // and also clear other 1-bit values
    if (field & SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_MASK) {
        reg =  (reg   & ~SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_MASK) &
              ~(field & ~SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_MASK);
    }
    // Clear any 1-bit values, leaving multibit status field untouched
    else {
        reg &= ~field;
    }
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS,reg);
}

mbox_op_s soc_ifc_read_mbox_cmd() {
    mbox_op_s op;

    //read mbox command
    op.cmd = lsu_read_32(CLP_MBOX_CSR_MBOX_CMD);
    VPRINTF(MEDIUM,"SOC_IFC: CMD from mailbox: 0x%x\n", op.cmd);

    //read mbox dlen
    op.dlen = lsu_read_32(CLP_MBOX_CSR_MBOX_DLEN);
    VPRINTF(MEDIUM,"SOC_IFC: DLEN from mailbox: 0x%x\n", op.dlen);

    return op;
}

/**
 * @brief Perform firmware update, assuming cmd/dlen already read from Mailbox
 * @param op is a struct containing the mailbox command and dlen fields
 * @return none
 */
void soc_ifc_mbox_fw_flow(mbox_op_s op) {
    uint32_t iccm_cp_size;
    uint32_t dccm_cp_size;
    uint32_t* iccm;
    uint32_t* dccm;
    uint32_t  offset; // In 32-bit dwords

    VPRINTF(LOW, "SOC_IFC: Beginning mbox fw flow\n");
    if (op.dlen > MBOX_DIR_SPAN) {
        VPRINTF(FATAL, "FATAL: Invalid dlen passed to mbox fw flow: 0x%x\n", op.dlen);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if (op.cmd == MBOX_CMD_FMC_UPDATE) {
        iccm = (uint32_t*) (RV_ICCM_SADR + MBOX_ICCM_OFFSET_FMC);
        dccm = (uint32_t*) (RV_DCCM_SADR + MBOX_DCCM_OFFSET_FMC);
    } else if (op.cmd == MBOX_CMD_RT_UPDATE) {
        iccm = (uint32_t*) (RV_ICCM_SADR + MBOX_ICCM_OFFSET_RT);
        dccm = (uint32_t*) (RV_DCCM_SADR + MBOX_DCCM_OFFSET_RT);
    } else {
        VPRINTF(FATAL, "FATAL: Invalid cmd passed to mbox fw flow: 0x%x\n", op.cmd);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    //////////////////////////////
    // Copy Firmware Image
    //  1. Get size of the text section for ICCM
    iccm_cp_size = soc_ifc_mbox_read_dataout_single();
    if (iccm_cp_size == 0x0 || (iccm_cp_size + 0x20) > op.dlen) { // 0x20 fudge factor for linker offsets that contain iccm/dccm copy size
        VPRINTF(FATAL, "Found invalid iccm size in firmware image received from SOC! Max expected 0x%x, got 0x%x\n", op.dlen, iccm_cp_size);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    // Add a dword to compensate for truncation, below, which clobbers the
    // extra unaligned byte-count
    if (iccm_cp_size & 0x3) {
        iccm_cp_size += 4;
    }
    iccm_cp_size >>= 2; // Align to dword for comparison with offset (which is in dwords)
    // Next 3 dwords are 0 (per linker) - discard
    iccm[0] = soc_ifc_mbox_read_dataout_single();
    iccm[0] = soc_ifc_mbox_read_dataout_single();
    iccm[0] = soc_ifc_mbox_read_dataout_single();
    offset = 0;

    //  2. Copy from mailbox into ICCM
    VPRINTF(LOW, "SOC_IFC: Cp to ICCM\n");
    while(offset < iccm_cp_size) {
        iccm[offset++] = soc_ifc_mbox_read_dataout_single();
    }

    //  3. Get size of the data section for DCCM
    dccm_cp_size = soc_ifc_mbox_read_dataout_single();
    if (dccm_cp_size == 0x0 || ((iccm_cp_size<<2) + dccm_cp_size + 0x20) > op.dlen) { // 0x20 fudge factor for linker offsets that contain iccm/dccm copy size
        VPRINTF(FATAL, "Found invalid dccm size in firmware image received from SOC! Max expected 0x%x, got 0x%x\n", op.dlen - iccm_cp_size - 0x20, dccm_cp_size);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    // Add a dword to compensate for truncation, below, which clobbers the
    // extra unaligned byte-count
    if (dccm_cp_size & 0x3) {
        dccm_cp_size += 4;
    }
    dccm_cp_size >>= 2; // Align to dword for comparison with offset (which is in dwords)
    // Next 3 dwords are 0 (per linker) - discard
    dccm[0] = soc_ifc_mbox_read_dataout_single();
    dccm[0] = soc_ifc_mbox_read_dataout_single();
    dccm[0] = soc_ifc_mbox_read_dataout_single();
    offset = 0;

    //  4. Copy from mailbox to DCCM
    VPRINTF(LOW, "SOC_IFC: Cp to DCCM\n");
    while(offset < dccm_cp_size) {
        dccm[offset++] = soc_ifc_mbox_read_dataout_single();
    }

    // Write DLEN to 0 (since there is no response)
    lsu_write_32(CLP_MBOX_CSR_MBOX_DLEN, 0);

    // Set the command complete status
    soc_ifc_set_mbox_status_field(CMD_COMPLETE);

}

void soc_ifc_fw_update(mbox_op_s op) {

    uint32_t * ICCM = (uint32_t *) RV_ICCM_SADR;
    uint32_t * iccm_dest = ICCM;
    uint32_t data_length;

    VPRINTF(MEDIUM, "Copying code from mailbox to ICCM\n");
    while (data_length < op.dlen) {
        VPRINTF(MEDIUM, "at %x: %x\n", (uintptr_t) iccm_dest, *iccm_dest);
            *iccm_dest++ = soc_ifc_mbox_read_dataout_single();
            data_length += 4; //dlen is in bytes
        }
}

void soc_ifc_set_fw_update_reset(uint8_t wait_cycles) {
    uint32_t reg;
    VPRINTF(MEDIUM,"SOC_IFC: Set fw update reset with wait_cycles [%d] (%s)\n", wait_cycles, wait_cycles > 5 ? "will override" : wait_cycles > 0 ? "will use default 5" : "won't override");
    // A 0-value argument means don't override the current value
    if (wait_cycles) {
        // Enforce minimum wait_cycles of 5
        if (wait_cycles > 5) {
            lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES, wait_cycles);
        } else {
            lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES, 5);
        }
    }
    reg = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET);
    reg = (reg | SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET,reg);
}

//SHA Accelerator
void soc_ifc_sha_accel_acquire_lock() {
    while((lsu_read_32(CLP_SHA512_ACC_CSR_LOCK) & SHA512_ACC_CSR_LOCK_LOCK_MASK) == 1);
}

void soc_ifc_sha_accel_wr_mode(enum sha_accel_mode_e mode) {
    uint32_t reg;
    reg = ((mode << SHA512_ACC_CSR_MODE_MODE_LOW) & SHA512_ACC_CSR_MODE_MODE_MASK) | 
            SHA512_ACC_CSR_MODE_ENDIAN_TOGGLE_MASK; //set endian toggle so we read from the mailbox as is
    lsu_write_32(CLP_SHA512_ACC_CSR_MODE,reg);
}

void soc_ifc_sha_accel_poll_status() {
    while((lsu_read_32(CLP_SHA512_ACC_CSR_STATUS) & SHA512_ACC_CSR_STATUS_VALID_MASK) == 0);
}

void soc_ifc_sha_accel_clr_lock() {
    //Write one to clear
    lsu_write_32((CLP_SHA512_ACC_CSR_LOCK), SHA512_ACC_CSR_LOCK_LOCK_MASK);
}   
