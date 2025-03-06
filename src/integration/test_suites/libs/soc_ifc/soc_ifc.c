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
#include "caliptra_reg.h"
#include "soc_ifc.h"
#include "printf.h"

uint32_t soc_ifc_mbox_read_dataout_single() {
    return lsu_read_32(CLP_MBOX_CSR_MBOX_DATAOUT);
}
uint32_t soc_ifc_mbox_dir_read_single(uint32_t rdptr) {
    return lsu_read_32(CLP_MBOX_SRAM_BASE_ADDR + rdptr);
}
uint32_t soc_ifc_mbox_dir_write_single(uint32_t wrptr, uint32_t wrdata) {
    lsu_write_32(CLP_MBOX_SRAM_BASE_ADDR + wrptr, wrdata);
}

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
        VPRINTF(ERROR,"SOC_IFC: Check mbox_status.mbox_fsm_ps found MBOX_ERROR, mailbox force-unlock needed\n");
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

uint8_t soc_ifc_mbox_acquire_lock(uint32_t attempt_count) {
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        if((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 0) {
            return 0;
        }
    }
    return 1;
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

uint8_t soc_ifc_sanitize_mbox_n_bytes(uint32_t byte_count, uint32_t attempt_count) {
    uint32_t notif_intr_en;
    if (byte_count > MBOX_DIR_SPAN) {
        VPRINTF(FATAL, "SOC_IFC: Illegal byte_count 0x%x\n", byte_count);
        SEND_STDOUT_CTRL(0x1);
    }
    if(soc_ifc_mbox_acquire_lock(attempt_count) != 0) {
        VPRINTF(WARNING, "Failed to acquire lock - mbox sanitize\n");
        for(uint32_t ii=1; ii<attempt_count; ii++) {
            lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
            if((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 0) {
                break;
            } else if (ii == attempt_count) {
                VPRINTF(FATAL, "FATAL: Failed to acquire lock after force unlock\n");
                return 1;
            }
        }
    }
    // Disable notification interrupts for soc_req_lock, which will probably
    // occur at a high frequency while sanitizing the mailbox and cause a slowdown
    notif_intr_en = lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R);
    lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, notif_intr_en & ~(SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_SOC_REQ_LOCK_EN_MASK |
                                                                                  SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_MBOX_ECC_COR_EN_MASK));
    for (uint32_t ii=0; ii < byte_count; ii+=4) {
        lsu_write_32(CLP_MBOX_SRAM_BASE_ADDR+ii, 0x0);
    }
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
    lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, notif_intr_en);
    return 0;
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

void soc_ifc_set_iccm_lock() {
    lsu_write_32((CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK), SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK);
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

void soc_ifc_sha_accel_execute() {
    lsu_write_32((CLP_SHA512_ACC_CSR_EXECUTE), SHA512_ACC_CSR_EXECUTE_EXECUTE_MASK);
}

void soc_ifc_sha_accel_poll_status() {
    while((lsu_read_32(CLP_SHA512_ACC_CSR_STATUS) & SHA512_ACC_CSR_STATUS_VALID_MASK) == 0) {
        //poke at the mailbox direct read path to create stall scenario
        lsu_read_32(CLP_MBOX_SRAM_BASE_ADDR);
    };
}

void soc_ifc_sha_accel_clr_lock() {
    //Write one to clear
    lsu_write_32((CLP_SHA512_ACC_CSR_LOCK), SHA512_ACC_CSR_LOCK_LOCK_MASK);
}   

// AXI DMA Functions
uint8_t soc_ifc_axi_dma_send_ahb_payload(uint64_t dst_addr, uint8_t fixed, uint32_t * payload, uint32_t byte_count, uint16_t block_size) {
    uint32_t reg;
    uint16_t mdepth;

    // Arm the command
    while (lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_BUSY_MASK);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_L,  dst_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_H, (dst_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_BYTE_COUNT, byte_count);
    lsu_write_32(CLP_AXI_DMA_REG_BLOCK_SIZE, (uint32_t) block_size);
    reg =  AXI_DMA_REG_CTRL_GO_MASK                                    |
          (axi_dma_rd_route_DISABLE << AXI_DMA_REG_CTRL_RD_ROUTE_LOW)  |
          (axi_dma_wr_route_AHB_FIFO << AXI_DMA_REG_CTRL_WR_ROUTE_LOW) |
          (fixed ? AXI_DMA_REG_CTRL_WR_FIXED_MASK : 0);
    lsu_write_32(CLP_AXI_DMA_REG_CTRL, reg);

    // Send data
    mdepth = (lsu_read_32(CLP_AXI_DMA_REG_CAP) & AXI_DMA_REG_CAP_FIFO_MAX_DEPTH_MASK) >> AXI_DMA_REG_CAP_FIFO_MAX_DEPTH_LOW;
    for (uint32_t dw_sent = 0; dw_sent < (byte_count>>2); dw_sent++) {
        // Wait for there to be available space in the FIFO
        while(((lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_FIFO_DEPTH_MASK) >> AXI_DMA_REG_STATUS0_FIFO_DEPTH_LOW) == mdepth);
        lsu_write_32(CLP_AXI_DMA_REG_WRITE_DATA, payload[dw_sent]);
    }

    // Check completion
    reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    while ((reg & AXI_DMA_REG_STATUS0_BUSY_MASK) && !(reg & AXI_DMA_REG_STATUS0_ERROR_MASK)) {
        reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    }

    if (reg & AXI_DMA_REG_STATUS0_ERROR_MASK) {
        VPRINTF(FATAL, "FATAL: AXI DMA reports error status for FIFO-to-AXI xfer\n");
        lsu_write_32(CLP_AXI_DMA_REG_CTRL, AXI_DMA_REG_CTRL_FLUSH_MASK);
        SEND_STDOUT_CTRL(0x1);
    }
}

uint8_t soc_ifc_axi_dma_read_ahb_payload(uint64_t src_addr, uint8_t fixed, uint32_t * payload, uint32_t byte_count, uint16_t block_size) {
    soc_ifc_axi_dma_arm_read_ahb_payload(src_addr, fixed, payload, byte_count, block_size);
    soc_ifc_axi_dma_get_read_ahb_payload(payload, byte_count);
    soc_ifc_axi_dma_wait_idle(0);
}
uint8_t soc_ifc_axi_dma_arm_read_ahb_payload(uint64_t src_addr, uint8_t fixed, uint32_t * payload, uint32_t byte_count, uint16_t block_size) {
    uint32_t reg;

    // Arm the command
    while (lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_BUSY_MASK);
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_L,  src_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_H, (src_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_BYTE_COUNT, byte_count);
    lsu_write_32(CLP_AXI_DMA_REG_BLOCK_SIZE, (uint32_t) block_size);
    reg = (AXI_DMA_REG_CTRL_GO_MASK)                                   |
          (axi_dma_rd_route_AHB_FIFO << AXI_DMA_REG_CTRL_RD_ROUTE_LOW) |
          (axi_dma_wr_route_DISABLE << AXI_DMA_REG_CTRL_WR_ROUTE_LOW)  |
          (fixed ? AXI_DMA_REG_CTRL_RD_FIXED_MASK : 0);
    lsu_write_32(CLP_AXI_DMA_REG_CTRL, reg);

}

uint8_t soc_ifc_axi_dma_get_read_ahb_payload(uint32_t * payload, uint32_t byte_count) {
    uint16_t mdepth;
    // Read data
    mdepth = (lsu_read_32(CLP_AXI_DMA_REG_CAP) & AXI_DMA_REG_CAP_FIFO_MAX_DEPTH_MASK) >> AXI_DMA_REG_CAP_FIFO_MAX_DEPTH_LOW;
    for (uint32_t dw_rcv = 0; dw_rcv < (byte_count>>2); dw_rcv++) {
        // Wait for there to be available data in the FIFO
        while(((lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_FIFO_DEPTH_MASK) >> AXI_DMA_REG_STATUS0_FIFO_DEPTH_LOW) == 0);
        payload[dw_rcv] = lsu_read_32(CLP_AXI_DMA_REG_READ_DATA);
    }
}

uint8_t soc_ifc_axi_dma_send_mbox_payload(uint64_t src_addr, uint64_t dst_addr, uint8_t fixed, uint32_t byte_count, uint16_t block_size) {
    uint32_t reg;

    // Acquire the mailbox lock
    if (soc_ifc_mbox_acquire_lock(1)) {
        VPRINTF(ERROR, "Acquire mailbox lock failed\n");
        return 1;
    }

    // src_addr checks
    if (src_addr & ~((uint64_t) (MBOX_DIR_SPAN-1))) {
        VPRINTF(ERROR, "src_addr 0x%x is out of bounds for mbox span!\n", src_addr);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if ((src_addr + byte_count) & ~((uint64_t) (MBOX_DIR_SPAN-1))) {
        VPRINTF(ERROR, "reading 0x%x bytes from src_addr 0x%x goes out of bounds for mbox span!\n", src_addr, byte_count);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Arm the command
    while (lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_BUSY_MASK);
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_L,  src_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_H, (src_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_L,  dst_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_H, (dst_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_BYTE_COUNT, byte_count);
    lsu_write_32(CLP_AXI_DMA_REG_BLOCK_SIZE, (uint32_t) block_size);
    reg = (AXI_DMA_REG_CTRL_GO_MASK)                                   |
          (axi_dma_rd_route_DISABLE << AXI_DMA_REG_CTRL_RD_ROUTE_LOW)  |
          (axi_dma_wr_route_MBOX << AXI_DMA_REG_CTRL_WR_ROUTE_LOW)     |
          (fixed ? AXI_DMA_REG_CTRL_WR_FIXED_MASK : 0);
    lsu_write_32(CLP_AXI_DMA_REG_CTRL, reg);

    // Check completion
    reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    while ((reg & AXI_DMA_REG_STATUS0_BUSY_MASK) && !(reg & AXI_DMA_REG_STATUS0_ERROR_MASK)) {
        reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    }

    // Check status
    if (reg & AXI_DMA_REG_STATUS0_ERROR_MASK) {
        VPRINTF(FATAL, "FATAL: AXI DMA reports error status for MBOX-to-AXI xfer\n");
        lsu_write_32(CLP_AXI_DMA_REG_CTRL, AXI_DMA_REG_CTRL_FLUSH_MASK);
        SEND_STDOUT_CTRL(0x1);
    }

    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
    return 0;
}

uint8_t soc_ifc_axi_dma_read_mbox_payload(uint64_t src_addr, uint64_t dst_addr, uint8_t fixed, uint32_t byte_count, uint16_t block_size) {
    uint32_t reg;

    // Acquire the mailbox lock
    if (soc_ifc_mbox_acquire_lock(1)) {
        VPRINTF(ERROR, "Acquire mailbox lock failed\n");
        return 1;
    }

    // dst_addr checks
    if (dst_addr & ~((uint64_t) (MBOX_DIR_SPAN-1))) {
        VPRINTF(ERROR, "dst_addr 0x%x is out of bounds for mbox span!\n", dst_addr);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if ((dst_addr + byte_count) & ~((uint64_t) (MBOX_DIR_SPAN-1))) {
        VPRINTF(ERROR, "writing 0x%x bytes to dst_addr 0x%x goes out of bounds for mbox span!\n", dst_addr, byte_count);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Arm the command
    while (lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_BUSY_MASK);
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_L,  src_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_H, (src_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_L,  dst_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_H, (dst_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_BYTE_COUNT, byte_count);
    lsu_write_32(CLP_AXI_DMA_REG_BLOCK_SIZE, (uint32_t) block_size);
    reg = (AXI_DMA_REG_CTRL_GO_MASK)                                   |
          (axi_dma_rd_route_MBOX << AXI_DMA_REG_CTRL_RD_ROUTE_LOW)     |
          (axi_dma_wr_route_DISABLE << AXI_DMA_REG_CTRL_WR_ROUTE_LOW)  |
          (fixed ? AXI_DMA_REG_CTRL_RD_FIXED_MASK : 0);
    lsu_write_32(CLP_AXI_DMA_REG_CTRL, reg);

    // Check completion
    reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    while ((reg & AXI_DMA_REG_STATUS0_BUSY_MASK) && !(reg & AXI_DMA_REG_STATUS0_ERROR_MASK)) {
        reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    }

    // Check status
    if (reg & AXI_DMA_REG_STATUS0_ERROR_MASK) {
        VPRINTF(FATAL, "FATAL: AXI DMA reports error status for AXI-to-MBOX xfer\n");
        lsu_write_32(CLP_AXI_DMA_REG_CTRL, AXI_DMA_REG_CTRL_FLUSH_MASK);
        SEND_STDOUT_CTRL(0x1);
    }

    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
    return 0;
}

uint8_t soc_ifc_axi_dma_read_mbox_payload_no_wait(uint64_t src_addr, uint64_t dst_addr, uint8_t fixed, uint32_t byte_count, uint16_t block_size) {
    uint32_t reg;

    // Acquire the mailbox lock
    if (soc_ifc_mbox_acquire_lock(1)) {
        VPRINTF(ERROR, "Acquire mailbox lock failed\n");
        return 1;
    }

    // dst_addr checks
    if (dst_addr & ~((uint64_t) (MBOX_DIR_SPAN-1))) {
        VPRINTF(ERROR, "dst_addr 0x%x is out of bounds for mbox span!\n", dst_addr);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if ((dst_addr + byte_count) & ~((uint64_t) (MBOX_DIR_SPAN-1))) {
        VPRINTF(ERROR, "writing 0x%x bytes to dst_addr 0x%x goes out of bounds for mbox span!\n", dst_addr, byte_count);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Arm the command
    while (lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_BUSY_MASK);
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_L,  src_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_H, (src_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_L,  dst_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_H, (dst_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_BYTE_COUNT, byte_count);
    lsu_write_32(CLP_AXI_DMA_REG_BLOCK_SIZE, (uint32_t) block_size);
    reg = (AXI_DMA_REG_CTRL_GO_MASK)                                   |
          (axi_dma_rd_route_MBOX << AXI_DMA_REG_CTRL_RD_ROUTE_LOW)     |
          (axi_dma_wr_route_DISABLE << AXI_DMA_REG_CTRL_WR_ROUTE_LOW)  |
          (fixed ? AXI_DMA_REG_CTRL_RD_FIXED_MASK : 0);
    lsu_write_32(CLP_AXI_DMA_REG_CTRL, reg);

    return 0;
}

uint8_t soc_ifc_axi_dma_send_axi_to_axi(uint64_t src_addr, uint8_t src_fixed, uint64_t dst_addr, uint8_t dst_fixed, uint32_t byte_count, uint16_t block_size) {
    soc_ifc_axi_dma_send_axi_to_axi_no_wait(src_addr, src_fixed, dst_addr, dst_fixed, byte_count, block_size);
    soc_ifc_axi_dma_wait_idle(0);
}

uint8_t soc_ifc_axi_dma_send_axi_to_axi_no_wait(uint64_t src_addr, uint8_t src_fixed, uint64_t dst_addr, uint8_t dst_fixed, uint32_t byte_count, uint16_t block_size) {
    uint32_t reg;

    // Arm the command
    while (lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_BUSY_MASK);
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_L,  src_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_H, (src_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_L,  dst_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_H, (dst_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_BYTE_COUNT, byte_count);
    lsu_write_32(CLP_AXI_DMA_REG_BLOCK_SIZE, (uint32_t) block_size);
    reg = (AXI_DMA_REG_CTRL_GO_MASK)                                 |
          (axi_dma_rd_route_AXI_WR << AXI_DMA_REG_CTRL_RD_ROUTE_LOW) |
          (axi_dma_wr_route_AXI_RD << AXI_DMA_REG_CTRL_WR_ROUTE_LOW) |
          (src_fixed ? AXI_DMA_REG_CTRL_RD_FIXED_MASK : 0)           |
          (dst_fixed ? AXI_DMA_REG_CTRL_WR_FIXED_MASK : 0);
    lsu_write_32(CLP_AXI_DMA_REG_CTRL, reg);

}

uint8_t soc_ifc_axi_dma_wait_idle(uint8_t clr_lock) {
    uint32_t reg;

    // Check completion
    reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    while ((reg & AXI_DMA_REG_STATUS0_BUSY_MASK) && !(reg & AXI_DMA_REG_STATUS0_ERROR_MASK)) {
        reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    }

    // Check status
    if (reg & AXI_DMA_REG_STATUS0_ERROR_MASK) {
        VPRINTF(FATAL, "FATAL: AXI DMA reports error status for xfer\n");
        lsu_write_32(CLP_AXI_DMA_REG_CTRL, AXI_DMA_REG_CTRL_FLUSH_MASK);
        SEND_STDOUT_CTRL(0x1);
    }

    if (clr_lock) {
        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
    }
}
