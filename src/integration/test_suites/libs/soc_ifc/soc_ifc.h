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
  
#include "stdint.h"
#include "riscv_hw_if.h"

/* --------------- symbols/typedefs --------------- */
enum boot_fsm_state_e {
    BOOT_IDLE   = 0x0,
    BOOT_FUSE   = 0x1,
    BOOT_FW_RST = 0x2,
    BOOT_WAIT   = 0x3,
    BOOT_DONE   = 0x4
};
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
    MBOX_EXECUTE_SOC  = 0x4,
    MBOX_ERROR        = 0x7
};

enum axi_dma_rd_route_e {
    axi_dma_rd_route_DISABLE  = 0x0,
    axi_dma_rd_route_MBOX     = 0x1,
    axi_dma_rd_route_AHB_FIFO = 0x2,
    axi_dma_rd_route_AXI_WR   = 0x3
};

enum axi_dma_wr_route_e {
    axi_dma_wr_route_DISABLE  = 0x0,
    axi_dma_wr_route_MBOX     = 0x1,
    axi_dma_wr_route_AHB_FIFO = 0x2,
    axi_dma_wr_route_AXI_RD   = 0x3
};

enum axi_dma_fsm_e {
    axi_dma_fsm_DMA_IDLE      = 0x0,
    axi_dma_fsm_DMA_WAIT_DATA = 0x1,
    axi_dma_fsm_DMA_DONE      = 0x2,
    axi_dma_fsm_DMA_ERROR     = 0x3
};

/**
* Decode:
*   [31]: Firmware command
*   [30]: Response required (if set)
*   [29]: uC to SOC Mailbox command
*/
enum {
    MBOX_CMD_FIELD_FW_LOW        = 31,
    MBOX_CMD_FIELD_RESP_LOW      = 30,
    MBOX_CMD_FIELD_UC_TO_SOC_LOW = 29
};

enum {
    MBOX_CMD_FIELD_FW_MASK        = 1 << MBOX_CMD_FIELD_FW_LOW  ,
    MBOX_CMD_FIELD_RESP_MASK      = 1 << MBOX_CMD_FIELD_RESP_LOW,
    MBOX_CMD_FIELD_UC_TO_SOC_MASK = 1 << MBOX_CMD_FIELD_UC_TO_SOC_LOW
};

enum mbox_cmd_e {
    MBOX_CMD_DIR_RD     = 0x01000000,
    MBOX_CMD_UC_BASIC   = 0x20000000,
    MBOX_CMD_UC_OVERRUN = 0x20000001,
    MBOX_CMD_RESP_BASIC = 0x40000000,
    MBOX_CMD_REG_ACCESS = 0x40000001,
    MBOX_CMD_OOB_ACCESS = 0x40000002,
    MBOX_CMD_FMC_UPDATE = 0xba5eba11,
    MBOX_CMD_RT_UPDATE  = 0xbabecafe,
    MBOX_CMD_SHA384_REQ = 0x40C0FFEE,
    MBOX_CMD_SHA512_REQ = 0x41C0FFEE,
    MBOX_CMD_SHA384_STREAM_REQ = 0x42C0FFEE,
    MBOX_CMD_SHA512_STREAM_REQ = 0x43C0FFEE
};

// Boundaries against which the incoming remote FW images are aligned
enum mbox_fw_offsets_e {
    MBOX_ICCM_OFFSET_FMC = 0x00000,
    MBOX_DCCM_OFFSET_FMC = 0x00000,
    MBOX_ICCM_OFFSET_RT  = 0x20000,
    MBOX_DCCM_OFFSET_RT  = 0x20000,
};

typedef struct {
    uint32_t dlen;
    enum mbox_cmd_e cmd;
} mbox_op_s;

enum sha_accel_mode_e {
    SHA_STREAM_384 = 0x0,
    SHA_STREAM_512 = 0x1,
    SHA_MBOX_384   = 0x2,
    SHA_MBOX_512   = 0x3,
};

/* --------------- Function Prototypes --------------- */
// Simple reg accesses
uint32_t soc_ifc_mbox_read_dataout_single();
uint32_t soc_ifc_mbox_dir_read_single(uint32_t rdptr);
uint32_t soc_ifc_mbox_dir_write_single(uint32_t wrptr, uint32_t wrdata);
void soc_ifc_clear_execute_reg();
uint8_t soc_ifc_chk_execute_uc();
void soc_ifc_set_mbox_status_field(enum mbox_status_e field);
void soc_ifc_set_flow_status_field(uint32_t field);
void soc_ifc_clr_flow_status_field(uint32_t field);
void soc_ifc_set_fw_update_reset(uint8_t wait_cycles);
void soc_ifc_set_iccm_lock();
// Mailbox command flows
uint8_t soc_ifc_mbox_acquire_lock(uint32_t attempt_count);
mbox_op_s soc_ifc_read_mbox_cmd();
void soc_ifc_mbox_fw_flow(mbox_op_s op);
void soc_ifc_fw_update(mbox_op_s op);
uint8_t soc_ifc_sanitize_mbox_n_bytes(uint32_t byte_count, uint32_t attempt_count);

// SHA Accelerator Functions
void soc_ifc_sha_accel_acquire_lock();
void soc_ifc_sha_accel_wr_mode(enum sha_accel_mode_e mode);
void soc_ifc_sha_accel_execute();
void soc_ifc_sha_accel_poll_status();
void soc_ifc_sha_accel_clr_lock();
void soc_ifc_w1clr_sha_lock_field();

// AXI DMA Functions
uint8_t soc_ifc_axi_dma_send_ahb_payload(uint64_t dst_addr, uint8_t fixed, uint32_t * payload, uint32_t byte_count, uint16_t block_size);
uint8_t soc_ifc_axi_dma_read_ahb_payload(uint64_t src_addr, uint8_t fixed, uint32_t * payload, uint32_t byte_count, uint16_t block_size);
uint8_t soc_ifc_axi_dma_send_mbox_payload(uint64_t src_addr, uint64_t dst_addr, uint8_t fixed, uint32_t byte_count, uint16_t block_size);
uint8_t soc_ifc_axi_dma_read_mbox_payload(uint64_t src_addr, uint64_t dst_addr, uint8_t fixed, uint32_t byte_count, uint16_t block_size);
uint8_t soc_ifc_axi_dma_send_axi_to_axi(uint64_t src_addr, uint8_t src_fixed, uint64_t dst_addr, uint8_t dst_fixed, uint32_t byte_count, uint16_t block_size);

#endif
