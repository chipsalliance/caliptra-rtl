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

`ifndef SOC_IFC_PKG
`define SOC_IFC_PKG

package soc_ifc_pkg;
    
    parameter SOC_IFC_ADDR_W = 18;
    parameter SOC_IFC_DATA_W = 32;
    parameter SOC_IFC_USER_W = 32;
    
    parameter MBOX_SIZE_KB = 128;
    parameter MBOX_DATA_W = 32;
    parameter MBOX_ECC_DATA_W = 7;
    parameter MBOX_DATA_AND_ECC_W = MBOX_DATA_W + MBOX_ECC_DATA_W;
    parameter MBOX_DEPTH = (MBOX_SIZE_KB * 1024 * 8) / MBOX_DATA_W;
    parameter MBOX_ADDR_W = $clog2(MBOX_DEPTH);

    parameter WDT_TIMEOUT_PERIOD_NUM_DWORDS = 2;
    parameter WDT_TIMEOUT_PERIOD_W = WDT_TIMEOUT_PERIOD_NUM_DWORDS * 32;

    //memory map
    parameter MBOX_DIR_START_ADDR    = 18'h0_0000;
    parameter MBOX_DIR_END_ADDR      = 18'h1_FFFF;
    parameter MBOX_REG_START_ADDR    = 18'h2_0000;
    parameter MBOX_REG_END_ADDR      = 18'h2_0FFF;
    parameter SHA_REG_START_ADDR     = 18'h2_1000;
    parameter SHA_REG_END_ADDR       = 18'h2_1FFF;
    parameter SOC_IFC_REG_START_ADDR = 18'h3_0000;
    parameter SOC_IFC_REG_END_ADDR   = 18'h3_FFFF;

    //Valid PAUSER
    //Lock the PAUSER values from integration time
    parameter [4:0] CPTRA_SET_MBOX_PAUSER_INTEG   = { 1'b0,          1'b0,          1'b0,          1'b0,          1'b0};
    parameter [4:0][31:0] CPTRA_MBOX_VALID_PAUSER = {32'h4444_4444, 32'h3333_3333, 32'h2222_2222, 32'h1111_1111, 32'h0000_0000};
    parameter [31:0] CPTRA_DEF_MBOX_VALID_PAUSER  = 32'hFFFF_FFFF;

    //DMI Register encodings
    //Read only registers
    parameter DMI_REG_MBOX_DLEN = 7'h50;
    parameter DMI_REG_MBOX_DOUT = 7'h51;
    parameter DMI_REG_MBOX_STATUS = 7'h52;
    parameter DMI_REG_BOOT_STATUS = 7'h53;
    parameter DMI_REG_CPTRA_HW_ERRROR_ENC = 7'h54;
    parameter DMI_REG_CPTRA_FW_ERROR_ENC = 7'h55;
    //RW registers
    parameter DMI_REG_CPTRA_DBG_MANUF_SERVICE_REG = 7'h60;
    parameter DMI_REG_BOOTFSM_GO = 7'h61;
    
    //BOOT FSM
    typedef enum logic [2:0] {
        BOOT_IDLE   = 3'b000,
        BOOT_FUSE   = 3'b001,
        BOOT_FW_RST = 3'b010,
        BOOT_WAIT   = 3'b011,
        BOOT_DONE   = 3'b100
    } boot_fsm_state_e;

    //MAILBOX FSM
    typedef enum logic [2:0] {
        MBOX_IDLE         = 3'b000,
        MBOX_RDY_FOR_CMD  = 3'b001,
        MBOX_RDY_FOR_DLEN = 3'b011,
        MBOX_RDY_FOR_DATA = 3'b010,
        MBOX_EXECUTE_UC   = 3'b110,
        MBOX_EXECUTE_SOC  = 3'b100
    } mbox_fsm_state_e;

    //MAILBOX Status
    typedef enum logic [3:0] {
        CMD_BUSY      = 4'd0,
        DATA_READY    = 4'd1,
        CMD_COMPLETE  = 4'd2,
        CMD_FAILURE   = 4'd3
    } mbox_status_e;

    //Any request into soc ifc block
    typedef struct packed {
        logic   [SOC_IFC_ADDR_W-1:0] addr;
        logic   [SOC_IFC_DATA_W-1:0] wdata;
        logic   [SOC_IFC_USER_W-1:0] user;
        logic                        write;
        logic                        soc_req;
    } soc_ifc_req_t;
    // ECC protected data
    typedef struct packed {
        logic [MBOX_ECC_DATA_W-1:0] ecc;
        logic [MBOX_DATA_W-1:0]     data;
    } mbox_sram_data_t;
    //Request to mbox sram
    typedef struct packed {
        logic cs;
        logic we;
        logic [MBOX_ADDR_W-1:0] addr;
        mbox_sram_data_t wdata;
    } mbox_sram_req_t;
    //Response from mbox sram
    typedef struct packed {
        mbox_sram_data_t rdata;
    } mbox_sram_resp_t;

    typedef enum logic [1:0] {
        DEVICE_UNPROVISIONED = 2'b00,
        DEVICE_MANUFACTURING = 2'b01,
        DEVICE_PRODUCTION    = 2'b11
    } device_lifecycle_e;

    typedef struct packed {
        logic debug_locked;
        device_lifecycle_e device_lifecycle;
    } security_state_t;

    typedef struct packed {
        logic [31:0] MBOX_DLEN;
        logic [31:0] MBOX_DOUT;
        logic [31:0] MBOX_STATUS;
    } mbox_dmi_reg_t;

endpackage

`endif
