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

`include "caliptra_sva.svh"

module mbox 
    import mbox_pkg::*;
    import mbox_csr_pkg::*;
    #(
     parameter DMI_REG_MBOX_DLEN_ADDR = 7'h50
    ,parameter DMI_REG_MBOX_LOCK_ADDR = 7'h75
    ,parameter DMI_REG_MBOX_CMD_ADDR = 7'h76
    ,parameter DMI_REG_MBOX_EXECUTE_ADDR = 7'h77
    ,parameter DMI_REG_MBOX_STATUS_ADDR = 7'h52
     //Mailbox interface configuration
    ,parameter MBOX_IFC_DATA_W = 32
    ,parameter MBOX_IFC_USER_W = 32
    ,parameter MBOX_IFC_ADDR_W = 32
     //Mailbox size configuration
    ,parameter MBOX_SIZE_KB = 256
    ,parameter MBOX_DATA_W = 32
    ,parameter MBOX_ECC_DATA_W = 7
    ,localparam MBOX_SIZE_BYTES = MBOX_SIZE_KB * 1024
    ,localparam MBOX_SIZE_DWORDS = MBOX_SIZE_BYTES/4
    ,localparam MBOX_DATA_AND_ECC_W = MBOX_DATA_W + MBOX_ECC_DATA_W
    ,localparam MBOX_DEPTH = (MBOX_SIZE_KB * 1024 * 8) / MBOX_DATA_W
    ,localparam MBOX_ADDR_W = $clog2(MBOX_DEPTH)
    ,localparam MBOX_DEPTH_LOG2 = $clog2(MBOX_DEPTH)
    )
    (
    input logic         clk,
    input logic         rst_b,

    //mailbox request
    input logic                         req_dv,
    output logic                        req_hold,
    input logic                         dir_req_dv,
    input logic [MBOX_IFC_ADDR_W-1:0]   req_data_addr,
    input logic [MBOX_IFC_DATA_W-1:0]   req_data_wdata,
    input logic [MBOX_IFC_DATA_W/8-1:0] req_data_wstrb,
    input logic [MBOX_IFC_USER_W-1:0]   req_data_user,
    input logic                         req_data_write,
    input logic                         req_data_soc_req,

    output logic        mbox_error,

    output logic [MBOX_DATA_W-1:0] rdata,
    output logic [MBOX_DATA_W-1:0] dir_rdata,

    input logic sha_sram_req_dv,
    input logic [MBOX_ADDR_W-1:0] sha_sram_req_addr,
    output logic [MBOX_ECC_DATA_W-1:0] sha_sram_resp_ecc,
    output logic [MBOX_DATA_W-1:0] sha_sram_resp_data,
    output logic sha_sram_hold, // Throttle the SRAM requests when writing corrected ECC

    //dma req
    input logic dma_sram_req_dv,
    input logic dma_sram_req_write,
    input logic [MBOX_IFC_ADDR_W-1:0] dma_sram_req_addr,
    input logic [MBOX_IFC_DATA_W-1:0] dma_sram_req_wdata,
    output logic [MBOX_IFC_DATA_W-1:0] dma_sram_rdata,
    output logic dma_sram_hold, // Throttle the SRAM requests when SHA accel has access.
    output logic dma_sram_error,

    //SRAM interface
    output logic mbox_sram_req_cs,
    output logic mbox_sram_req_we,
    output logic [MBOX_ADDR_W-1:0] mbox_sram_req_addr,
    output logic [MBOX_ECC_DATA_W-1:0] mbox_sram_req_ecc,
    output logic [MBOX_DATA_W-1:0]     mbox_sram_req_wdata,
    input logic [MBOX_ECC_DATA_W-1:0] mbox_sram_resp_ecc,
    input logic [MBOX_DATA_W-1:0]     mbox_sram_resp_data,

    // ECC Status
    output logic sram_single_ecc_error,
    output logic sram_double_ecc_error,

    // Status
    output logic uc_mbox_lock,

    //interrupts
    output logic uc_mbox_data_avail,
    output logic soc_mbox_data_avail,
    output logic soc_req_mbox_lock,
    output mbox_protocol_error_t mbox_protocol_error,
    output logic mbox_inv_axi_user_axs,

    //DMI reg access
    input logic dmi_mbox_avail,
    input logic dmi_inc_rdptr,
    input logic dmi_inc_wrptr,
    input logic dmi_reg_wen,
    input logic dmi_reg_ren,
    input logic [31:0] dmi_reg_wdata,
    input logic [6:0]  dmi_reg_addr,
    output mbox_dmi_reg_t dmi_reg

);

//this module is used to instantiate a single mailbox instance
//requests within the address space of this mailbox are routed here from the top level

//State Machine
//The state machine controls the access to the mailbox.
//This will be used to ensure that protocol is followed and
//requests are granted only to the device that has locked the mailbox

//present and next state
mbox_fsm_state_e mbox_fsm_ns;
mbox_fsm_state_e mbox_fsm_ps;

//arcs between states
logic arc_FORCE_MBOX_UNLOCK;
logic arc_MBOX_IDLE_MBOX_RDY_FOR_CMD;
logic arc_MBOX_RDY_FOR_CMD_MBOX_RDY_FOR_DLEN;
logic arc_MBOX_RDY_FOR_DLEN_MBOX_RDY_FOR_DATA;
logic arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC;
logic arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC;
logic arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_TAP;
logic arc_MBOX_EXECUTE_UC_MBOX_IDLE;
logic arc_MBOX_EXECUTE_SOC_MBOX_IDLE;
logic arc_MBOX_EXECUTE_TAP_MBOX_IDLE;
logic arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_SOC;
logic arc_MBOX_EXECUTE_SOC_MBOX_EXECUTE_UC;
logic arc_MBOX_EXECUTE_TAP_MBOX_EXECUTE_UC;
logic arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_TAP;
logic arc_MBOX_RDY_FOR_CMD_MBOX_ERROR;
logic arc_MBOX_RDY_FOR_DLEN_MBOX_ERROR;
logic arc_MBOX_RDY_FOR_DATA_MBOX_ERROR;
logic arc_MBOX_EXECUTE_UC_MBOX_ERROR;
logic arc_MBOX_EXECUTE_SOC_MBOX_ERROR;
logic arc_MBOX_EXECUTE_TAP_MBOX_ERROR;
//sram
logic [MBOX_DATA_W-1:0] sram_wdata;
logic [MBOX_ECC_DATA_W-1:0] sram_wdata_ecc;
logic [MBOX_DEPTH_LOG2-1:0] sram_waddr;
logic [MBOX_DEPTH_LOG2-1:0] mbox_wrptr, mbox_wrptr_nxt;
logic mbox_wr_full, mbox_wr_full_nxt;
logic inc_wrptr;
logic [MBOX_DEPTH_LOG2-1:0] sram_rdaddr;
logic [MBOX_DEPTH_LOG2-1:0] mbox_rdptr, mbox_rdptr_nxt;
logic mbox_rd_full, mbox_rd_full_nxt;
logic inc_rdptr;
logic rst_mbox_rdptr;
logic rst_mbox_wrptr;
logic sram_rd_ecc_en;
logic [MBOX_DATA_W-1:0] sram_rdata;
logic [MBOX_ECC_DATA_W-1:0] sram_rdata_ecc;
logic [MBOX_DATA_W-1:0] sram_rdata_cor;
logic [MBOX_ECC_DATA_W-1:0] sram_rdata_cor_ecc;
logic sram_we;
logic mbox_protocol_sram_we;
logic mbox_protocol_sram_rd, mbox_protocol_sram_rd_f;
logic dir_req_dv_q, dir_req_rd_phase;
logic dir_req_wr_ph;
logic dma_sram_req_dv_q, dma_sram_req_rd_phase;
logic mask_rdata;
logic [MBOX_DEPTH_LOG2-1:0] dir_req_addr;

logic soc_has_lock, soc_has_lock_nxt;
logic uc_has_lock, uc_has_lock_nxt;
logic tap_has_lock, tap_has_lock_nxt;
logic req_data_uc_req;
logic valid_requester;
logic valid_receiver;

logic [MBOX_DEPTH_LOG2:0] mbox_dlen_in_dws;
logic latch_dlen_in_dws;
logic [MBOX_DEPTH_LOG2:0] dlen_in_dws, dlen_in_dws_nxt;
logic rdptr_inc_valid;
logic mbox_rd_valid, mbox_rd_valid_f;
logic wrptr_inc_valid;

mbox_protocol_error_t mbox_protocol_error_nxt;

logic tap_mode;
logic tap_mbox_data_avail;

//csr
logic [MBOX_DATA_W-1:0] csr_rdata;
logic read_error;
logic write_error;

mbox_csr__in_t hwif_in;
mbox_csr__out_t hwif_out;

assign mbox_error = read_error | write_error;

assign tap_mode = hwif_out.tap_mode.enabled.value;

assign uc_mbox_lock = uc_has_lock;

assign req_data_uc_req = ~req_data_soc_req;


//Determine if this is a valid request from the requester side
//1) uC requests are valid if uc has lock
//2) SoC requests are valid if soc has lock and it's the AXI USER that locked it 
always_comb valid_requester = hwif_out.mbox_lock.lock.value & 
                              ((req_data_uc_req & (uc_has_lock || (mbox_fsm_ps == MBOX_EXECUTE_UC))) |
                               (req_data_soc_req & soc_has_lock & (req_data_user == hwif_out.mbox_user.user.value[MBOX_IFC_USER_W-1:0])));

//Determine if this is a valid request from the receiver side
always_comb valid_receiver = hwif_out.mbox_lock.lock.value &
                             //Receiver is valid when in their execute state
                             //if they don't have the lock
                             ((req_data_uc_req & (soc_has_lock | tap_has_lock) & (mbox_fsm_ps == MBOX_EXECUTE_UC )) |
                              (req_data_soc_req & uc_has_lock & (mbox_fsm_ps == MBOX_EXECUTE_SOC)) |
                             //Receiver is valid when they are reading a response to their request
                             (valid_requester & ((soc_has_lock & (mbox_fsm_ps == MBOX_EXECUTE_SOC)) |
                                                 (uc_has_lock & (mbox_fsm_ps == MBOX_EXECUTE_UC)))));

//We want to mask read data when
//Invalid ID is trying to access the mailbox data
always_comb mask_rdata = hwif_out.mbox_dataout.dataout.swacc & ~valid_receiver;

//move from idle to rdy for command when lock is acquired
//we have a valid read, to the lock register, and it's not currently locked
always_comb arc_MBOX_IDLE_MBOX_RDY_FOR_CMD = (mbox_fsm_ps == MBOX_IDLE) & ~hwif_out.mbox_lock.lock.value & (hwif_out.mbox_lock.lock.swmod | hwif_in.mbox_lock.lock.hwset);
//move from rdy for cmd to rdy for dlen when cmd is written
always_comb arc_MBOX_RDY_FOR_CMD_MBOX_RDY_FOR_DLEN = (mbox_fsm_ps == MBOX_RDY_FOR_CMD) & ((hwif_out.mbox_cmd.command.swmod & valid_requester) | hwif_in.mbox_cmd.command.we);
//move from rdy for dlen to rdy for data when dlen is written
always_comb arc_MBOX_RDY_FOR_DLEN_MBOX_RDY_FOR_DATA = (mbox_fsm_ps == MBOX_RDY_FOR_DLEN) & ((hwif_out.mbox_dlen.length.swmod & valid_requester) | hwif_in.mbox_dlen.length.we);
//move from rdy for data to execute uc when SoC sets execute bit
always_comb arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC = (mbox_fsm_ps == MBOX_RDY_FOR_DATA) & hwif_out.mbox_execute.execute.value & (soc_has_lock | tap_has_lock);
//move from rdy for data to execute soc when uc writes to execute
always_comb arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC = (mbox_fsm_ps == MBOX_RDY_FOR_DATA) & hwif_out.mbox_execute.execute.value & uc_has_lock & ~tap_mode;
//move from rdy for data to execute tap when uc writes to execute in tap_mode
always_comb arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_TAP = (mbox_fsm_ps == MBOX_RDY_FOR_DATA) & hwif_out.mbox_execute.execute.value & uc_has_lock & tap_mode;
//move from rdy to execute to idle when uc resets execute
always_comb arc_MBOX_EXECUTE_UC_MBOX_IDLE = (mbox_fsm_ps == MBOX_EXECUTE_UC) & ~hwif_out.mbox_execute.execute.value;
always_comb arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_SOC = (mbox_fsm_ps == MBOX_EXECUTE_UC) & soc_has_lock & ~tap_mode & (hwif_out.mbox_status.status.value != CMD_BUSY);
always_comb arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_TAP = (mbox_fsm_ps == MBOX_EXECUTE_UC) & tap_has_lock & (hwif_out.mbox_status.status.value != CMD_BUSY);
//move from rdy to execute to idle when SoC resets execute
always_comb arc_MBOX_EXECUTE_SOC_MBOX_IDLE = (mbox_fsm_ps == MBOX_EXECUTE_SOC) & ~hwif_out.mbox_execute.execute.value;
always_comb arc_MBOX_EXECUTE_SOC_MBOX_EXECUTE_UC = (mbox_fsm_ps == MBOX_EXECUTE_SOC) & uc_has_lock & ~tap_mode & (hwif_out.mbox_status.status.value != CMD_BUSY);
//move from rdy to execute to idle when uc resets execute
always_comb arc_MBOX_EXECUTE_TAP_MBOX_IDLE = (mbox_fsm_ps == MBOX_EXECUTE_TAP) & ~hwif_out.mbox_execute.execute.value;
always_comb arc_MBOX_EXECUTE_TAP_MBOX_EXECUTE_UC = (mbox_fsm_ps == MBOX_EXECUTE_TAP) & uc_has_lock & tap_mode & ~tap_has_lock & (hwif_out.mbox_status.status.value != CMD_BUSY);
//move back to IDLE and unlock when force unlock is set
always_comb arc_FORCE_MBOX_UNLOCK = hwif_out.mbox_unlock.unlock.value;
// Detect error conditions and peg to the error state until serviced.
// Any register write (or read from mbox_dataout) by a VALID agent
// while in the incorrect state for access to that register results
// in transition to MBOX_ERROR and assertion of the protocol_error.
// Any register write or read by an INVALID agent results in the access
// being silently dropped.
// Assumption: uC (ROM, FMC, RT) will never make an invalid request.
// NOTE: Any AXI agent can trigger the error at any point during a uC->SOC flow
//       by writing to mbox_status (since it's a valid_receiver).
//       FIXED! valid_receiver is restricted by FSM state now.
always_comb arc_MBOX_RDY_FOR_CMD_MBOX_ERROR  = (mbox_fsm_ps == MBOX_RDY_FOR_CMD) &&
                                               req_dv && req_data_soc_req && ~req_hold && valid_requester &&
                                              (req_data_write ? (!hwif_out.mbox_cmd.command.swmod) :
                                                                (hwif_out.mbox_dataout.dataout.swacc));
always_comb arc_MBOX_RDY_FOR_DLEN_MBOX_ERROR = (mbox_fsm_ps == MBOX_RDY_FOR_DLEN) &&
                                               req_dv && req_data_soc_req && ~req_hold && valid_requester &&
                                              (req_data_write ? (!hwif_out.mbox_dlen.length.swmod) :
                                                                (hwif_out.mbox_dataout.dataout.swacc));
always_comb arc_MBOX_RDY_FOR_DATA_MBOX_ERROR = (mbox_fsm_ps == MBOX_RDY_FOR_DATA) &&
                                               req_dv && req_data_soc_req && ~req_hold && valid_requester &&
                                              (req_data_write ? (!(hwif_out.mbox_datain.datain.swmod || hwif_out.mbox_execute.execute.swmod)) :
                                                                (hwif_out.mbox_dataout.dataout.swacc));
always_comb arc_MBOX_EXECUTE_UC_MBOX_ERROR   = (mbox_fsm_ps == MBOX_EXECUTE_UC) &&
                                               req_dv && req_data_soc_req && ~req_hold && valid_requester &&
                                              (req_data_write ? (1'b1/* any write by 'valid' soc is illegal here */) :
                                                                (hwif_out.mbox_dataout.dataout.swacc));
always_comb arc_MBOX_EXECUTE_SOC_MBOX_ERROR  = (mbox_fsm_ps == MBOX_EXECUTE_SOC) &&
                                               req_dv && req_data_soc_req && ~req_hold &&
                                              (req_data_write ? ((valid_requester && !(hwif_out.mbox_execute.execute.swmod)) ||
                                                                 (uc_has_lock   && !(hwif_out.mbox_status.status.swmod))) :
                                                                (1'b0 /* any read allowed by SoC during this stage; dataout consumption is expected */));
always_comb arc_MBOX_EXECUTE_TAP_MBOX_ERROR  = 1'b0;

//capture the dlen when we change to execute states, this ensures that only the dlen programmed
//by the client filling the mailbox is used for masking the data
//Store the dlen as a ptr to the last entry
always_comb latch_dlen_in_dws = arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC | arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC | arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_SOC |
                                arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_TAP | arc_MBOX_EXECUTE_TAP_MBOX_EXECUTE_UC | arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_TAP;
always_comb mbox_dlen_in_dws = (hwif_out.mbox_dlen.length.value >= MBOX_SIZE_BYTES) ? MBOX_SIZE_DWORDS[MBOX_DEPTH_LOG2:0] :
                               (hwif_out.mbox_dlen.length.value[MBOX_DEPTH_LOG2+2:2]) + (hwif_out.mbox_dlen.length.value[0] | hwif_out.mbox_dlen.length.value[1]);
//latched dlen is the smaller of the programmed dlen or the current wrptr
//this avoids a case where a sender writes less than programmed and the receiver can read beyond that
//if the mailbox is full (flag set when writing last entry), always take the programmed dlen
always_comb dlen_in_dws_nxt = (~mbox_wr_full & ({1'b0,mbox_wrptr} < mbox_dlen_in_dws)) ? {1'b0,mbox_wrptr} : mbox_dlen_in_dws;

// Restrict the read pointer from passing the dlen or rolling over
always_comb rdptr_inc_valid = ({1'b0,mbox_rdptr} < dlen_in_dws) & (mbox_rdptr < (MBOX_SIZE_DWORDS-1));
// No more valid reads if we read the last entry
// On pre-load of entry 0, ensure that next dlen isn't 0
// Restrict reads once read pointer has passed the dlen
always_comb mbox_rd_valid = (rst_mbox_rdptr & (dlen_in_dws_nxt != 0)) | (~rst_mbox_rdptr & ~mbox_rd_full & ({1'b0,mbox_rdptr} < dlen_in_dws));
// Restrict the write pointer from rolling over
always_comb wrptr_inc_valid = mbox_wrptr < (MBOX_SIZE_DWORDS-1);


always_comb begin : mbox_fsm_combo
    uc_has_lock_nxt = 0;
    soc_has_lock_nxt = 0;
    tap_has_lock_nxt = 0;
    rst_mbox_rdptr = 0; //resetting the read pointer will pre-load dataout
    rst_mbox_wrptr = 0;
    inc_rdptr = 0;
    inc_wrptr = 0;
    uc_mbox_data_avail = 0;
    soc_mbox_data_avail = 0;
    tap_mbox_data_avail = 0;
    mbox_protocol_error_nxt = '{default: 0};
    mbox_fsm_ns = mbox_fsm_ps;

    unique case (mbox_fsm_ps)
        MBOX_IDLE: begin
            if (arc_MBOX_IDLE_MBOX_RDY_FOR_CMD) begin
                mbox_fsm_ns = MBOX_RDY_FOR_CMD;
                soc_has_lock_nxt = req_data_soc_req & hwif_out.mbox_lock.lock.swmod; //soc requested the lock
                uc_has_lock_nxt = ~req_data_soc_req & hwif_out.mbox_lock.lock.swmod; //uc requested the lock
                tap_has_lock_nxt = hwif_in.mbox_lock.lock.hwset; //tap set the lock
            end
            // Flag a non-fatal error, but don't change states, if mbox is already IDLE
            // when an unexpected SOC access happens
            if (req_dv && req_data_soc_req && ~req_hold && (req_data_write || hwif_out.mbox_dataout.dataout.swacc)) begin
                mbox_protocol_error_nxt.axs_without_lock = 1'b1;
            end
        end
        MBOX_RDY_FOR_CMD: begin
            if (arc_MBOX_RDY_FOR_CMD_MBOX_RDY_FOR_DLEN) begin
                mbox_fsm_ns = MBOX_RDY_FOR_DLEN;
            end
            else if (arc_MBOX_RDY_FOR_CMD_MBOX_ERROR) begin
                mbox_fsm_ns = MBOX_ERROR;
                mbox_protocol_error_nxt.axs_incorrect_order = 1'b1;
            end
            if (arc_FORCE_MBOX_UNLOCK) begin
                mbox_fsm_ns = MBOX_IDLE;
                mbox_protocol_error_nxt = '{default: 0};
            end
        end
        MBOX_RDY_FOR_DLEN: begin
            if (arc_MBOX_RDY_FOR_DLEN_MBOX_RDY_FOR_DATA) begin
                mbox_fsm_ns = MBOX_RDY_FOR_DATA;
                rst_mbox_wrptr = 1;
            end
            else if (arc_MBOX_RDY_FOR_DLEN_MBOX_ERROR) begin
                mbox_fsm_ns = MBOX_ERROR;
                mbox_protocol_error_nxt.axs_incorrect_order = 1'b1;
            end
            if (arc_FORCE_MBOX_UNLOCK) begin
                mbox_fsm_ns = MBOX_IDLE;
                mbox_protocol_error_nxt = '{default: 0};
            end
        end
        MBOX_RDY_FOR_DATA: begin
            //update the write pointers to sram when accessing datain register
            inc_wrptr = (hwif_out.mbox_datain.datain.swmod & valid_requester & ~req_hold) |
                        (dmi_inc_wrptr & tap_has_lock);
            if (arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC) begin
                mbox_fsm_ns = MBOX_EXECUTE_UC;
                //reset wrptr so receiver can write response
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
            else if (arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC) begin
                mbox_fsm_ns = MBOX_EXECUTE_SOC;
                //reset wrptr so receiver can write response
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
            else if (arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_TAP) begin
                mbox_fsm_ns = MBOX_EXECUTE_TAP;
                //reset wrptr so receiver can write response
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
            else if (arc_MBOX_RDY_FOR_DATA_MBOX_ERROR) begin
                mbox_fsm_ns = MBOX_ERROR;
                mbox_protocol_error_nxt.axs_incorrect_order = 1'b1;
            end
            if (arc_FORCE_MBOX_UNLOCK) begin
                mbox_fsm_ns = MBOX_IDLE;
                inc_wrptr = 0;
                inc_rdptr = 0;
                mbox_protocol_error_nxt = '{default: 0};
            end
        end
        //SoC set execute, data is for the uC
        //only uC can read from mbox
        //only uC can write to datain here to respond to SoC
        MBOX_EXECUTE_UC: begin
            uc_mbox_data_avail = 1;
            inc_rdptr = dmi_inc_rdptr | (hwif_out.mbox_dataout.dataout.swacc & req_data_uc_req & ~req_hold);
            inc_wrptr = hwif_out.mbox_datain.datain.swmod & req_data_uc_req & ~req_hold;
            if (arc_MBOX_EXECUTE_UC_MBOX_IDLE) begin
                mbox_fsm_ns = MBOX_IDLE;
            end
            else if (arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_SOC) begin
                mbox_fsm_ns = MBOX_EXECUTE_SOC;
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
            else if (arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_TAP) begin
                mbox_fsm_ns = MBOX_EXECUTE_TAP;
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
            else if (arc_MBOX_EXECUTE_UC_MBOX_ERROR) begin
                mbox_fsm_ns = MBOX_ERROR;
                mbox_protocol_error_nxt.axs_incorrect_order = 1'b1;
            end
            if (arc_FORCE_MBOX_UNLOCK) begin
                mbox_fsm_ns = MBOX_IDLE;
                inc_wrptr = 0;
                inc_rdptr = 0;
                mbox_protocol_error_nxt = '{default: 0};
            end
        end
        //uC set execute, data is for the SoC
        //If we're here, restrict reading to the AXI USER that requested the data
        //Only SoC can read from mbox
        //Only SoC can write to datain here to respond to uC
        MBOX_EXECUTE_SOC: begin
            soc_mbox_data_avail = 1;
            inc_rdptr = (dmi_inc_rdptr | (hwif_out.mbox_dataout.dataout.swacc & req_data_soc_req & valid_receiver & ~req_hold));
            if (arc_MBOX_EXECUTE_SOC_MBOX_IDLE) begin
                mbox_fsm_ns = MBOX_IDLE;
            end
            else if (arc_MBOX_EXECUTE_SOC_MBOX_EXECUTE_UC) begin
                mbox_fsm_ns = MBOX_EXECUTE_UC;
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
            else if (arc_MBOX_EXECUTE_SOC_MBOX_ERROR) begin
                mbox_fsm_ns = MBOX_ERROR;
                mbox_protocol_error_nxt.axs_incorrect_order = 1'b1;
            end
            if (arc_FORCE_MBOX_UNLOCK) begin
                mbox_fsm_ns = MBOX_IDLE;
                inc_wrptr = 0;
                inc_rdptr = 0;
                mbox_protocol_error_nxt = '{default: 0};
            end
        end
        MBOX_EXECUTE_TAP: begin
            tap_mbox_data_avail = 1;
            inc_rdptr = (dmi_inc_rdptr);
            inc_wrptr = (dmi_inc_wrptr);
            if (arc_MBOX_EXECUTE_TAP_MBOX_IDLE) begin
                mbox_fsm_ns = MBOX_IDLE;
            end
            else if (arc_MBOX_EXECUTE_TAP_MBOX_EXECUTE_UC) begin
                mbox_fsm_ns = MBOX_EXECUTE_UC;
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
            else if (arc_MBOX_EXECUTE_TAP_MBOX_ERROR) begin
                mbox_fsm_ns = MBOX_ERROR;
                mbox_protocol_error_nxt.axs_incorrect_order = 1'b1;
            end
            if (arc_FORCE_MBOX_UNLOCK) begin
                mbox_fsm_ns = MBOX_IDLE;
                inc_wrptr = 0;
                inc_rdptr = 0;
                mbox_protocol_error_nxt = '{default: 0};
            end
        end
        MBOX_ERROR: begin
            mbox_protocol_error_nxt = '{default: 0};
            if (arc_FORCE_MBOX_UNLOCK) begin
                mbox_fsm_ns = MBOX_IDLE;
                mbox_protocol_error_nxt = '{default: 0};
            end
        end

        default: begin
            mbox_fsm_ns = mbox_fsm_ps;
        end
    endcase
end

// Any ol' AXI_USER is fine for reg-reads (except dataout)
// NOTE: This only captures accesses by AXI agents that are valid, but do not
//       have lock. Invalid agent accesses are blocked by arbiter.
assign mbox_inv_axi_user_axs = req_dv && req_data_soc_req && !req_hold &&
                               !valid_requester && !valid_receiver &&
                               (req_data_write || hwif_out.mbox_dataout.dataout.swacc);


//increment read ptr only if its allowed
always_comb mbox_protocol_sram_rd = inc_rdptr | rst_mbox_rdptr;
always_comb mbox_protocol_sram_we = inc_wrptr & ~mbox_wr_full;

//flops
always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b)begin
        mbox_fsm_ps <= MBOX_IDLE;
        soc_has_lock <= '0;
        uc_has_lock <= '0;
        tap_has_lock <= '0;
        dir_req_rd_phase <= '0;
        dma_sram_req_rd_phase <= '0;
        mbox_wrptr <= '0;
        mbox_wr_full <= '0;
        mbox_rdptr <= '0;
        mbox_rd_full <= '0;
        mbox_rd_valid_f <= '0;
        mbox_protocol_sram_rd_f <= '0;
        dlen_in_dws <= '0;
        mbox_protocol_error <= '0;
        sram_rd_ecc_en <= '0;
    end
    else begin
        mbox_fsm_ps <= mbox_fsm_ns;
        soc_has_lock <= arc_MBOX_IDLE_MBOX_RDY_FOR_CMD ? soc_has_lock_nxt : 
                        hwif_out.mbox_lock.lock.value ? soc_has_lock : '0;
        uc_has_lock  <= arc_MBOX_IDLE_MBOX_RDY_FOR_CMD ? uc_has_lock_nxt : 
                        hwif_out.mbox_lock.lock.value ? uc_has_lock : '0;
        tap_has_lock <= arc_MBOX_IDLE_MBOX_RDY_FOR_CMD ? tap_has_lock_nxt : 
                        hwif_out.mbox_lock.lock.value ? tap_has_lock : '0;
        dir_req_rd_phase <= dir_req_dv_q & ~sha_sram_req_dv & ~(dma_sram_req_dv_q & dma_sram_req_write) & ~req_data_write;
        dma_sram_req_rd_phase <= dma_sram_req_dv_q & ~sha_sram_req_dv & ~dma_sram_req_write;
        mbox_wrptr <= ((inc_wrptr & wrptr_inc_valid) | rst_mbox_wrptr) ? mbox_wrptr_nxt : mbox_wrptr;
        mbox_wr_full <= (inc_wrptr | rst_mbox_wrptr) ? mbox_wr_full_nxt : mbox_wr_full;
        mbox_rdptr <= (mbox_protocol_sram_rd) ? mbox_rdptr_nxt : mbox_rdptr;
        mbox_protocol_sram_rd_f <= (mbox_protocol_sram_rd | mbox_protocol_sram_rd_f) ? mbox_protocol_sram_rd : mbox_protocol_sram_rd_f;
        mbox_rd_full <= (inc_rdptr | rst_mbox_rdptr) ? mbox_rd_full_nxt : mbox_rd_full;
        mbox_rd_valid_f <= (mbox_rd_valid | mbox_rd_valid_f) ? mbox_rd_valid : mbox_rd_valid_f;
                             
        dlen_in_dws <= latch_dlen_in_dws ? dlen_in_dws_nxt : dlen_in_dws;                    
        mbox_protocol_error <= mbox_protocol_error_nxt;
        //enable ecc for mbox protocol, direct reads, or SHA direct reads
        sram_rd_ecc_en <= mbox_protocol_sram_rd | (dir_req_dv_q & ~sha_sram_req_dv & ~req_data_write) | (dma_sram_req_dv_q & ~dma_sram_req_write) | sha_sram_req_dv;
    end
end

always_comb dma_sram_req_dv_q = dma_sram_req_dv & hwif_out.mbox_lock.lock.value & uc_has_lock & ~dma_sram_req_rd_phase;
//need to hold direct read accesses for 1 clock to get response
//create a qualified direct request signal that is masked during the data phase
//hold the interface to insert wait state when direct request comes
//mask the request and hold the interface if SHA is using the mailbox
//hold when a read to dataout is coming and we haven't updated the data yet
always_comb dir_req_dv_q = (dir_req_dv & ~dir_req_rd_phase & hwif_out.mbox_lock.lock.value & (uc_has_lock | (mbox_fsm_ps == MBOX_EXECUTE_UC))) | 
                           (dma_sram_req_dv_q) |
                            sha_sram_req_dv;
always_comb dir_req_wr_ph = dir_req_dv_q & ~sha_sram_req_dv & ((~dma_sram_req_dv_q & req_data_write) | (dma_sram_req_dv_q & dma_sram_req_write));
always_comb dir_req_addr = sha_sram_req_dv   ? sha_sram_req_addr :
                           dma_sram_req_dv_q ? dma_sram_req_addr[MBOX_DEPTH_LOG2+1:2] :
                                               req_data_addr[MBOX_DEPTH_LOG2+1:2];

// Arb precedence:
//   SHA accelerator: highest
//   DMA (with lock): next
//   Direct request:  lowest
// No arbitration/round-robin -- this is strictly observed for every txn

                       //Direct read from uC, stall 1 clock dv_q will be de-asserted second clock
always_comb req_hold = (dir_req_dv_q & ~sha_sram_req_dv & ~dma_sram_req_dv_q & ~req_data_write) |
                       //Direct access from uC while sha accelerator or DMA is accessing
                       (dir_req_dv & ~dir_req_rd_phase & (sha_sram_req_dv | dma_sram_req_dv_q | dma_sram_req_rd_phase)) |
                       //in an update cycle for dataout register
                       (hwif_out.mbox_dataout.dataout.swacc & mbox_protocol_sram_rd_f);

always_comb dma_sram_hold = (sha_sram_req_dv && !dma_sram_req_rd_phase) || (dma_sram_req_dv_q && !dma_sram_req_write);
always_comb sha_sram_hold = 1'b0;

//SRAM interface
always_comb sram_we = dir_req_wr_ph | mbox_protocol_sram_we;
//align the direct address to a word
always_comb sram_rdaddr = dir_req_dv_q ? dir_req_addr : 
                          rst_mbox_rdptr ? 'd0 : mbox_rdptr;
always_comb sram_waddr = dir_req_dv_q    ? dir_req_addr : mbox_wrptr;
//data phase after request for direct access
//We want to mask the read data for certain accesses
always_comb rdata = ({MBOX_DATA_W{~mask_rdata}} & csr_rdata);
always_comb dir_rdata = dir_req_rd_phase ? sram_rdata_cor : '0;
always_comb dma_sram_rdata = dma_sram_req_rd_phase ? sram_rdata_cor : '0;

always_comb dma_sram_error = 1'b0; // TODO: ecc error?

always_comb begin: mbox_sram_inf
    //read live on direct access, or when pointer has been incremented, for pre-load on read pointer reset, or ecc correction
    mbox_sram_req_cs = dir_req_dv_q | mbox_protocol_sram_we | mbox_protocol_sram_rd;
    mbox_sram_req_we = sram_we;
    mbox_sram_req_addr = sram_we ? sram_waddr : sram_rdaddr;
    mbox_sram_req_wdata = sram_wdata;
    mbox_sram_req_ecc  = sram_wdata_ecc;

    sram_rdata     = mbox_sram_resp_data;
    sram_rdata_ecc = mbox_sram_resp_ecc;
    sha_sram_resp_ecc  = sram_rdata_cor_ecc;
    sha_sram_resp_data = sram_rdata_cor;
end

// From RISC-V core beh_lib.sv
// 32-bit data width hardcoded
// 7-bit ECC width hardcoded
rvecc_encode mbox_ecc_encode (
    .din    (sram_wdata    ),
    .ecc_out(sram_wdata_ecc)
);
// synthesis translate_off
`ifdef CLP_ASSERT_ON 
initial assert(MBOX_DATA_W == 32) else
    $error("%m::rvecc_encode supports 32-bit data width; must change SRAM ECC implementation to support MBOX_DATA_W = %d", MBOX_DATA_W);
`endif
// synthesis translate_on
rvecc_decode ecc_decode (
    .en              (sram_rd_ecc_en       ),
    .sed_ded         ( 1'b0                ),    // 1 : means only detection
    .din             (sram_rdata           ),
    .ecc_in          (sram_rdata_ecc       ),
    .dout            (sram_rdata_cor       ),
    .ecc_out         (sram_rdata_cor_ecc   ),
    .single_ecc_error(sram_single_ecc_error), // TODO use to flag write-back
    .double_ecc_error(sram_double_ecc_error)  // TODO use to flag command error
);

//control for sram write and read pointer
//SoC access is controlled by mailbox, each subsequent read or write increments the pointer
//uC accesses can specify the specific read or write address, or rely on mailbox to control
//if tap has lock or is responding to a request it can write instead
always_comb sram_wdata = (dma_sram_req_dv_q && dma_sram_req_write )                           ? dma_sram_req_wdata : 
                         (dmi_inc_wrptr & ((mbox_fsm_ps == MBOX_EXECUTE_TAP) | tap_has_lock)) ? dmi_reg_wdata : 
                                                                                                req_data_wdata;

//in ready for data state we increment the pointer each time we write
always_comb mbox_wrptr_nxt = rst_mbox_wrptr ? '0 :
                             (inc_wrptr & wrptr_inc_valid) ? mbox_wrptr + 'd1 : 
                                                             mbox_wrptr;

always_comb mbox_wr_full_nxt = rst_mbox_wrptr ? '0 : inc_wrptr & (mbox_wrptr == (MBOX_DEPTH-1));

//in execute state we increment the pointer each time we write
always_comb mbox_rdptr_nxt = rst_mbox_rdptr ? 'd1 :
                             (inc_rdptr & rdptr_inc_valid) ? mbox_rdptr + 'd1 : 
                                                             mbox_rdptr;

always_comb mbox_rd_full_nxt = rst_mbox_rdptr ? '0 : inc_rdptr & (mbox_rdptr == (MBOX_DEPTH-1));

//Intterupts
//Notify uC when it has the lock and SoC is requesting the lock
always_comb soc_req_mbox_lock = hwif_out.mbox_lock.lock.value & uc_has_lock & hwif_out.mbox_lock.lock.swmod & req_data_soc_req;

always_comb hwif_in.cptra_rst_b = rst_b;
always_comb hwif_in.mbox_user.user.next = 32'(req_data_user);
always_comb hwif_in.mbox_status.mbox_fsm_ps.next = mbox_fsm_ps;

always_comb hwif_in.soc_req = req_data_soc_req;
//check the requesting ID:
//don't update mailbox data if lock hasn't been acquired
//if uc has the lock, check that this request is from uc
//if soc has the lock, check that this request is from soc and ID attributes match
always_comb hwif_in.valid_requester = valid_requester;
always_comb hwif_in.valid_receiver = valid_receiver;

//indicate that requesting ID is setting the lock
always_comb hwif_in.lock_set = arc_MBOX_IDLE_MBOX_RDY_FOR_CMD;

//update dataout
always_comb hwif_in.mbox_dataout.dataout.swwe = '0; //no sw write enable, but need the storage element
//update dataout whenever we read from the sram for a dataout access
//we load the first entry on the arc to execute
always_comb hwif_in.mbox_dataout.dataout.we = mbox_protocol_sram_rd_f;
always_comb hwif_in.mbox_dataout.dataout.next = mbox_rd_valid_f ? sram_rdata_cor : '0;
//clear the lock when moving from execute to idle
always_comb hwif_in.mbox_lock.lock.hwclr = arc_MBOX_EXECUTE_SOC_MBOX_IDLE | arc_MBOX_EXECUTE_UC_MBOX_IDLE | arc_MBOX_EXECUTE_TAP_MBOX_IDLE | arc_FORCE_MBOX_UNLOCK;
//clear the mailbox status when we go back to IDLE
always_comb hwif_in.mbox_status.status.hwclr = arc_MBOX_EXECUTE_SOC_MBOX_IDLE | arc_MBOX_EXECUTE_UC_MBOX_IDLE | arc_MBOX_EXECUTE_TAP_MBOX_IDLE | arc_FORCE_MBOX_UNLOCK;
//clear the execute register when we force unlock
always_comb hwif_in.mbox_execute.execute.hwclr = arc_FORCE_MBOX_UNLOCK;
// Set mbox_csr status fields in response to ECC errors
always_comb hwif_in.mbox_status.ecc_single_error.hwset = sram_single_ecc_error;
always_comb hwif_in.mbox_status.ecc_double_error.hwset = sram_double_ecc_error;
always_comb hwif_in.mbox_status.soc_has_lock.next = soc_has_lock;
always_comb hwif_in.mbox_status.tap_has_lock.next = tap_has_lock;
//Assign valid read pointer bits to status register
always_comb begin
    hwif_in.mbox_status.mbox_rdptr.next = '0;
    for (int i = 0; i < MBOX_DEPTH_LOG2; i++) begin //rdptr status register is hardcoded to 256KB depth
        hwif_in.mbox_status.mbox_rdptr.next[i] = mbox_rdptr[i];
    end
end

//Set the lock if tap is reading a 0
always_comb hwif_in.mbox_lock.lock.hwset = dmi_mbox_avail & dmi_reg_ren & (dmi_reg_addr == DMI_REG_MBOX_LOCK_ADDR) & ~hwif_out.mbox_lock.lock.value & ~hwif_out.mbox_lock.lock.swmod;

always_comb hwif_in.mbox_cmd.command.we = dmi_mbox_avail & dmi_reg_wen & (dmi_reg_addr == DMI_REG_MBOX_CMD_ADDR) & (tap_has_lock | (mbox_fsm_ps == MBOX_EXECUTE_TAP));
always_comb hwif_in.mbox_cmd.command.next = dmi_reg_wdata;

always_comb hwif_in.mbox_dlen.length.we = dmi_mbox_avail & dmi_reg_wen & (dmi_reg_addr == DMI_REG_MBOX_DLEN_ADDR) & (tap_has_lock | (mbox_fsm_ps == MBOX_EXECUTE_TAP));
always_comb hwif_in.mbox_dlen.length.next = dmi_reg_wdata;

always_comb hwif_in.mbox_status.status.we = dmi_mbox_avail & dmi_reg_wen & (dmi_reg_addr == DMI_REG_MBOX_STATUS_ADDR) & (tap_has_lock | (mbox_fsm_ps == MBOX_EXECUTE_TAP));
always_comb hwif_in.mbox_status.status.next = dmi_reg_wdata[3:0];

always_comb hwif_in.mbox_execute.execute.we = dmi_mbox_avail & dmi_reg_wen & (dmi_reg_addr == DMI_REG_MBOX_EXECUTE_ADDR) & (tap_has_lock);
always_comb hwif_in.mbox_execute.execute.next = dmi_reg_wdata[0];


//return a 1 on the lock if software is requesting the lock to avoid tap and sw thinking they got the lock
//always show locked if dmi mbox avail not set
always_comb dmi_reg.MBOX_LOCK = {31'b0, (hwif_out.mbox_lock.lock.value | hwif_out.mbox_lock.lock.swmod | ~dmi_mbox_avail)};
always_comb dmi_reg.MBOX_CMD = hwif_out.mbox_cmd.command.value;
always_comb dmi_reg.MBOX_DLEN = hwif_out.mbox_dlen.length.value;
always_comb dmi_reg.MBOX_DOUT = hwif_out.mbox_dataout.dataout.value;
always_comb dmi_reg.MBOX_STATUS = {5'b0,                                        /* [31:27] */
                                   hwif_out.mbox_status.tap_has_lock.value,     /* [26] */
                                   hwif_out.mbox_status.mbox_rdptr.value,       /* [25:10]*/
                                   hwif_out.mbox_status.soc_has_lock.value,     /* [9] */
                                   hwif_out.mbox_status.mbox_fsm_ps.value,      /* [8:6] */
                                   hwif_out.mbox_status.ecc_double_error.value, /* [5] */
                                   hwif_out.mbox_status.ecc_single_error.value, /* [4] */
                                   hwif_out.mbox_status.status.value            /* [3:0] */
                                   };

logic [MBOX_IFC_DATA_W-1:0] s_cpuif_wr_biten;
logic s_cpuif_req_stall_wr_nc;
logic s_cpuif_req_stall_rd_nc;
logic s_cpuif_rd_ack_nc;
logic s_cpuif_wr_ack_nc;

genvar i;
generate
    for (i=0;i<MBOX_IFC_DATA_W;i++) begin: assign_biten_from_wstrb
        assign s_cpuif_wr_biten[i] = req_data_wstrb[i/8];
    end
endgenerate

mbox_csr
mbox_csr1(
    .clk(clk),
    .rst('0),

    .s_cpuif_req(req_dv & ~dir_req_dv),
    .s_cpuif_req_is_wr(req_data_write),
    .s_cpuif_addr(req_data_addr[MBOX_CSR_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data(req_data_wdata),
    .s_cpuif_wr_biten(s_cpuif_wr_biten),
    .s_cpuif_req_stall_wr(s_cpuif_req_stall_wr_nc),
    .s_cpuif_req_stall_rd(s_cpuif_req_stall_rd_nc),
    .s_cpuif_rd_ack(s_cpuif_rd_ack_nc),
    .s_cpuif_rd_err(read_error),
    .s_cpuif_rd_data(csr_rdata),
    .s_cpuif_wr_ack(s_cpuif_wr_ack_nc),
    .s_cpuif_wr_err(write_error),

    .hwif_in(hwif_in),
    .hwif_out(hwif_out)
);

`CALIPTRA_ASSERT_MUTEX(ERR_MBOX_ACCESS_MUTEX, {dir_req_dv_q , mbox_protocol_sram_we , mbox_protocol_sram_rd }, clk, !rst_b)
//`CALIPTRA_ASSERT_MUTEX(ERR_MBOX_DIR_SHA_COLLISION, {dir_req_dv, sha_sram_req_dv}, clk, !rst_b)
`CALIPTRA_ASSERT_NEVER(ERR_MBOX_DIR_REQ_FROM_SOC, (dir_req_dv & req_data_soc_req), clk, !rst_b)
`CALIPTRA_ASSERT_MUTEX(ERR_MBOX_LOCK_MUTEX, {soc_has_lock, uc_has_lock, tap_has_lock}, clk, !rst_b)
endmodule
