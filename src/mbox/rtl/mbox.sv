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

`include "mbox_defines.svh"

module mbox #(
     parameter DATA_W = 32
    ,parameter SIZE_KB = 128
    ,parameter BASE_ADDR = 0
    )
    (
    input logic        clk,
    input logic        rst_b,

    //mailbox request
    input logic        req_dv,
    input mbox_req_t   req_data,
    output logic       mbox_error,

    output logic [DATA_W-1:0] rdata,

    //interrupts
    output logic       uc_mbox_data_avail,
    output logic       soc_mbox_data_avail

);

localparam DEPTH = (SIZE_KB * 1024 * 8) / DATA_W;
//bits of addr used to address the mailbox
localparam MBOX_ADDR_MSB = $clog2(SIZE_KB*1024)-1;
localparam MBOX_ADDR_LSB = $clog2(DATA_W/8);
//ADDRESS MAP
//DIRECT ADDRESSING from BASE through MBOX size
//Control registers start after direct address space (base + size in bytes)
localparam MBOX_CR_BASE = BASE_ADDR + (SIZE_KB * 1024);

//32b Control registers
localparam MBOX_LOCK_ADDR    = MBOX_CR_BASE + 'h0_0000;
localparam MBOX_CMD_ADDR     = MBOX_CR_BASE + 'h0_0004;
localparam MBOX_DLEN_ADDR    = MBOX_CR_BASE + 'h0_0008;
localparam MBOX_DATAIN_ADDR  = MBOX_CR_BASE + 'h0_000C;
localparam MBOX_DATAOUT_ADDR = MBOX_CR_BASE + 'h0_0010;
localparam MBOX_EXEC_ADDR    = MBOX_CR_BASE + 'h0_0014;
localparam MBOX_STATUS_ADDR  = MBOX_CR_BASE + 'h0_0018;

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
logic arc_MBOX_IDLE_MBOX_RDY_FOR_CMD;
logic arc_MBOX_RDY_FOR_CMD_MBOX_RDY_FOR_DLEN;
logic arc_MBOX_RDY_FOR_DLEN_MBOX_RDY_FOR_DATA;
logic arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC;
logic arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC;
logic arc_MBOX_EXECUTE_UC_MBOX_IDLE;
logic arc_MBOX_EXECUTE_SOC_MBOX_IDLE;

//sram
logic [DATA_W-1:0] sram_wdata;
logic [$clog2(DEPTH)-1:0] sram_waddr;
logic [$clog2(DEPTH)-1:0] mbox_wrptr, mbox_wrptr_nxt;
logic inc_wrptr;
logic [$clog2(DEPTH)-1:0] sram_rdaddr;
logic [$clog2(DEPTH)-1:0] mbox_rdptr, mbox_rdptr_nxt;
logic inc_rdptr;
logic rst_mbox_ptr;
logic [DATA_W-1:0] sram_rdata;
logic sram_we, sram_rd;

//registers
logic lock_cr, lock_cr_nxt;
logic soc_has_lock, soc_has_lock_nxt;
logic lock_cr_en;
logic [MBOX_USER_W-1:0] user_cr, user_cr_nxt;
logic user_cr_en;
logic [31:0] cmd_cr, cmd_cr_nxt;
logic cmd_cr_en;
logic [31:0] dlen_cr, dlen_cr_nxt;
logic dlen_cr_en;
logic execute_cr, execute_cr_nxt;
logic execute_cr_en;
logic [31:0] status_cr, status_cr_nxt;
logic status_cr_en;

//controls
logic valid_read_cycle;
logic read_error;
logic valid_write_cycle;
logic write_error;

assign mbox_error = read_error | write_error;

//move from idle to rdy for command when lock is acquired
//we have a valid read, to the lock register, and it's not currently locked
always_comb arc_MBOX_IDLE_MBOX_RDY_FOR_CMD = valid_read_cycle & ~lock_cr & (req_data.addr == MBOX_LOCK_ADDR);
//move from rdy for cmd to rdy for dlen when cmd is written
always_comb arc_MBOX_RDY_FOR_CMD_MBOX_RDY_FOR_DLEN = cmd_cr_en;
//move from rdy for dlen to rdy for data when dlen is written
always_comb arc_MBOX_RDY_FOR_DLEN_MBOX_RDY_FOR_DATA = dlen_cr_en;
//move from rdy for data to execute uc when SoC sets execute bit
always_comb arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC = execute_cr & soc_has_lock;
//move from rdy for data to execute soc when uc writes to execute
always_comb arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC = execute_cr & ~soc_has_lock;
//move from rdy to execute to idle when uc resets execute
always_comb arc_MBOX_EXECUTE_UC_MBOX_IDLE = ~execute_cr;
//move from rdy to execute to idle when SoC resets execute
always_comb arc_MBOX_EXECUTE_SOC_MBOX_IDLE = ~execute_cr;

always_comb begin : mbox_fsm_combo
    lock_cr_en = 0;
    user_cr_en = 0;
    lock_cr_nxt = lock_cr;
    user_cr_nxt = user_cr;
    soc_has_lock_nxt = 0;
    rst_mbox_ptr = 0;
    uc_mbox_data_avail = 0;
    soc_mbox_data_avail = 0;
    mbox_fsm_ns = mbox_fsm_ps;

    unique casez (mbox_fsm_ps)
        MBOX_IDLE: begin
            if (arc_MBOX_IDLE_MBOX_RDY_FOR_CMD) begin
                mbox_fsm_ns = MBOX_RDY_FOR_CMD;
                lock_cr_en = 1;
                lock_cr_nxt = 1; //set the lock
                user_cr_en = 1;
                user_cr_nxt = req_data.user; //store the user attribute
                soc_has_lock_nxt = req_data.soc_req; //remember if soc or uc requested the lock
            end
        end
        MBOX_RDY_FOR_CMD: begin
            if (arc_MBOX_RDY_FOR_CMD_MBOX_RDY_FOR_DLEN) begin
                mbox_fsm_ns = MBOX_RDY_FOR_DLEN;
            end
        end
        MBOX_RDY_FOR_DLEN: begin
            if (arc_MBOX_RDY_FOR_DLEN_MBOX_RDY_FOR_DATA) begin
                mbox_fsm_ns = MBOX_RDY_FOR_DATA;
            end
        end
        MBOX_RDY_FOR_DATA: begin
            if (arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC) begin
                mbox_fsm_ns = MBOX_EXECUTE_UC;
            end
            else if (arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC) begin
                mbox_fsm_ns = MBOX_EXECUTE_SOC;
            end
        end
        MBOX_EXECUTE_UC: begin
            uc_mbox_data_avail = 1;
            if (arc_MBOX_EXECUTE_UC_MBOX_IDLE) begin
                mbox_fsm_ns = MBOX_IDLE;
                lock_cr_en = 1;
                lock_cr_nxt = 0; //reset the lock
                user_cr_en = 1;
                user_cr_nxt = '0;
                rst_mbox_ptr = 1;
            end
        end
        MBOX_EXECUTE_SOC: begin
            soc_mbox_data_avail = 1;
            if (arc_MBOX_EXECUTE_SOC_MBOX_IDLE) begin
                mbox_fsm_ns = MBOX_IDLE;
                lock_cr_en = 1;
                lock_cr_nxt = 0; //reset the lock
                user_cr_en = 1;
                user_cr_nxt = '0;
                rst_mbox_ptr = 1;
            end
        end

        default: begin
            mbox_fsm_ns = mbox_fsm_ps;
        end
    endcase
end

//next state -> present state
//reset mbox fsm to idle on rst_b
`CLP_RSTD_FF(mbox_fsm_ps, mbox_fsm_ns, clk, rst_b, MBOX_IDLE)

//LOCK register
//reading this register and observing an unlocked state will lock the mailbox
//the mailbox will stay locked until EXECUTE is reset
`CLP_EN_RST_FF(lock_cr, lock_cr_nxt, clk, lock_cr_en, rst_b)
`CLP_EN_RST_FF(soc_has_lock, soc_has_lock_nxt, clk, lock_cr_en, rst_b)

//USER register
//store the user attribute here when locking the mailbox, only grant requests
//made by the user that has locked the mailbox
`CLP_EN_RST_FF(user_cr, user_cr_nxt, clk, user_cr_en, rst_b)

//CMD register
//the user of the mailbox will write command opcodes here for firmware to consume
`CLP_EN_RST_FF(cmd_cr, cmd_cr_nxt, clk, cmd_cr_en, rst_b)

//DLEN register
//indicates the intended number of bytes to be written into the mailbox
`CLP_EN_RST_FF(dlen_cr, dlen_cr_nxt, clk, dlen_cr_en, rst_b)

//EXECUTE register
//setting this bit indicates that the requester has completed its request and will signal to the receiver
//receiver is responsible for resetting this bit when it has finished reading the mailbox
//execute uc is set by SOC and read by UC
//execute soc is set by UC and read by SOC
`CLP_EN_RST_FF(execute_cr, execute_cr_nxt, clk, execute_cr_en, rst_b)

//SRAM
//Primary storage for the mailbox, can be accessed by reading DATAOUT or writing DATAIN
//only accessed by the device that locked the mailbox
caliptra_sram 
#(
    .DATA_WIDTH(DATA_W),
    .DEPTH(DEPTH)
)
mbox_ram1
(
    .clk_i(clk),
    
    .we_i(sram_we),
    .waddr_i(sram_waddr),
    .wdata_i(sram_wdata),
    
    .rdaddr_i(sram_rdaddr),
    .rdata_o(sram_rdata)
);

//control for sram write and read pointer
//SoC access is controlled by mailbox, each subsequent read or write increments the pointer
//uC accesses can specify the specific read or write address, or rely on mailbox to control
always_comb sram_wdata = req_data.wdata;

//in ready for data state we increment the pointer each time we write
always_comb mbox_wrptr_nxt = rst_mbox_ptr ? '0 :
                             inc_wrptr ? mbox_wrptr + 'd1 : 
                                         mbox_wrptr;
`CLP_EN_RST_FF(mbox_wrptr, mbox_wrptr_nxt, clk, inc_wrptr | rst_mbox_ptr, rst_b)

//in execute state we increment the pointer each time we write
always_comb mbox_rdptr_nxt = rst_mbox_ptr ? '0 :
                             inc_rdptr ? mbox_rdptr + 'd1 : 
                                          mbox_rdptr;
`CLP_EN_RST_FF(mbox_rdptr, mbox_rdptr_nxt, clk, inc_rdptr | rst_mbox_ptr, rst_b)

//determine if this request is a valid read cycle
//first check if it's a read request
//next check that the mailbox is either unlocked OR the user_cr matches the request
//this ensure that we only grant reads to the user that locked the mailbox
always_comb valid_read_cycle = req_dv & ~req_data.write & (~lock_cr | (user_cr == req_data.user));

//final read mux
//if the request is a read, and requester has necessary permissions
//populate the read data onto the output
always_comb begin : mbox_read_mux
    rdata = 'hDEAD_BEEF; //drive dead beef
    sram_rdaddr = '0;
    inc_rdptr = 0;
    read_error = '0;

    if (valid_read_cycle) begin
        unique case (req_data.addr) inside
            [BASE_ADDR : MBOX_CR_BASE - 1]: begin
                //direct read of sram, uc only
                if (~req_data.soc_req) begin
                    sram_rdaddr = req_data.addr[MBOX_ADDR_MSB:MBOX_ADDR_LSB];
                    rdata = sram_rdata;
                end
            end 
            MBOX_LOCK_ADDR: begin
                rdata = { {($bits(rdata) - $bits(lock_cr)){1'b0}}, lock_cr };
            end
            MBOX_CMD_ADDR: begin
                rdata = cmd_cr;
            end
            MBOX_DLEN_ADDR: begin
                rdata = dlen_cr;
            end
            MBOX_DATAIN_ADDR: begin
                //Register is WO
                read_error = 1;
            end
            MBOX_DATAOUT_ADDR: begin
                //drive mailbox output
                if (((mbox_fsm_ps == MBOX_EXECUTE_UC) & ~req_data.soc_req) | ((mbox_fsm_ps == MBOX_EXECUTE_SOC) & req_data.soc_req)) begin
                    inc_rdptr = 1;
                    sram_rdaddr = mbox_rdptr;
                    rdata = sram_rdata;
                end else begin
                    read_error = 1;
                end
            end
            MBOX_EXEC_ADDR: begin
                rdata = { {($bits(rdata) - $bits(execute_cr)){1'b0}}, execute_cr };
            end
            MBOX_STATUS_ADDR: begin
                rdata = status_cr;
            end
            default: begin
                //drive zero if address doesn't match anything
                rdata = 'hDEAD_BEEF;
                //drive read error if address doesn't match anything
                read_error = 1;
            end
        endcase
    end
end

//determine if this request is a valid write cycle
//must have acquired the lock to the mailbox before writing anything
//and the user cr has to match the user sending the write
always_comb valid_write_cycle = req_dv & req_data.write & lock_cr & (user_cr == req_data.user);

always_comb begin : mbox_write_mux
    cmd_cr_en = 0;
    cmd_cr_nxt = '0;
    dlen_cr_en = 0;
    dlen_cr_nxt = '0;
    execute_cr_en = 0;
    execute_cr_nxt = '0;
    inc_wrptr = 0;
    sram_we = 0;
    sram_waddr = '0;
    write_error = '0;

    if (valid_write_cycle) begin
        unique case (req_data.addr) inside
            [MBOX_CR_BASE-1:BASE_ADDR]: begin
                //direct write to sram, uc only
                if (~req_data.soc_req) begin
                    sram_we = 1;
                    sram_waddr = req_data.addr[MBOX_ADDR_MSB:MBOX_ADDR_LSB];
                end
            end 
            MBOX_LOCK_ADDR: begin
                //Register is RO
                write_error = 1;
            end
            MBOX_CMD_ADDR: begin
                cmd_cr_en = 1;
                cmd_cr_nxt = req_data.wdata;
            end
            MBOX_DLEN_ADDR: begin
                dlen_cr_en = 1;
                dlen_cr_nxt = req_data.wdata;
            end
            MBOX_DATAIN_ADDR: begin
                //if FSM is in rdy for data, write to mbox else error
                if (mbox_fsm_ps == MBOX_RDY_FOR_DATA) begin
                    inc_wrptr = 1;
                    sram_we = 1;
                    sram_waddr = mbox_wrptr;
                end else begin
                    write_error = 1;
                end
                
            end
            MBOX_DATAOUT_ADDR: begin
                //Register is RO
                write_error = 1;
            end
            MBOX_EXEC_ADDR: begin
                execute_cr_en = 1;
                execute_cr_nxt = req_data.wdata[$bits(execute_cr_nxt)-1:0];
            end
            MBOX_STATUS_ADDR: begin
                //Register is RO
                write_error = 1;
            end
            default: begin
                //drive read error if address doesn't match anything
                write_error = 1;
            end
        endcase
    end
end

endmodule