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

logic soc_has_lock, soc_has_lock_nxt;

//controls
logic read_error;
logic write_error;

mbox_csr_pkg::mbox_csr__in_t hwif_in;
mbox_csr_pkg::mbox_csr__out_t hwif_out;

assign mbox_error = read_error | write_error;

//move from idle to rdy for command when lock is acquired
//we have a valid read, to the lock register, and it's not currently locked
always_comb arc_MBOX_IDLE_MBOX_RDY_FOR_CMD = ~hwif_out.mbox_lock.lock.value & hwif_out.mbox_lock.lock.swmod;
//move from rdy for cmd to rdy for dlen when cmd is written
always_comb arc_MBOX_RDY_FOR_CMD_MBOX_RDY_FOR_DLEN = hwif_out.mbox_cmd.command.swmod;
//move from rdy for dlen to rdy for data when dlen is written
always_comb arc_MBOX_RDY_FOR_DLEN_MBOX_RDY_FOR_DATA = hwif_out.mbox_dlen.length.swmod;
//move from rdy for data to execute uc when SoC sets execute bit
always_comb arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC = hwif_out.mbox_execute.execute.value & soc_has_lock;
//move from rdy for data to execute soc when uc writes to execute
always_comb arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC = hwif_out.mbox_execute.execute.value & ~soc_has_lock;
//move from rdy to execute to idle when uc resets execute
always_comb arc_MBOX_EXECUTE_UC_MBOX_IDLE = ~hwif_out.mbox_execute.execute.value;
//move from rdy to execute to idle when SoC resets execute
always_comb arc_MBOX_EXECUTE_SOC_MBOX_IDLE = ~hwif_out.mbox_execute.execute.value;

always_comb begin : mbox_fsm_combo
    soc_has_lock_nxt = 0;
    rst_mbox_ptr = 0;
    inc_rdptr = 0; inc_wrptr = 0;
    sram_we = '0;
    uc_mbox_data_avail = 0;
    soc_mbox_data_avail = 0;
    mbox_fsm_ns = mbox_fsm_ps;

    unique casez (mbox_fsm_ps)
        MBOX_IDLE: begin
            if (arc_MBOX_IDLE_MBOX_RDY_FOR_CMD) begin
                mbox_fsm_ns = MBOX_RDY_FOR_CMD;
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
            //update the read/write pointers to sram when accessing datain/dataout registers
            inc_rdptr = hwif_out.mbox_dataout.dataout.swacc;
            inc_wrptr = hwif_out.mbox_datain.datain.swmod;
            sram_we = hwif_out.mbox_datain.datain.swmod;
            if (arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC) begin
                mbox_fsm_ns = MBOX_EXECUTE_UC;
            end
            else if (arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC) begin
                mbox_fsm_ns = MBOX_EXECUTE_SOC;
            end
        end
        MBOX_EXECUTE_UC: begin
            uc_mbox_data_avail = 1;
            inc_rdptr = hwif_out.mbox_dataout.dataout.swacc;
            if (arc_MBOX_EXECUTE_UC_MBOX_IDLE) begin
                mbox_fsm_ns = MBOX_IDLE;
                rst_mbox_ptr = 1;
            end
        end
        MBOX_EXECUTE_SOC: begin
            soc_mbox_data_avail = 1;
            inc_rdptr = hwif_out.mbox_dataout.dataout.swacc;
            if (arc_MBOX_EXECUTE_SOC_MBOX_IDLE) begin
                mbox_fsm_ns = MBOX_IDLE;
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

`CLP_EN_RST_FF(soc_has_lock, soc_has_lock_nxt, clk, arc_MBOX_IDLE_MBOX_RDY_FOR_CMD, rst_b)

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

//add support for direct writes/reads from uc
always_comb sram_rdaddr = mbox_rdptr;
always_comb sram_waddr = mbox_wrptr;

always_comb hwif_in.reset_b = rst_b;
//always_comb hwif_in.soc_req = req_data.soc_req;
always_comb hwif_in.mbox_user.user.next = req_data.user;
//check the requesting user:
//don't update mailbox data if lock hasn't been acquired
//if uc has the lock, check that this request if rom uc
//if soc has the lock, check that this request is from soc and user attribute matters
always_comb hwif_in.valid_user = hwif_out.mbox_lock.lock.value & ((~soc_has_lock & ~req_data.soc_req) |
                                                                  (soc_has_lock & req_data.soc_req & (req_data.user == hwif_out.mbox_user.user.value))) ;
//indicate that requesting user is setting the lock
always_comb hwif_in.lock_set = arc_MBOX_IDLE_MBOX_RDY_FOR_CMD;
always_comb hwif_in.mbox_dataout.dataout.next = sram_rdata;
//clear the lock when moving from execute to idle
always_comb hwif_in.mbox_lock.lock.hwclr = arc_MBOX_EXECUTE_SOC_MBOX_IDLE | arc_MBOX_EXECUTE_UC_MBOX_IDLE;

mbox_csr
mbox_csr1(
    .clk(clk),
    .rst('0),

    .s_cpuif_req(req_dv),
    .s_cpuif_req_is_wr(req_data.write),
    .s_cpuif_addr(req_data.addr),
    .s_cpuif_wr_data(req_data.wdata),
    .s_cpuif_req_stall_wr(),
    .s_cpuif_req_stall_rd(),
    .s_cpuif_rd_ack(),
    .s_cpuif_rd_err(read_error),
    .s_cpuif_rd_data(rdata),
    .s_cpuif_wr_ack(),
    .s_cpuif_wr_err(write_error),

    .hwif_in(hwif_in),
    .hwif_out(hwif_out)
);

endmodule