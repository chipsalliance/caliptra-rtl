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

module mbox 
    import soc_ifc_pkg::*;
    import mbox_csr_pkg::*;
    #(
     parameter DATA_W = 32
    ,parameter SIZE_KB = 128
    )
    (
    input logic         clk,
    input logic         rst_b,

    //mailbox request
    input logic         req_dv,
    output logic        req_hold,
    input logic         dir_req_dv,
    input soc_ifc_req_t req_data,
    output logic        mbox_error,

    output logic [DATA_W-1:0] rdata,

    input logic sha_sram_req_dv,
    input logic [MBOX_ADDR_W-1:0] sha_sram_req_addr,
    output mbox_sram_resp_t sha_sram_resp,
    output logic sha_sram_hold, // Throttle the SRAM requests when writing corrected ECC

    //SRAM interface
    output mbox_sram_req_t  mbox_sram_req,
    input  mbox_sram_resp_t mbox_sram_resp,

    // ECC Status
    output logic sram_single_ecc_error,
    output logic sram_double_ecc_error,

    //interrupts
    output logic uc_mbox_data_avail,
    output logic soc_mbox_data_avail

);

localparam DEPTH = (SIZE_KB * 1024 * 8) / DATA_W;

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
logic [MBOX_ECC_DATA_W-1:0] sram_wdata_ecc;
logic [$clog2(DEPTH)-1:0] sram_waddr;
logic [$clog2(DEPTH)-1:0] mbox_wrptr, mbox_wrptr_nxt;
logic inc_wrptr;
logic [$clog2(DEPTH)-1:0] sram_rdaddr;
logic [$clog2(DEPTH)-1:0] mbox_rdptr, mbox_rdptr_nxt;
logic inc_rdptr,inc_rdptr_f;
logic rst_mbox_ptr;
logic [DATA_W-1:0] sram_rdata;
logic [MBOX_ECC_DATA_W-1:0] sram_rdata_ecc;
logic [DATA_W-1:0] sram_rdata_cor;
logic [MBOX_ECC_DATA_W-1:0] sram_rdata_cor_ecc;
logic sram_we;
logic mbox_protocol_sram_we;
logic sram_ecc_cor_we;
logic [$clog2(DEPTH)-1:0] sram_ecc_cor_waddr;
logic dir_req_dv_q, dir_req_rd_phase;

logic soc_has_lock, soc_has_lock_nxt;

//csr
logic [DATA_W-1:0] csr_rdata;
logic read_error;
logic write_error;

mbox_csr__in_t hwif_in;
mbox_csr__out_t hwif_out;

assign mbox_error = read_error | write_error;

//move from idle to rdy for command when lock is acquired
//we have a valid read, to the lock register, and it's not currently locked
always_comb arc_MBOX_IDLE_MBOX_RDY_FOR_CMD = ~hwif_out.mbox_lock.lock.value & hwif_out.mbox_lock.lock.swmod;
//move from rdy for cmd to rdy for dlen when cmd is written
always_comb arc_MBOX_RDY_FOR_CMD_MBOX_RDY_FOR_DLEN = hwif_out.mbox_cmd.command.swmod & hwif_in.valid_user;
//move from rdy for dlen to rdy for data when dlen is written
always_comb arc_MBOX_RDY_FOR_DLEN_MBOX_RDY_FOR_DATA = hwif_out.mbox_dlen.length.swmod & hwif_in.valid_user;
//move from rdy for data to execute uc when SoC sets execute bit
always_comb arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC = hwif_out.mbox_execute.execute.value & soc_has_lock;
//move from rdy for data to execute soc when uc writes to execute
always_comb arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC = hwif_out.mbox_execute.execute.value & ~soc_has_lock;
//move from rdy to execute to idle when uc resets execute
always_comb arc_MBOX_EXECUTE_UC_MBOX_IDLE = (mbox_fsm_ps == MBOX_EXECUTE_UC) & ~hwif_out.mbox_execute.execute.value;
//move from rdy to execute to idle when SoC resets execute
always_comb arc_MBOX_EXECUTE_SOC_MBOX_IDLE = (mbox_fsm_ps == MBOX_EXECUTE_SOC) & ~hwif_out.mbox_execute.execute.value;

always_comb begin : mbox_fsm_combo
    soc_has_lock_nxt = 0;
    rst_mbox_ptr = 0;
    inc_rdptr = 0; inc_wrptr = 0;
    mbox_protocol_sram_we = '0;
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
            //update the write pointers to sram when accessing datain register
            inc_wrptr = hwif_out.mbox_datain.datain.swmod & hwif_in.valid_user;
            mbox_protocol_sram_we = hwif_out.mbox_datain.datain.swmod & hwif_in.valid_user;
            if (arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC) begin
                mbox_fsm_ns = MBOX_EXECUTE_UC;
                //load the first dword when we move to execute
                inc_rdptr = 1'b1;
            end
            else if (arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC) begin
                mbox_fsm_ns = MBOX_EXECUTE_SOC;
                //load the first dword when we move to execute
                inc_rdptr = 1'b1;
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

//flops
always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b)begin
        mbox_fsm_ps <= MBOX_IDLE;
        soc_has_lock <= '0;
        dir_req_rd_phase <= '0;
        mbox_wrptr <= '0;
        mbox_rdptr <= '0;
        inc_rdptr_f <= '0;
        sram_ecc_cor_waddr <= '0;
    end
    else begin
        mbox_fsm_ps <= mbox_fsm_ns;
        soc_has_lock <= arc_MBOX_IDLE_MBOX_RDY_FOR_CMD ? soc_has_lock_nxt : soc_has_lock;
        dir_req_rd_phase <= dir_req_dv_q & ~req_data.write;
        mbox_wrptr <= (inc_wrptr | rst_mbox_ptr) ? mbox_wrptr_nxt : mbox_wrptr;
        mbox_rdptr <= (inc_rdptr | rst_mbox_ptr) ? mbox_rdptr_nxt : mbox_rdptr;
        inc_rdptr_f <= (inc_rdptr | inc_rdptr_f) ? inc_rdptr : inc_rdptr_f;
        sram_ecc_cor_waddr <= /*dir_req_rd_phase ? sram_ecc_cor_waddr :*/
                                                 sram_rdaddr;
    end
end

//need to hold direct read accesses for 1 clock to get response
//create a qualified direct request signal that is masked during the data phase
//hold the interface to insert wait state when direct request comes
//mask the request and hold the interface if SHA is using the mailbox
//hold when a read to dataout is coming and we haven't updated the data yet
//FIXME: it's possible we could deliver the read data directly from the sram, or we could have two flop stages and speculatively read ahead to stream
always_comb dir_req_dv_q = dir_req_dv & ~dir_req_rd_phase & ~sha_sram_req_dv;
always_comb req_hold = (dir_req_dv_q & ~req_data.write) | 
                       (dir_req_dv & sha_sram_req_dv) |
                       (hwif_out.mbox_dataout.dataout.swacc & inc_rdptr_f);
always_comb sha_sram_hold = sram_single_ecc_error/* || sram_ecc_cor_we*/;

//SRAM interface
always_comb sram_ecc_cor_we = sram_single_ecc_error; // TODO we probably want this to be a reg-stage to reduce combo logic SRAM -> rdata -> wdata -> SRAM
always_comb sram_we = (dir_req_dv_q & req_data.write) | mbox_protocol_sram_we | sram_ecc_cor_we;
//align the direct address to a word
always_comb sram_rdaddr = dir_req_dv_q ? req_data.addr[$clog2(DEPTH)+1:2] : mbox_rdptr;
always_comb sram_waddr = sram_ecc_cor_we ? sram_ecc_cor_waddr :
                         dir_req_dv_q    ? req_data.addr[$clog2(DEPTH)+1:2] : mbox_wrptr;
//data phase after request for direct access
always_comb rdata = dir_req_rd_phase ? sram_rdata_cor : csr_rdata;

always_comb begin: mbox_sram_inf
    //read live on direct access, or when pointer has been incremented, or if write was made to same address as rdptr
    mbox_sram_req.cs = sha_sram_req_dv | dir_req_dv_q | mbox_protocol_sram_we | inc_rdptr | sram_ecc_cor_we;
    mbox_sram_req.we = sram_we & ~sha_sram_req_dv;
    mbox_sram_req.addr = sha_sram_req_dv ? sha_sram_req_addr :
                                 sram_we ? sram_waddr : sram_rdaddr;
    mbox_sram_req.wdata.data = sram_ecc_cor_we ? sram_rdata_cor     : sram_wdata;
    mbox_sram_req.wdata.ecc  = sram_ecc_cor_we ? sram_rdata_cor_ecc : sram_wdata_ecc;

    sram_rdata     = mbox_sram_resp.rdata.data;
    sram_rdata_ecc = mbox_sram_resp.rdata.ecc;
    sha_sram_resp  = '{rdata: '{ecc:sram_rdata_cor_ecc , data:sram_rdata_cor}};
end

// From RISC-V core beh_lib.sv
// 32-bit data width hardcoded
// 7-bit ECC width hardcoded
rvecc_encode mbox_ecc_encode (
    .din    (sram_wdata    ),
    .ecc_out(sram_wdata_ecc)
);
// synthesis translate_off
initial assert(DATA_W == 32) else
    $error("%m::rvecc_encode supports 32-bit data width; must change SRAM ECC implementation to support DATA_W = %d", DATA_W);
// synthesis translate_on
rvecc_decode ecc_decode (
    .en              (dir_req_rd_phase     ),
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
always_comb sram_wdata = req_data.wdata;

//in ready for data state we increment the pointer each time we write
always_comb mbox_wrptr_nxt = rst_mbox_ptr ? '0 :
                             inc_wrptr ? mbox_wrptr + 'd1 : 
                                         mbox_wrptr;


//in execute state we increment the pointer each time we write
always_comb mbox_rdptr_nxt = rst_mbox_ptr ? '0 :
                             inc_rdptr ? mbox_rdptr + 'd1 : 
                                         mbox_rdptr;

always_comb hwif_in.reset_b = rst_b;
always_comb hwif_in.mbox_user.user.next = req_data.user;

//check the requesting user:
//don't update mailbox data if lock hasn't been acquired
//if uc has the lock, check that this request is from uc
//if soc has the lock, check that this request is from soc and user attributes match
always_comb hwif_in.valid_user = hwif_out.mbox_lock.lock.value & ((~soc_has_lock & ~req_data.soc_req) |
                                                                  (soc_has_lock & req_data.soc_req & (req_data.user == hwif_out.mbox_user.user.value)));
//indicate that requesting user is setting the lock
always_comb hwif_in.lock_set = arc_MBOX_IDLE_MBOX_RDY_FOR_CMD;

//update dataout
always_comb hwif_in.mbox_dataout.dataout.swwe = '0; //no sw write enable, but need the storage element
//update dataout whenever we read from the sram for a dataout access
//we load the first entry on the arc to execute
always_comb hwif_in.mbox_dataout.dataout.we = inc_rdptr_f;
always_comb hwif_in.mbox_dataout.dataout.next = sram_rdata_cor;
//clear the lock when moving from execute to idle
always_comb hwif_in.mbox_lock.lock.hwclr = arc_MBOX_EXECUTE_SOC_MBOX_IDLE | arc_MBOX_EXECUTE_UC_MBOX_IDLE;
// Set mbox_csr status fields in response to ECC errors
always_comb hwif_in.mbox_status.ecc_single_error.hwset = sram_single_ecc_error;
always_comb hwif_in.mbox_status.ecc_double_error.hwset = sram_double_ecc_error;


logic s_cpuif_req_stall_wr_nc;
logic s_cpuif_req_stall_rd_nc;
logic s_cpuif_rd_ack_nc;
logic s_cpuif_wr_ack_nc;

mbox_csr
mbox_csr1(
    .clk(clk),
    .rst('0),

    .s_cpuif_req(req_dv & (req_data.addr[SOC_IFC_ADDR_W-1:MBOX_CSR_ADDR_WIDTH] == MBOX_REG_START_ADDR[SOC_IFC_ADDR_W-1:MBOX_CSR_ADDR_WIDTH])),
    .s_cpuif_req_is_wr(req_data.write),
    .s_cpuif_addr(req_data.addr[MBOX_CSR_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data(req_data.wdata),
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

`ASSERT_MUTEX(ERR_MBOX_ACCESS_MUTEX, {sha_sram_req_dv, dir_req_dv_q, mbox_protocol_sram_we, inc_rdptr}, clk, rst_b)

endmodule
