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
    output logic soc_mbox_data_avail,

    //DMI reg access
    input logic dmi_inc_rdptr,
    output mbox_dmi_reg_t dmi_reg

);

localparam DEPTH = (SIZE_KB * 1024 * 8) / DATA_W;
localparam MBOX_SIZE_IN_DW = (SIZE_KB*1024)/4;

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
logic arc_MBOX_EXECUTE_UC_MBOX_IDLE;
logic arc_MBOX_EXECUTE_SOC_MBOX_IDLE;
logic arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_SOC;
logic arc_MBOX_EXECUTE_SOC_MBOX_EXECUTE_UC;

//sram
logic [DATA_W-1:0] sram_wdata;
logic [MBOX_ECC_DATA_W-1:0] sram_wdata_ecc;
logic [$clog2(DEPTH)-1:0] sram_waddr;
logic [$clog2(DEPTH)-1:0] mbox_wrptr, mbox_wrptr_nxt;
logic inc_wrptr;
logic [$clog2(DEPTH)-1:0] sram_rdaddr;
logic [$clog2(DEPTH)-1:0] mbox_rdptr, mbox_rdptr_nxt;
logic inc_rdptr,inc_rdptr_f;
logic rst_mbox_rdptr;
logic rst_mbox_wrptr;
logic [DATA_W-1:0] sram_rdata;
logic [MBOX_ECC_DATA_W-1:0] sram_rdata_ecc;
logic [DATA_W-1:0] sram_rdata_cor;
logic [MBOX_ECC_DATA_W-1:0] sram_rdata_cor_ecc;
logic sram_we;
logic mbox_protocol_sram_we;
logic sram_ecc_cor_we;
logic [$clog2(DEPTH)-1:0] sram_ecc_cor_waddr;
logic dir_req_dv_q, dir_req_rd_phase;
logic dir_req_wr_ph;
logic mask_rdata;
logic [$clog2(DEPTH)-1:0] dir_req_addr;

logic soc_has_lock, soc_has_lock_nxt;
logic valid_requester;
logic valid_receiver;

//csr
logic [DATA_W-1:0] csr_rdata;
logic read_error;
logic write_error;

mbox_csr__in_t hwif_in;
mbox_csr__out_t hwif_out;

assign mbox_error = read_error | write_error;

//Determine if this is a valid request from the requester side
//1) uC requests are valid if uc has lock
//2) SoC requests are valid if soc has lock and it's the user that locked it 
always_comb valid_requester = hwif_out.mbox_lock.lock.value & 
                              ((~req_data.soc_req & (~soc_has_lock || (mbox_fsm_ps == MBOX_EXECUTE_UC))) |
                               ( req_data.soc_req & soc_has_lock & (req_data.user == hwif_out.mbox_user.user.value)));

//Determine if this is a valid request from the receiver side
always_comb valid_receiver = hwif_out.mbox_lock.lock.value &
                             //Receiver is valid when they don't have the lock
                             ((~req_data.soc_req & soc_has_lock) | (req_data.soc_req & ~soc_has_lock) |
                             //Receiver is valid when they are reading a response to their request
                             (valid_requester & ((soc_has_lock & (mbox_fsm_ps == MBOX_EXECUTE_SOC)) |
                                                 (~soc_has_lock & (mbox_fsm_ps == MBOX_EXECUTE_UC)))));

//We want to mask read data when
//Invalid user is trying to access the mailbox data, or we're not in execute state
always_comb mask_rdata = hwif_out.mbox_dataout.dataout.swacc & ~valid_receiver;

//move from idle to rdy for command when lock is acquired
//we have a valid read, to the lock register, and it's not currently locked
always_comb arc_MBOX_IDLE_MBOX_RDY_FOR_CMD = ~hwif_out.mbox_lock.lock.value & hwif_out.mbox_lock.lock.swmod;
//move from rdy for cmd to rdy for dlen when cmd is written
always_comb arc_MBOX_RDY_FOR_CMD_MBOX_RDY_FOR_DLEN = hwif_out.mbox_cmd.command.swmod & valid_requester;
//move from rdy for dlen to rdy for data when dlen is written
always_comb arc_MBOX_RDY_FOR_DLEN_MBOX_RDY_FOR_DATA = hwif_out.mbox_dlen.length.swmod & valid_requester;
//move from rdy for data to execute uc when SoC sets execute bit
always_comb arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC = hwif_out.mbox_execute.execute.value & soc_has_lock;
//move from rdy for data to execute soc when uc writes to execute
always_comb arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC = hwif_out.mbox_execute.execute.value & ~soc_has_lock;
//move from rdy to execute to idle when uc resets execute
always_comb arc_MBOX_EXECUTE_UC_MBOX_IDLE = (mbox_fsm_ps == MBOX_EXECUTE_UC) & ~hwif_out.mbox_execute.execute.value;
always_comb arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_SOC = (mbox_fsm_ps == MBOX_EXECUTE_UC) & soc_has_lock & (hwif_out.mbox_status.status.value != CMD_BUSY);
//move from rdy to execute to idle when SoC resets execute
always_comb arc_MBOX_EXECUTE_SOC_MBOX_IDLE = (mbox_fsm_ps == MBOX_EXECUTE_SOC) & ~hwif_out.mbox_execute.execute.value;
always_comb arc_MBOX_EXECUTE_SOC_MBOX_EXECUTE_UC = (mbox_fsm_ps == MBOX_EXECUTE_SOC) & ~soc_has_lock & (hwif_out.mbox_status.status.value != CMD_BUSY);
//move back to IDLE and unlock when force unlock is set
always_comb arc_FORCE_MBOX_UNLOCK = hwif_out.mbox_unlock.unlock.value;

logic [31:0] mbox_dlen_in_dws, mbox_dlen_in_dwsQ;
logic        rdptr_inc_valid;

always_comb begin
     mbox_dlen_in_dws = ((hwif_out.mbox_dlen.length.value >> 2) + (hwif_out.mbox_dlen.length.value[0] | hwif_out.mbox_dlen.length.value[1]));
     mbox_dlen_in_dwsQ = (mbox_dlen_in_dws > MBOX_SIZE_IN_DW) ? MBOX_SIZE_IN_DW : mbox_dlen_in_dws;

     // Restrict mailbox dataout read once the DLEN in "DWORDS" is reached
     // Increment read pointer only if the mailbox data length in DWORDS is non-zero and the rdptr didnt pass
     rdptr_inc_valid  =  (|mbox_dlen_in_dwsQ) & ((mbox_rdptr + 'd1) <= mbox_dlen_in_dwsQ);

end

always_comb begin : mbox_fsm_combo
    soc_has_lock_nxt = 0;
    rst_mbox_rdptr = 0;
    rst_mbox_wrptr = 0;
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
            if (arc_FORCE_MBOX_UNLOCK) begin
                mbox_fsm_ns = MBOX_IDLE;
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
        end
        MBOX_RDY_FOR_DLEN: begin
            if (arc_MBOX_RDY_FOR_DLEN_MBOX_RDY_FOR_DATA) begin
                mbox_fsm_ns = MBOX_RDY_FOR_DATA;
            end
            if (arc_FORCE_MBOX_UNLOCK) begin
                mbox_fsm_ns = MBOX_IDLE;
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
        end
        MBOX_RDY_FOR_DATA: begin
            //update the write pointers to sram when accessing datain register
            inc_wrptr = hwif_out.mbox_datain.datain.swmod & valid_requester;
            mbox_protocol_sram_we = hwif_out.mbox_datain.datain.swmod & valid_requester;
            if (arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC) begin
                mbox_fsm_ns = MBOX_EXECUTE_UC;
                //reset wrptr so receiver can write response
                rst_mbox_wrptr = 1'b1;
                //load the first dword when we move to execute
                inc_rdptr = 1'b1;
            end
            else if (arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC) begin
                mbox_fsm_ns = MBOX_EXECUTE_SOC;
                //reset wrptr so receiver can write response
                rst_mbox_wrptr = 1'b1;
                //load the first dword when we move to execute
                inc_rdptr = 1'b1;
            end
            if (arc_FORCE_MBOX_UNLOCK) begin
                mbox_fsm_ns = MBOX_IDLE;
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
        end
        //SoC set execute, data is for the uC
        //only uC can read from mbox
        //only uC can write to datain here to respond to SoC
        MBOX_EXECUTE_UC: begin
            uc_mbox_data_avail = 1;
            inc_rdptr = dmi_inc_rdptr | (hwif_out.mbox_dataout.dataout.swacc & ~req_data.soc_req);
            inc_wrptr = hwif_out.mbox_datain.datain.swmod & ~req_data.soc_req;
            mbox_protocol_sram_we = hwif_out.mbox_datain.datain.swmod & ~req_data.soc_req;
            if (arc_MBOX_EXECUTE_UC_MBOX_IDLE) begin
                mbox_fsm_ns = MBOX_IDLE;
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
            else if (arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_SOC) begin
                mbox_fsm_ns = MBOX_EXECUTE_SOC;
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
            if (arc_FORCE_MBOX_UNLOCK) begin
                mbox_fsm_ns = MBOX_IDLE;
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
        end
        //uC set execute, data is for the SoC
        //If we're here, restrict reading to the user that requested the data
        //Only SoC can read from mbox
        //Only SoC can write to datain here to respond to uC
        MBOX_EXECUTE_SOC: begin
            soc_mbox_data_avail = 1;
            inc_rdptr = (dmi_inc_rdptr | (hwif_out.mbox_dataout.dataout.swacc & req_data.soc_req & valid_receiver));
            if (arc_MBOX_EXECUTE_SOC_MBOX_IDLE) begin
                mbox_fsm_ns = MBOX_IDLE;
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
            else if (arc_MBOX_EXECUTE_SOC_MBOX_EXECUTE_UC) begin
                mbox_fsm_ns = MBOX_EXECUTE_UC;
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
            if (arc_FORCE_MBOX_UNLOCK) begin
                mbox_fsm_ns = MBOX_IDLE;
                rst_mbox_wrptr = 1;
                rst_mbox_rdptr = 1;
            end
        end

        default: begin
            mbox_fsm_ns = mbox_fsm_ps;
        end
    endcase
end


//increment read ptr only if its allowed
logic inc_rdptrQ;
assign inc_rdptrQ = inc_rdptr & rdptr_inc_valid;

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
        dir_req_rd_phase <= dir_req_dv_q & ~sha_sram_req_dv & ~req_data.write;
        mbox_wrptr <= (inc_wrptr | rst_mbox_wrptr) ? mbox_wrptr_nxt : mbox_wrptr;
        mbox_rdptr <= (inc_rdptrQ | rst_mbox_rdptr) ? mbox_rdptr_nxt : mbox_rdptr;
        inc_rdptr_f <= (inc_rdptrQ | inc_rdptr_f) ? inc_rdptrQ : inc_rdptr_f;
        sram_ecc_cor_waddr <= /*dir_req_rd_phase ? sram_ecc_cor_waddr :*/
                                                 sram_rdaddr;
    end
end



//need to hold direct read accesses for 1 clock to get response
//create a qualified direct request signal that is masked during the data phase
//hold the interface to insert wait state when direct request comes
//mask the request and hold the interface if SHA is using the mailbox
//hold when a read to dataout is coming and we haven't updated the data yet
always_comb dir_req_dv_q = (dir_req_dv & ~dir_req_rd_phase & hwif_out.mbox_lock.lock.value & (~soc_has_lock | (mbox_fsm_ps == MBOX_EXECUTE_UC))) | 
                            sha_sram_req_dv;
always_comb dir_req_wr_ph = dir_req_dv_q & ~sha_sram_req_dv & req_data.write;
always_comb dir_req_addr = sha_sram_req_dv ? sha_sram_req_addr : req_data.addr[$clog2(DEPTH)+1:2];

always_comb req_hold = (dir_req_dv_q & ~req_data.write) | 
                       (dir_req_dv & sha_sram_req_dv) |
                       (hwif_out.mbox_dataout.dataout.swacc & inc_rdptr_f);

always_comb sha_sram_hold = sram_single_ecc_error/* || sram_ecc_cor_we*/;

//SRAM interface
always_comb sram_ecc_cor_we = sram_single_ecc_error; // TODO we probably want this to be a reg-stage to reduce combo logic SRAM -> rdata -> wdata -> SRAM
always_comb sram_we = dir_req_wr_ph | mbox_protocol_sram_we | sram_ecc_cor_we;
//align the direct address to a word
always_comb sram_rdaddr = dir_req_dv_q ? dir_req_addr : mbox_rdptr;
always_comb sram_waddr = sram_ecc_cor_we ? sram_ecc_cor_waddr :
                         dir_req_dv_q    ? dir_req_addr : mbox_wrptr;
//data phase after request for direct access
//We want to mask the read data for certain accesses
always_comb rdata = dir_req_rd_phase ? sram_rdata_cor : ({DATA_W{~mask_rdata}} & csr_rdata);

always_comb begin: mbox_sram_inf
    //read live on direct access, or when pointer has been incremented, or if write was made to same address as rdptr
    mbox_sram_req.cs = dir_req_dv_q | mbox_protocol_sram_we | inc_rdptr | sram_ecc_cor_we;
    mbox_sram_req.we = sram_we;
    mbox_sram_req.addr = sram_we ? sram_waddr : sram_rdaddr;
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
    .en              (dir_req_rd_phase | inc_rdptr_f),
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
always_comb mbox_wrptr_nxt = rst_mbox_wrptr ? '0 :
                             inc_wrptr ? mbox_wrptr + 'd1 : 
                                         mbox_wrptr;


//in execute state we increment the pointer each time we write
always_comb mbox_rdptr_nxt = rst_mbox_rdptr ? '0 :
                             inc_rdptrQ ? mbox_rdptr + 'd1 : 
                                         mbox_rdptr;

always_comb hwif_in.cptra_rst_b = rst_b;
always_comb hwif_in.mbox_user.user.next = req_data.user;
always_comb hwif_in.mbox_status.mbox_fsm_ps.next = mbox_fsm_ps;

always_comb hwif_in.soc_req = req_data.soc_req;
//check the requesting user:
//don't update mailbox data if lock hasn't been acquired
//if uc has the lock, check that this request is from uc
//if soc has the lock, check that this request is from soc and user attributes match
always_comb hwif_in.valid_requester = valid_requester;
always_comb hwif_in.valid_receiver = valid_receiver;

//indicate that requesting user is setting the lock
always_comb hwif_in.lock_set = arc_MBOX_IDLE_MBOX_RDY_FOR_CMD;

//update dataout
always_comb hwif_in.mbox_dataout.dataout.swwe = '0; //no sw write enable, but need the storage element
//update dataout whenever we read from the sram for a dataout access
//we load the first entry on the arc to execute
always_comb hwif_in.mbox_dataout.dataout.we = inc_rdptr_f;
always_comb hwif_in.mbox_dataout.dataout.next = sram_rdata_cor;
//clear the lock when moving from execute to idle
always_comb hwif_in.mbox_lock.lock.hwclr = arc_MBOX_EXECUTE_SOC_MBOX_IDLE | arc_MBOX_EXECUTE_UC_MBOX_IDLE | arc_FORCE_MBOX_UNLOCK;
//clear the mailbox status when we go back to IDLE
always_comb hwif_in.mbox_status.status.hwclr = arc_MBOX_EXECUTE_SOC_MBOX_IDLE | arc_MBOX_EXECUTE_UC_MBOX_IDLE | arc_FORCE_MBOX_UNLOCK;
// Set mbox_csr status fields in response to ECC errors
always_comb hwif_in.mbox_status.ecc_single_error.hwset = sram_single_ecc_error;
always_comb hwif_in.mbox_status.ecc_double_error.hwset = sram_double_ecc_error;
always_comb hwif_in.mbox_status.soc_has_lock.next = soc_has_lock;

always_comb dmi_reg.MBOX_DLEN = hwif_out.mbox_dlen.length.value;
always_comb dmi_reg.MBOX_DOUT = hwif_out.mbox_dataout.dataout.value;
always_comb dmi_reg.MBOX_STATUS = {22'd0,                                       /* [31:10] */
                                   hwif_out.mbox_status.soc_has_lock.value,     /* [9] */
                                   hwif_out.mbox_status.mbox_fsm_ps.value,      /* [8:6] */
                                   hwif_out.mbox_status.ecc_double_error.value, /* [5] */
                                   hwif_out.mbox_status.ecc_single_error.value, /* [4] */
                                   hwif_out.mbox_status.status.value            /* [3:0] */
                                   };

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

`CALIPTRA_ASSERT_MUTEX(ERR_MBOX_ACCESS_MUTEX, {dir_req_dv_q, mbox_protocol_sram_we, inc_rdptr}, clk, rst_b)
`CALIPTRA_ASSERT_MUTEX(ERR_MBOX_DIR_SHA_COLLISION, {dir_req_dv, sha_sram_req_dv}, clk, rst_b)

endmodule
