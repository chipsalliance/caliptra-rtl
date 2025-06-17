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

module sha512_acc_top
    import soc_ifc_pkg::*;
    import mbox_pkg::*;
    import sha512_acc_csr_pkg::*;
    import sha512_params_pkg::*; 
  #(
    parameter DATA_WIDTH = 32
    )(
      // Clock and reset.
      input logic         clk,
      input logic         rst_b,
      input logic         cptra_pwrgood,
  
      // Incoming request from ahb or axi
      input logic         req_dv,
      output logic        req_hold,
      input soc_ifc_req_t req_data,
      output logic [DATA_WIDTH-1:0] rdata,
      output logic        err,

      // Direct access to mailbox
      output logic sha_sram_req_dv,
      output logic [CPTRA_MBOX_ADDR_W-1:0] sha_sram_req_addr,
      input cptra_mbox_sram_resp_t sha_sram_resp,
      input logic sha_sram_hold,

      // Interrupts
      output logic error_intr,
      output logic notif_intr
    );

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam DATA_NUM_BYTES = DATA_WIDTH / 8;
  localparam BLOCK_NO = 1024 / DATA_WIDTH;
  localparam BYTE_NO = 1024 / 8;
  localparam BLOCK_OFFSET_W = $clog2(BLOCK_NO);
  localparam BYTE_OFFSET_W = $clog2(1024/8);

  logic lock_set;
  logic datain_write;
  logic stall_write;
  logic execute_set;

  logic init_reg;
  logic next_reg;
  logic soc_has_lock;
  logic [1:0] mode;
  logic [1:0] sha_mode;
  logic streaming_mode;
  logic mailbox_mode;

  logic [BYTE_OFFSET_W-1:0] num_bytes_data;
  logic extra_pad_block_required;

  //extra bit for roll over on full read
  logic [CPTRA_MBOX_ADDR_W:0] mbox_rdptr;
  logic [CPTRA_MBOX_ADDR_W-1:0] mbox_start_addr, mbox_end_addr;
  logic mbox_read_to_end;
  logic mbox_read_en;
  logic mbox_read_done;
  logic mbox_block_we;

  sha_fsm_state_e sha_fsm_ps, sha_fsm_ns;

  logic arc_SHA_IDLE_SHA_BLOCK_0;
  logic arc_SHA_BLOCK_0_SHA_BLOCK_N;
  logic arc_SHA_BLOCK_0_SHA_PAD0;
  logic arc_SHA_BLOCK_N_SHA_BLOCK_N;
  logic arc_SHA_BLOCK_N_SHA_PAD0;
  logic arc_SHA_PAD0_SHA_PAD1;
  logic arc_SHA_PAD0_SHA_DONE;
  logic arc_SHA_PAD1_SHA_DONE;
  logic arc_IDLE;

  logic mbox_mode_block_we;
  logic stream_mode_block_we;
  logic block_we;
  logic mbox_mode_last_dword_wr;
  logic block_full;
  logic [31:0] num_bytes_wr;
  logic [BLOCK_OFFSET_W:0] block_wptr;
  logic [DATA_NUM_BYTES-1:0][7:0] mbox_rdata;
  logic [DATA_NUM_BYTES-1:0][7:0] streaming_wdata;
  logic [DATA_NUM_BYTES-1:0][7:0] input_data;
  logic [DATA_NUM_BYTES-1:0][7:0] swizzled_data;
  logic [DATA_WIDTH-1:0] block_wdata;
  logic [0:BLOCK_NO-1][DATA_WIDTH-1:0] block_reg,block_reg_nxt;
  logic [0:BYTE_NO-1][7:0] block_reg_nxt_pad;
  logic [1023:0] pad_mask;
  logic [127:0] pad_length;

  //output comes in big endian
  logic [0:15][31:0] digest_reg;
  logic              digest_valid_reg;

  sha512_acc_csr__in_t hwif_in;
  sha512_acc_csr__out_t hwif_out;

  logic read_error, write_error;
  logic [DATA_WIDTH-1:0] reg_biten;

  logic              core_ready;
  logic              core_ready_q;
  logic [15:0][31:0] core_digest;
  logic              core_digest_valid;
  logic              core_digest_valid_q;

  logic zeroize_pulse;

  assign req_hold = stall_write;
  
  assign err = read_error | write_error;

  assign zeroize_pulse = hwif_out.CONTROL.ZEROIZE.value;

  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  sha512_core core(
                   .clk(clk),
                   .reset_n(rst_b),
                   .zeroize(zeroize_pulse),

                   .init_cmd(init_reg),
                   .next_cmd(next_reg),
                   .restore_cmd(1'b0),
                   .mode(sha_mode),

                   .block_msg(block_reg),
                   .restore_digest('0),

                   .ready(core_ready),

                   .digest(core_digest),
                   .digest_valid(core_digest_valid)
                  );

always_comb core_ready_q = core_ready & ~(init_reg | next_reg);
always_comb core_digest_valid_q = core_digest_valid & ~(init_reg | next_reg);
//registers for sha core controls
  always_ff @(posedge clk or negedge rst_b) begin : sha_regs
    if (!rst_b) begin
      digest_reg <= '0;
      digest_valid_reg <= '0;
      init_reg <= '0;
      next_reg <= '0;
    end
    else begin
      init_reg <= arc_SHA_BLOCK_0_SHA_BLOCK_N | arc_SHA_BLOCK_0_SHA_PAD0; 
      next_reg <= arc_SHA_BLOCK_N_SHA_BLOCK_N | arc_SHA_BLOCK_N_SHA_PAD0 | arc_SHA_PAD0_SHA_PAD1;
      digest_valid_reg <= core_digest_valid;
      if (core_digest_valid & ~digest_valid_reg)
        digest_reg <= core_digest;
    end
  end // reg_update

  //SHA API
  //Acquire the lock and store the user
  always_comb hwif_in.USER.USER.next = 32'(req_data.user);
  //Detect the lock getting set when swmod is asserted and lock is 0 and it's not a write
  //Since this lock is cleared by writing, the swmod asserts on write attempts too, but we only want to set lock on read when value is 0
  always_comb lock_set = ~hwif_out.LOCK.LOCK.value & hwif_out.LOCK.LOCK.swmod & ~req_data.write;
  always_comb hwif_in.lock_set = lock_set;

  //check the requesting user:
  //don't update SHA registers if lock hasn't been acquired
  //if uc has the lock, check that this request is from uc
  //if soc has the lock, check that this request is from soc and user attributes match
  always_comb hwif_in.valid_user = hwif_out.LOCK.LOCK.value & ((~soc_has_lock & ~req_data.soc_req) |
                                                                (soc_has_lock & req_data.soc_req & (req_data.user == hwif_out.USER.USER.value[SOC_IFC_USER_W-1:0])));
  always_comb hwif_in.soc_req = req_data.soc_req;
  always_comb hwif_in.STATUS.SOC_HAS_LOCK.next = soc_has_lock;
  
  always_comb mode = hwif_out.MODE.MODE.value;
  //mode encoding bit 0 determines 512 or 384.
  always_comb sha_mode = mode[0] ? MODE_SHA_512 : MODE_SHA_384;
  //determine streaming or mailbox mode - SoC is limited to streaming mode only
  always_comb streaming_mode = ~mode[1] | soc_has_lock;
  always_comb mailbox_mode = mode[1] & ~soc_has_lock;
  //Detect writes to datain register
  always_comb datain_write = hwif_in.valid_user & hwif_out.DATAIN.DATAIN.swmod;
  always_comb execute_set = hwif_out.EXECUTE.EXECUTE.value;

  //When we reach the end of a block we indicate block full
  //If this is also the end of the entire DLEN, mask block full so that we properly pad the last dword
  //We don't want to mask this if num bytes wr is == dlen. This means we wrote a full dword and no padding goes here
  always_comb block_full = block_wptr[BLOCK_OFFSET_W] & ~(num_bytes_wr > hwif_out.DLEN.LENGTH.value);
  always_comb mbox_mode_last_dword_wr = mbox_mode_block_we & (block_wptr == (BLOCK_NO-1));

  //read from mbox is one clock ahead of writes
  //stall reads based on hold signal from mbox (which is asserted during ECC write-back)
  //don't read the next dword if we are writing the last dword of a block and core isn't ready
  //keep stalling the read once the block is full until core is ready - this will reset the block pointer and start the next one
  always_comb mbox_read_en = mailbox_mode & ~mbox_read_done & !sha_sram_hold & ~(mbox_mode_last_dword_wr | block_full);

  always_comb sha_sram_req_dv = mbox_read_en;
  always_comb sha_sram_req_addr = mbox_rdptr[CPTRA_MBOX_ADDR_W-1:0];

  //stall the write if we are trying to stream datain and it's the end of a block but the core isn't ready
  always_comb stall_write = datain_write & block_full;

  always_comb mbox_mode_block_we = (mailbox_mode & mbox_block_we);
  always_comb stream_mode_block_we = (streaming_mode & datain_write & ~stall_write);

  always_comb block_we = mbox_mode_block_we | stream_mode_block_we;
  
  genvar b;
  generate
    for (b=0; b<DATA_NUM_BYTES; b++) begin: DATAIN_SELECT_AND_SWIZZLE
      always_comb mbox_rdata[b]      = sha_sram_resp.rdata.data[b*8 +: 8];
      always_comb streaming_wdata[b] = req_data.wdata          [b*8 +: 8];
      always_comb input_data[b] = ({8{mailbox_mode}}   & mbox_rdata[b]     ) |
                                  ({8{streaming_mode}} & streaming_wdata[b]);
      always_comb swizzled_data[b] = hwif_out.MODE.ENDIAN_TOGGLE.value ? input_data[b] : //assign data as-is from input
                                                                         input_data[(DATA_NUM_BYTES-1-b)]; //convert data to big endian
    end
  endgenerate

  always_comb block_wdata = swizzled_data;

  //registers for the HW API
  always_ff @(posedge clk or negedge rst_b) begin : api_regs
    if (~rst_b) begin
      sha_fsm_ps    <= SHA_IDLE;
      soc_has_lock  <= '0;
      block_wptr    <= '0;
      mbox_rdptr    <= '0;
      mbox_block_we <= '0;
      block_reg     <= '0;
      num_bytes_wr  <= '0;
    end
    else begin
      sha_fsm_ps   <= sha_fsm_ns;
      soc_has_lock <= (hwif_in.lock_set & req_data.soc_req) ? '1 : 
                       hwif_out.LOCK.LOCK.value ? soc_has_lock : '0;

      block_wptr <= (arc_SHA_BLOCK_0_SHA_BLOCK_N | arc_SHA_BLOCK_N_SHA_BLOCK_N | arc_IDLE) ? '0 :
                    block_we                                                               ? block_wptr + 'd1 : 
                                                                                             block_wptr;

      mbox_rdptr <= arc_SHA_IDLE_SHA_BLOCK_0 & mailbox_mode ? {1'b0,mbox_start_addr} :
                    mbox_read_en                            ? mbox_rdptr + 'd1 :
                                                              mbox_rdptr;

      mbox_block_we <= mbox_read_en;

      num_bytes_wr <= arc_IDLE ? '0 :
                      block_we ? num_bytes_wr + 'd4 : num_bytes_wr;

      for (int dword = 0; dword < BLOCK_NO; dword++) begin
        block_reg[dword] <= block_we & (block_wptr[BLOCK_OFFSET_W-1:0] == dword) ? block_wdata : block_reg_nxt[dword];
      end
    end
  end

  //padding logic
  //this is how many bytes of data are in the last block
  assign num_bytes_data = hwif_out.DLEN.LENGTH.value[BYTE_OFFSET_W-1:0];
  //when there are >= 112 bytes of data in the block we can't fit the length
  assign extra_pad_block_required = (num_bytes_data >= 'd112);

  always_comb begin : sha_padding_logic
    pad_mask = '1;
    //set the valid bytes to '1 to keep the valid data and zero out the rest
    pad_mask = pad_mask << (1024-(num_bytes_data*8));
    //we append the length in bits to the least significant 128 bits
    pad_length = {{($bits(pad_length)-32){1'b0}}, hwif_out.DLEN.LENGTH.value} << 3;

    //First case - Padding and length fit - just pad and add the length in this block
    //This might be an empty padded block with just length if dlen is divisible by 1024
    if (~extra_pad_block_required & (arc_SHA_BLOCK_0_SHA_PAD0 | arc_SHA_BLOCK_N_SHA_PAD0)) begin
      block_reg_nxt_pad = block_reg & pad_mask;
      //force the pad bit on the MSB of the first byte of padding
      block_reg_nxt_pad[num_bytes_data] = 8'h80;
      //write the length in bits into the highest 128 bits
      //only if this is a case where dlen is divisible by 1024
      block_reg_nxt_pad[112:127] = pad_length;
    end
    //Second case - length won't fit, we need to first send valid data + pad followed by zeroes and length
    else if (extra_pad_block_required & (arc_SHA_BLOCK_0_SHA_PAD0 | arc_SHA_BLOCK_N_SHA_PAD0)) begin
      block_reg_nxt_pad = block_reg & pad_mask;
      //force the pad bit on the MSB of the first byte of padding
      block_reg_nxt_pad[num_bytes_data] = 8'h80;
    end
    //This is sending the zeroes and length since we started the padding in the previous block
    else if (arc_SHA_PAD0_SHA_PAD1) begin
      block_reg_nxt_pad = '0;
      //write the length in bits into the highest 128 bits
      block_reg_nxt_pad[112:127] = pad_length;
    end
    //Default case is to just send the block as-is
    else begin
      block_reg_nxt_pad = block_reg;
    end
    block_reg_nxt = block_reg_nxt_pad;
  end

  //byte address aligning to mailbox read pointer
  always_comb mbox_start_addr = hwif_out.START_ADDRESS.ADDR.value[CPTRA_MBOX_ADDR_W+1:2];

  //Convert DLEN to an end address. DLEN is in bytes, address is in dwords
  //detect overflow of end address to indicate we want to read to the end of the mailbox
  always_comb {mbox_read_to_end, mbox_end_addr} = mbox_start_addr + 
                                                  hwif_out.DLEN.LENGTH.value[CPTRA_MBOX_ADDR_W+2:2] + 
                                                  (hwif_out.DLEN.LENGTH.value[1] | hwif_out.DLEN.LENGTH.value[0]);
  
  always_comb mbox_read_done = (sha_fsm_ps == SHA_IDLE) | ~mailbox_mode | 
                               //If the DLEN overflowed our end address, just read to the end of the mailbox and stop
                               //Otherwise read until read pointer == end address
                               (~mbox_read_to_end & mbox_rdptr[CPTRA_MBOX_ADDR_W-1:0] == mbox_end_addr) | 
                               (mbox_read_to_end & mbox_rdptr[CPTRA_MBOX_ADDR_W]);

  //HW API State Machine
  //whenever lock is cleared, go back to idle
  always_comb arc_IDLE = ~hwif_out.LOCK.LOCK.value;
  //Streaming mode - go to block 0 when first datain comes
  //Mailbox mode - go to block 0 when execute is set
  always_comb arc_SHA_IDLE_SHA_BLOCK_0 = (sha_fsm_ps == SHA_IDLE) & (
                                         (streaming_mode & datain_write) |
                                         (mailbox_mode & execute_set));
  //When a full block is complete, send INIT and move to BLOCK_N state
  always_comb arc_SHA_BLOCK_0_SHA_BLOCK_N = (sha_fsm_ps == SHA_BLOCK_0) & block_full & core_ready_q;
  always_comb arc_SHA_BLOCK_N_SHA_BLOCK_N = (sha_fsm_ps == SHA_BLOCK_N) & block_full & core_ready_q;
  //When execute is set for streaming, OR we reach the end of the mailbox region, move to PAD0
  //If a block ends on 1024 bit boundary, we can't move to PAD until that block is processed
  //so we give priority to the end of block arcs, and move to PAD only after core is ready for the pad block
  always_comb arc_SHA_BLOCK_0_SHA_PAD0 = (sha_fsm_ps == SHA_BLOCK_0) & ~arc_SHA_BLOCK_0_SHA_BLOCK_N &
                                         (streaming_mode & (execute_set & core_ready_q) |
                                          mailbox_mode & (mbox_read_done & ~block_we & core_ready_q));
  always_comb arc_SHA_BLOCK_N_SHA_PAD0 = (sha_fsm_ps == SHA_BLOCK_N) & ~arc_SHA_BLOCK_N_SHA_BLOCK_N &
                                         (streaming_mode & (execute_set & core_ready_q) |
                                          mailbox_mode & (mbox_read_done & ~block_we & core_ready_q)); 
  //Moving to PAD0 fills in the padding for the current block and sends NEXT command
  //If we can't fit the length into the current block we'll need another block to pad and write the length in
  //So go to PAD1 after PAD0 in this case
  always_comb arc_SHA_PAD0_SHA_PAD1 = (sha_fsm_ps == SHA_PAD0) & extra_pad_block_required & core_ready_q;                            
  //Move to done state as soon as SHA is done with the final padded block
  always_comb arc_SHA_PAD0_SHA_DONE = (sha_fsm_ps == SHA_PAD0) & ~extra_pad_block_required & core_digest_valid_q;
  always_comb arc_SHA_PAD1_SHA_DONE = (sha_fsm_ps == SHA_PAD1) & core_digest_valid_q;

  //SHA API FSM State Combo
  always_comb begin : sha_api_combo
    //default back to present state
    sha_fsm_ns = sha_fsm_ps;

    unique case (sha_fsm_ps) inside
      SHA_IDLE: begin
        if (arc_SHA_IDLE_SHA_BLOCK_0) sha_fsm_ns = SHA_BLOCK_0;
      end
      SHA_BLOCK_0: begin
        if (arc_IDLE) sha_fsm_ns = SHA_IDLE;
        else if (arc_SHA_BLOCK_0_SHA_BLOCK_N) sha_fsm_ns = SHA_BLOCK_N;
        else if (arc_SHA_BLOCK_0_SHA_PAD0) sha_fsm_ns = SHA_PAD0;
      end
      SHA_BLOCK_N: begin
        if (arc_IDLE) sha_fsm_ns = SHA_IDLE;
        else if (arc_SHA_BLOCK_N_SHA_BLOCK_N) sha_fsm_ns = SHA_BLOCK_N;
        else if (arc_SHA_BLOCK_N_SHA_PAD0) sha_fsm_ns = SHA_PAD0;
      end
      SHA_PAD0: begin
        if (arc_IDLE) sha_fsm_ns = SHA_IDLE;
        else if (arc_SHA_PAD0_SHA_PAD1) sha_fsm_ns = SHA_PAD1;
        else if (arc_SHA_PAD0_SHA_DONE) sha_fsm_ns = SHA_DONE;
      end
      SHA_PAD1: begin
        if (arc_IDLE) sha_fsm_ns = SHA_IDLE;
        else if (arc_SHA_PAD1_SHA_DONE) sha_fsm_ns = SHA_DONE;
      end
      SHA_DONE: begin
        if (arc_IDLE) sha_fsm_ns = SHA_IDLE;
      end
      default: begin
        //TODO Error condition
        sha_fsm_ns = SHA_IDLE;
      end
    endcase
  end

//register hw interface
always_comb begin
  hwif_in.STATUS.VALID.next = (sha_fsm_ps == SHA_DONE);
  hwif_in.EXECUTE.EXECUTE.hwclr = arc_IDLE;
  for (int dword =0; dword < 16; dword++) begin
    hwif_in.DIGEST[dword].DIGEST.next = digest_reg[dword];
    hwif_in.DIGEST[dword].DIGEST.hwclr = zeroize_pulse;
  end
end

genvar i;
generate
    for (i=0;i<DATA_WIDTH;i++) begin: assign_biten_from_wstrb
        assign reg_biten[i] = req_data.wstrb[i/8];
    end
endgenerate

//Register Block
sha512_acc_csr i_sha512_acc_csr (
    .clk(clk),
    .rst(1'b0),

    .s_cpuif_req         (req_dv & (req_data.addr[SOC_IFC_ADDR_W-1:SHA512_ACC_CSR_ADDR_WIDTH] == SHA_REG_START_ADDR[SOC_IFC_ADDR_W-1:SHA512_ACC_CSR_ADDR_WIDTH])),
    .s_cpuif_req_is_wr   (req_data.write),
    .s_cpuif_addr        (req_data.addr[SHA512_ACC_CSR_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data     (req_data.wdata),
    .s_cpuif_wr_biten    (reg_biten),
    .s_cpuif_req_stall_wr( ),
    .s_cpuif_req_stall_rd( ),
    .s_cpuif_rd_ack      ( ),
    .s_cpuif_rd_err      (read_error),
    .s_cpuif_rd_data     (rdata),
    .s_cpuif_wr_ack      ( ),
    .s_cpuif_wr_err      (write_error),

    .hwif_in (hwif_in ),
    .hwif_out(hwif_out)
);

//Error conditions
//mailbox mode addressing errors
logic mailbox_address_err;
always_comb mailbox_address_err = (mbox_end_addr < mbox_start_addr); //calculated end comes before start

//interrupt register hw interface
assign hwif_in.cptra_rst_b = rst_b;
assign hwif_in.cptra_pwrgood = cptra_pwrgood;
assign hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = ~soc_has_lock & (arc_SHA_PAD0_SHA_DONE | arc_SHA_PAD1_SHA_DONE);
assign hwif_in.intr_block_rf.error_internal_intr_r.error0_sts.hwset = 1'b0; // TODO
assign hwif_in.intr_block_rf.error_internal_intr_r.error1_sts.hwset = 1'b0; // TODO
assign hwif_in.intr_block_rf.error_internal_intr_r.error2_sts.hwset = 1'b0; // TODO
assign hwif_in.intr_block_rf.error_internal_intr_r.error3_sts.hwset = 1'b0; // TODO

assign error_intr = hwif_out.intr_block_rf.error_global_intr_r.intr;
assign notif_intr = hwif_out.intr_block_rf.notif_global_intr_r.intr;

endmodule // sha512_acc_top
