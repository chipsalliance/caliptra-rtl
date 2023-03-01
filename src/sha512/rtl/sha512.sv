//======================================================================
// Updated by Caliptra team to modify data access width
// and removing the work factor
//
// sha512.sv
// --------
// Top level wrapper for the SHA-512 hash function providing
// a simple memory like interface with 32 bit data access.
//
//
// Author: Joachim Strombergson
// Copyright (c) 2014,  Secworks Sweden AB
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or
// without modification, are permitted provided that the following
// conditions are met:
//
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
// FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
// COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
// BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
// STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
// ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
//======================================================================

module sha512
    import sha512_reg_pkg::*;
    import kv_defines_pkg::*;    
    #(
        parameter ADDR_WIDTH = 32,
        parameter DATA_WIDTH = 64
    )(
        // Clock and reset.
        input wire           clk,
        input wire           reset_n,
        input wire           cptra_pwrgood,

        // Control.
        input wire           cs,
        input wire           we,

        // Data ports.
        input wire  [ADDR_WIDTH-1 : 0] address,
        input wire  [DATA_WIDTH-1 : 0] write_data,
        output wire [DATA_WIDTH-1 : 0] read_data,
        output wire          err,

        // KV interface
        output kv_read_t kv_read,
        output kv_write_t kv_write,
        input kv_rd_resp_t kv_rd_resp,
        input kv_wr_resp_t kv_wr_resp,

        // Interrupts
        output wire error_intr,
        output wire notif_intr
    );

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  `include "sha512_param.sv"

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  reg init_reg;
  reg next_reg;
  reg ready_reg;
  reg [1 : 0] mode_reg;
  logic zeroize_reg;

  localparam BLOCK_SIZE   = 1024;
  localparam DIG_SIZE     = 512;

  localparam BLOCK_NUM_DWORDS = BLOCK_SIZE / DATA_WIDTH;
  localparam DIG_NUM_DWORDS = DIG_SIZE / DATA_WIDTH;

  reg [DATA_WIDTH-1 : 0][BLOCK_NUM_DWORDS-1 : 0]    block_reg ;
  reg [DIG_NUM_DWORDS-1 : 0][DATA_WIDTH-1 : 0]      digest_reg;
  reg [DIG_NUM_DWORDS-1 : 0][DATA_WIDTH-1 : 0]      kv_reg;
  reg                                               digest_valid_reg;
  logic [DIG_NUM_DWORDS-1 : 0][DATA_WIDTH-1 : 0]    get_mask;

  sha512_reg__in_t hwif_in;
  sha512_reg__out_t hwif_out;
  logic read_error, write_error;

  //interface with client
  logic kv_src_write_en;
  logic [4:0] kv_src_write_offset;
  logic [31:0] kv_src_write_data;

  kv_error_code_e kv_src_error, kv_dest_error;
  logic kv_src_ready, kv_src_done;
  logic kv_dest_ready, kv_dest_done;

  logic dest_keyvault;
  kv_write_ctrl_reg_t kv_write_ctrl_reg;
  kv_read_ctrl_reg_t kv_read_ctrl_reg;

  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  wire                                          core_ready;
  wire [BLOCK_SIZE-1 : 0]                       core_block;
  wire [DIG_NUM_DWORDS-1 : 0][DATA_WIDTH-1 : 0] core_digest;
  wire                                          core_digest_valid;

  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
   assign core_block = { block_reg[00], block_reg[01], block_reg[02], block_reg[03],
                         block_reg[04], block_reg[05], block_reg[06], block_reg[07],
                         block_reg[08], block_reg[09], block_reg[10], block_reg[11],
                         block_reg[12], block_reg[13], block_reg[14], block_reg[15],
                         block_reg[16], block_reg[17], block_reg[18], block_reg[19],
                         block_reg[20], block_reg[21], block_reg[22], block_reg[23],
                         block_reg[24], block_reg[25], block_reg[26], block_reg[27],
                         block_reg[28], block_reg[29], block_reg[30], block_reg[31]};
  
  assign err = read_error | write_error;

  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  sha512_core core(
                   .clk(clk),
                   .reset_n(reset_n),
                   .zeroize(zeroize_reg),

                   .init_cmd(init_reg),
                   .next_cmd(next_reg),
                   .mode(mode_reg),

                   .work_factor(1'b0),
                   .work_factor_num(32'b0),

                   .block_msg(core_block),

                   .ready(core_ready),

                   .digest(core_digest),
                   .digest_valid(core_digest_valid)
                  );


  //----------------------------------------------------------------
  // reg_update
  //
  // Update functionality for all registers in the core.
  // All registers are positive edge triggered with asynchronous
  // active low reset. All registers have write enable.
  //----------------------------------------------------------------
  always @ (posedge clk or negedge reset_n) begin : reg_update
    if (!reset_n) begin
      ready_reg           <= '0;
      digest_reg          <= '0;
      digest_valid_reg    <= '0;
      kv_reg              <= '0;
    end
    else if (zeroize_reg) begin
      ready_reg           <= '0;
      digest_reg          <= '0;
      digest_valid_reg    <= '0;
      kv_reg              <= '0;
    end
    else begin
      ready_reg        <= core_ready;
      digest_valid_reg <= core_digest_valid;

      if (core_digest_valid & ~digest_valid_reg & ~dest_keyvault)
        digest_reg <= core_digest & get_mask;
      if (core_digest_valid & ~digest_valid_reg & dest_keyvault)
        kv_reg <= core_digest & get_mask;

    end
  end // reg_update

  always_comb begin
    unique casez (mode_reg)
      2'b00 :    get_mask = {{7{32'hffffffff}}, {9{32'h00000000}}};   //SHA512/224
      2'b01 :    get_mask = {{8{32'hffffffff}}, {8{32'h00000000}}};   //SHA512/256
      2'b10 :    get_mask = {{12{32'hffffffff}}, {4{32'h00000000}}};  //SHA384
      default :  get_mask = {16{32'hffffffff}};                       //SHA512
    endcase
  end


  //register hw interface
  always_comb begin

    hwif_in.SHA512_NAME[0].NAME.next = CORE_NAME0;
    hwif_in.SHA512_NAME[1].NAME.next = CORE_NAME1;

    hwif_in.SHA512_VERSION[0].VERSION.next = CORE_VERSION0;
    hwif_in.SHA512_VERSION[1].VERSION.next = CORE_VERSION1;

    init_reg = hwif_out.SHA512_CTRL.INIT.value;
    next_reg = hwif_out.SHA512_CTRL.NEXT.value;
    mode_reg = hwif_out.SHA512_CTRL.MODE.value;
    zeroize_reg = hwif_out.SHA512_CTRL.ZEROIZE.value;

    hwif_in.SHA512_STATUS.READY.next = ready_reg;
    hwif_in.SHA512_STATUS.VALID.next = digest_valid_reg;

    //output comes in big endian
    for (int dword =0; dword < DIG_NUM_DWORDS; dword++) begin
      hwif_in.SHA512_DIGEST[dword].DIGEST.next = digest_reg[15-dword];
      hwif_in.SHA512_DIGEST[dword].DIGEST.hwclr = zeroize_reg;
    end

    for (int dword=0; dword< BLOCK_NUM_DWORDS; dword++) begin
      block_reg[dword] = hwif_out.SHA512_BLOCK[dword].BLOCK.value;
      hwif_in.SHA512_BLOCK[dword].BLOCK.we = (kv_src_write_en & (kv_src_write_offset == dword));
      hwif_in.SHA512_BLOCK[dword].BLOCK.next = kv_src_write_data;
      hwif_in.SHA512_BLOCK[dword].BLOCK.hwclr = zeroize_reg;
    end
    //Set valid when fsm is done
    hwif_in.SHA512_KV_RD_STATUS.ERROR.next = kv_src_error;
    hwif_in.SHA512_KV_WR_STATUS.ERROR.next = kv_dest_error;
    //Set valid when fsm is done
    hwif_in.SHA512_KV_RD_STATUS.READY.next = kv_src_ready;
    hwif_in.SHA512_KV_WR_STATUS.READY.next = kv_dest_ready;
    //Set valid when fsm is done
    hwif_in.SHA512_KV_RD_STATUS.VALID.hwset = kv_src_done;
    hwif_in.SHA512_KV_WR_STATUS.VALID.hwset = kv_dest_done;
    //reset valid when fsm is started
    hwif_in.SHA512_KV_RD_STATUS.VALID.hwclr = kv_read_ctrl_reg.read_en;
    hwif_in.SHA512_KV_WR_STATUS.VALID.hwclr = kv_write_ctrl_reg.write_en;
    //clear en when busy
    hwif_in.SHA512_KV_RD_CTRL.read_en.hwclr = ~kv_src_ready;
    hwif_in.SHA512_KV_WR_CTRL.write_en.hwclr = ~kv_dest_ready;

  end

  `CALIPTRA_KV_WRITE_CTRL_REG2STRUCT(kv_write_ctrl_reg, SHA512_KV_WR_CTRL)
  `CALIPTRA_KV_READ_CTRL_REG2STRUCT(kv_read_ctrl_reg, SHA512_KV_RD_CTRL)


// Register Block
sha512_reg i_sha512_reg (
    .clk(clk),
    .rst(1'b0),

    .s_cpuif_req         (cs),
    .s_cpuif_req_is_wr   (we),
    .s_cpuif_addr        (address[SHA512_REG_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data     (write_data                              ),
    .s_cpuif_req_stall_wr( ),
    .s_cpuif_req_stall_rd( ),
    .s_cpuif_rd_ack      ( ),
    .s_cpuif_rd_err      (read_error),
    .s_cpuif_rd_data     (read_data),
    .s_cpuif_wr_ack      ( ),
    .s_cpuif_wr_err      (write_error),

    .hwif_in (hwif_in ),
    .hwif_out(hwif_out)
);

//interrupt register hw interface
assign hwif_in.reset_b = reset_n;
assign hwif_in.error_reset_b = cptra_pwrgood;
assign hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = core_digest_valid & ~digest_valid_reg;
assign hwif_in.intr_block_rf.error_internal_intr_r.error0_sts.hwset = 1'b0; // TODO
assign hwif_in.intr_block_rf.error_internal_intr_r.error1_sts.hwset = 1'b0; // TODO
assign hwif_in.intr_block_rf.error_internal_intr_r.error2_sts.hwset = 1'b0; // TODO
assign hwif_in.intr_block_rf.error_internal_intr_r.error3_sts.hwset = 1'b0; // TODO

assign error_intr = hwif_out.intr_block_rf.error_global_intr_r.intr;
assign notif_intr = hwif_out.intr_block_rf.notif_global_intr_r.intr;

//Read Block
kv_read_client #(
    .DATA_WIDTH(BLOCK_SIZE),
    .PAD(1)
)
sha512_block_kv_read
(
    .clk(clk),
    .rst_b(reset_n),

    //client control register
    .read_ctrl_reg(kv_read_ctrl_reg),

    //interface with kv
    .kv_read(kv_read),
    .kv_resp(kv_rd_resp),

    //interface with client
    .write_en(kv_src_write_en),
    .write_offset(kv_src_write_offset),
    .write_data(kv_src_write_data),

    .error_code(kv_src_error),
    .kv_ready(kv_src_ready),
    .read_done(kv_src_done)
);

kv_write_client #(
  .DATA_WIDTH(DIG_SIZE)
)
sha512_result_kv_write
(
  .clk(clk),
  .rst_b(reset_n),

  //client control register
  .write_ctrl_reg(kv_write_ctrl_reg),

  //interface with kv
  .kv_write(kv_write),
  .kv_resp(kv_wr_resp),

  //interface with client
  .dest_keyvault(dest_keyvault),
  .dest_data_avail(core_digest_valid & ~digest_valid_reg),
  .dest_data(kv_reg),

  .error_code(kv_dest_error),
  .kv_ready(kv_dest_ready),
  .dest_done(kv_dest_done)
);

endmodule // sha512

//======================================================================
// EOF sha512.sv
//======================================================================
