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
//==============================================================================
//
// aes_cbc.v
// --------
// The module supports AES_CBC and it is the modified version of aes.v file. 
// In the hierarcy, one level up module is the aes_ctrl_32.sv or aes_ctrl_64.sv  
// This module receives the data from AHB just before decoding it into block, 
// key, and IV.
//
// The "IV XOR Plaintext" operation is just added into the AES first Key XOR path.
// The combinational logical path is ((IV XOR Plaintext) XOR Key). The lower
// hierarcy, aes core, has not been changed. Instead, aes_core_cbc was created.
// The created design differs from the original one only with an XOR operation. 
//
// AES CBC mode is tested with aes_cbc_tb.sv
// 
// 
//==============================================================================

`default_nettype none

module aes_cbc 
  import aes_param_pkg::*;
  import kv_defines_pkg::*;
  import aes_intr_regs_pkg::*;
 #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
  )
  (
   // Clock and reset.
   input wire           clk,
   input wire           reset_n,
   input wire           cptra_pwrgood,

   input wire [255:0] cptra_obf_key,

   //Obfuscated UDS and FE
   input wire [31:0][31:0] obf_field_entropy,
   input wire [11:0][31:0] obf_uds_seed,

   // Control.
   input wire           cs,
   input wire           we,

   // Data ports.
   input wire  [ADDR_WIDTH-1 : 0] address,
   input wire  [DATA_WIDTH-1 : 0] write_data,
   output wire [DATA_WIDTH-1 : 0] read_data,

   // Interrupt Outputs
   output error_intr,
   output notif_intr,

   //interface with kv
   output kv_write_t kv_write
  );

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  reg init_reg;
  reg init_new;

  reg next_reg;
  reg next_new;

  reg encdec_reg;
  reg keylen_reg;
  reg config_we;
  reg kv_ctrl_we;
  reg intr_regs_we;

  localparam BLOCK_NO = 128 / DATA_WIDTH;
  localparam KEY_NO   = 256 / DATA_WIDTH;
  localparam IV_NO    = 128 / DATA_WIDTH;

  logic [BLOCK_NO-1:0][DATA_WIDTH-1:0] block_reg ;
  reg          block_we;

  logic [KEY_NO-1:0][DATA_WIDTH-1:0] key_reg ;
  reg          key_we;

  reg [DATA_WIDTH - 1 : 0] IV_reg [BLOCK_NO - 1 : 0];
  reg          IV_we;

  reg [127 : 0] result_reg;
  reg [127 : 0] kv_result_reg;
  logic [31  : 0] intr_reg_data;
  reg           valid_reg;
  reg           ready_reg;
  logic         core_valid_p;

  reg [3:0] addr_diff;
  reg [1:0] temp_result;
  reg [1:0] result_idx;


  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  reg [DATA_WIDTH - 1  : 0]   tmp_read_data;

  wire           core_encdec;
  wire           core_init;
  wire           core_next;
  wire           core_ready;
  wire [255 : 0] core_key;
  wire           core_keylen;
  wire [127 : 0] core_block;
  wire [127 : 0] core_IV;
  wire [127 : 0] core_result;
  wire           core_valid;



  //client control register
  kv_doe_reg_t doe_ctrl_reg;

  //interface with client
  logic doe_key_write_en;
  logic doe_src_write_en;
  logic [127:0] doe_src_write_data;

  logic doe_init;
  logic doe_next;

  logic doe_flow_ip;

  logic flow_done;

  aes_intr_regs__in_t  intr_regs_hwif_in;
  aes_intr_regs__out_t intr_regs_hwif_out;


  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign read_data = tmp_read_data;

  assign core_key     = {key_reg[0], key_reg[1], key_reg[2], key_reg[3], key_reg[4], key_reg[5], key_reg[6], key_reg[7]};
  assign core_block   = {block_reg[0], block_reg[1], block_reg[2], block_reg[3]};
  assign core_IV      = {IV_reg[0], IV_reg[1], IV_reg[2], IV_reg[3]};

  assign core_init   = init_reg | doe_init;
  assign core_next   = next_reg | doe_next;
  assign core_encdec = encdec_reg & ~doe_flow_ip; //force decypher for DOE
  assign core_keylen = keylen_reg | doe_flow_ip; //force 256b KEY for DOE


  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  aes_core_cbc core(
                .clk(clk),
                .reset_n(reset_n),

                .encdec(core_encdec),
                .init_cmd(core_init),
                .next_cmd(core_next),
                .ready(core_ready),

                .key(core_key),
                .keylen(core_keylen),

                .IV(core_IV),
                .IV_updated(IV_we),

                .block_msg(core_block),
                .result(core_result),
                .result_valid(core_valid)
               );


  //----------------------------------------------------------------
  // reg_update
  // Update functionality for all registers in the core.
  // All registers are positive edge triggered with asynchronous
  // active low reset.
  //----------------------------------------------------------------
  always @ (posedge clk or negedge reset_n)
    begin : reg_update
      integer ii;

      if (!reset_n)
        begin
          for (ii = 0 ; ii < BLOCK_NO ; ii = ii + 1)
            block_reg[ii] <= '{default:0};

          for (ii = 0 ; ii < IV_NO ; ii = ii + 1)
            IV_reg[ii] <= 32'h0;

          for (ii = 0 ; ii < KEY_NO ; ii = ii + 1)
            key_reg[ii] <= 32'h0;

          init_reg   <= 1'b0;
          next_reg   <= 1'b0;
          encdec_reg <= 1'b0;
          keylen_reg <= 1'b0;

          result_reg <= 128'h0;
          valid_reg  <= 1'b0;
          ready_reg  <= 1'b0;

          kv_result_reg <= 128'h0;
          doe_ctrl_reg <= '0;
        end
      else
        begin
          ready_reg  <= core_ready;
          valid_reg  <= core_valid;
          if (~doe_flow_ip)
            result_reg <= core_result;
          else if (doe_flow_ip)
            kv_result_reg <= core_result;
          init_reg   <= init_new;
          next_reg   <= next_new;

          if (config_we)
            begin
              encdec_reg <= write_data[AES_CTRL_ENCDEC_BIT];
              keylen_reg <= write_data[AES_CTRL_KEYLEN_BIT];
            end

          if (key_we)
            key_reg[address[4 : 2]] <= write_data;
          else if (doe_key_write_en) 
            key_reg <= cptra_obf_key;
          if (block_we)
            block_reg[address[3 : 2]] <= write_data;
          else if (doe_src_write_en) 
            block_reg <= doe_src_write_data;
          if (IV_we)
            IV_reg[address[3 : 2]] <= write_data;
          if (kv_ctrl_we) begin
            doe_ctrl_reg.flow_done  <= write_data[0];
            doe_ctrl_reg.dest_sel   <= write_data[3:1];
            doe_ctrl_reg.cmd        <= kv_doe_cmd_e'(write_data[5:4]);
          end
          else if (flow_done) begin
            doe_ctrl_reg.cmd <= DOE_NOP;
            doe_ctrl_reg.dest_sel <= '0;
            doe_ctrl_reg.flow_done <= 1'b1;
          end
        end
    end // reg_update


  //----------------------------------------------------------------
  // api
  //
  // The interface command decoding logic.
  //----------------------------------------------------------------
  always @* begin
    addr_diff = (address[3:0] - AES_ADDR_RESULT_START[3:0]);
    temp_result = 4'h3 - (addr_diff >> 2);
    result_idx = temp_result[1:0];
  end

  always @*
    begin : api
      init_new      = 1'b0;
      next_new      = 1'b0;
      config_we     = 1'b0;
      key_we        = 1'b0;
      block_we      = 1'b0;
      IV_we         = 1'b0;
      kv_ctrl_we    = 1'b0;
      intr_regs_we  = 1'b0;
      tmp_read_data = 32'h0;

      if (cs)
        begin
          if (we)
            begin
              if (address == AES_ADDR_CTRL)
                begin
                  init_new = write_data[AES_CTRL_INIT_BIT];
                  next_new = write_data[AES_CTRL_NEXT_BIT];
                end

              if (address == AES_ADDR_CONFIG)
                config_we = 1'b1;

              if ((address >= AES_ADDR_KEY_START) && (address <= AES_ADDR_KEY_END))
                key_we = 1'b1;

              if ((address >= AES_ADDR_BLOCK_START) && (address <= AES_ADDR_BLOCK_END))
                block_we = 1'b1;

              if ((address >= AES_ADDR_IV_START) && (address <= AES_ADDR_IV_END))
                IV_we = 1'b1;
              if (address == AES_ADDR_KV_CTRL)
                kv_ctrl_we = 1'b1;
              if ((address >= AES_ADDR_INTR_START) && (address <= AES_ADDR_INTR_END))
                intr_regs_we = 1'b1;
            end // if (we)

          else
            begin
              case (address) inside
                `ifdef AES_DATA_BUS_64
                  AES_ADDR_NAME0:    tmp_read_data = AES_CORE_NAME;
                  AES_ADDR_VERSION0: tmp_read_data = AES_CORE_VERSION;
                  AES_ADDR_CTRL:     tmp_read_data = {60'h0, keylen_reg, encdec_reg, next_reg, init_reg};
                  AES_ADDR_STATUS:   tmp_read_data = {62'h0, valid_reg, ready_reg};
                  [AES_ADDR_RESULT_START:AES_ADDR_RESULT_END]: tmp_read_data = result_reg[(1 - ((address - AES_ADDR_RESULT_START) >> 3)) * 64 +: 64];
                  [AES_ADDR_INTR_START:AES_ADDR_INTR_END]: tmp_read_data = {32'h0,intr_reg_data};
                `else
                  AES_ADDR_NAME0:    tmp_read_data = AES_CORE_NAME[31 : 0];
                  AES_ADDR_NAME1:    tmp_read_data = AES_CORE_NAME[63 : 32];
                  AES_ADDR_VERSION0: tmp_read_data = AES_CORE_VERSION[31 : 0];
                  AES_ADDR_VERSION1: tmp_read_data = AES_CORE_VERSION[63 : 32];
                  AES_ADDR_CTRL:     tmp_read_data = {28'h0, keylen_reg, encdec_reg, next_reg, init_reg};
                  AES_ADDR_STATUS:   tmp_read_data = {30'h0, valid_reg, ready_reg};
                  AES_ADDR_KV_CTRL:  tmp_read_data = {26'h0, doe_ctrl_reg};
                  [AES_ADDR_RESULT_START:AES_ADDR_RESULT_END]: tmp_read_data = result_reg[result_idx * 32 +: 32];
                  [AES_ADDR_INTR_START:AES_ADDR_INTR_END]: tmp_read_data = intr_reg_data;
                `endif

                default:
                  begin
                    tmp_read_data = 32'h0;
                  end
              endcase // case (address)

            end
        end
    end // addr_decoder


kv_doe
kv_doe1 
(
  .clk(clk),
  .rst_b(reset_n),

    //Obfuscated UDS and FE
  .obf_field_entropy(obf_field_entropy),
  .obf_uds_seed(obf_uds_seed),

  //client control register
  .doe_ctrl_reg(doe_ctrl_reg),

  //interface with kv
  .kv_write(kv_write),

  //interface with client
  .key_write_en(doe_key_write_en),
  .src_write_en(doe_src_write_en),
  .src_write_data(doe_src_write_data),

  .doe_init(doe_init),
  .doe_next(doe_next),

  .doe_flow_ip(doe_flow_ip),
  .init_done(core_ready),
  .dest_data_avail(core_valid),
  .dest_data(kv_result_reg),

  .flow_done(flow_done)

);

always_comb core_valid_p = core_valid & ~valid_reg;

always_comb intr_regs_hwif_in.reset_b = reset_n;
always_comb intr_regs_hwif_in.error_reset_b = cptra_pwrgood;

// Pulse input to intr_regs to set the interrupt status bit and generate interrupt output (if enabled)
always_comb intr_regs_hwif_in.intr_block_rf.error_internal_intr_r.error0_sts.hwset  = 1'b0; // TODO please assign
always_comb intr_regs_hwif_in.intr_block_rf.error_internal_intr_r.error1_sts.hwset  = 1'b0; // TODO please assign
always_comb intr_regs_hwif_in.intr_block_rf.error_internal_intr_r.error2_sts.hwset  = 1'b0; // TODO please assign
always_comb intr_regs_hwif_in.intr_block_rf.error_internal_intr_r.error3_sts.hwset  = 1'b0; // TODO please assign
always_comb intr_regs_hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = core_valid_p;


aes_intr_regs i_intr_regs (
        .clk(clk),
        .rst(reset_n),

        .s_cpuif_req         (cs                                   ),
        .s_cpuif_req_is_wr   (intr_regs_we                         ),
        .s_cpuif_addr        (address[AES_INTR_REGS_ADDR_WIDTH-1:0]),
        .s_cpuif_wr_data     (write_data[31:0]                     ),

        .s_cpuif_req_stall_wr(                  ),
        .s_cpuif_req_stall_rd(                  ),
        .s_cpuif_rd_ack      (                  ),
        .s_cpuif_rd_err      (/*TODO*/          ),
        .s_cpuif_rd_data     (intr_reg_data     ),
        .s_cpuif_wr_ack      (                  ),
        .s_cpuif_wr_err      (/*TODO*/          ),

        .hwif_in             (intr_regs_hwif_in ),
        .hwif_out            (intr_regs_hwif_out)
    );

assign error_intr = intr_regs_hwif_out.intr_block_rf.error_global_intr_r.intr;
assign notif_intr = intr_regs_hwif_out.intr_block_rf.notif_global_intr_r.intr;

endmodule // aes

//======================================================================
// EOF aes.v
//======================================================================
