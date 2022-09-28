//======================================================================
//
// Updated by: Emre Karabulut
// I updated the design data path. The addressing and data path were 
// based on 64-bit. After my update, the bus and addressing is 32-bit
//
//
// hmac.v
// ------
// Top level wrapper for the HMAC core providing a simple memory
// like interface with 32 bit data access.
//
//
// Author: Joachim Strombergson
// Copyright (c) 2018 Assured AB
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
`include "kv_defines.svh"

module hmac #(
            ADDR_WIDTH = 32
            )(
            // Clock and reset.
            input wire           clk,
            input wire           reset_n,

            // Control.
            input wire           cs,
            input wire           we,

            // Data ports.
            input wire  [ADDR_WIDTH - 1 : 0] address,
            input wire  [31 : 0] write_data,
            output wire [31 : 0] read_data,

            // KV interface
            output kv_read_t kv_read,
            output kv_write_t kv_write,
            input kv_resp_t kv_resp
           );

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  `include "hmac_param.sv"

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  reg init_reg;
  reg init_new;

  reg next_reg;
  reg next_new;
  
  reg ready_reg;
  reg tag_valid_reg;

  reg [31 : 0] key_reg [0 : 11];
  reg          key_we;

  reg [31 : 0] block_reg [0 : 31];
  reg          block_we;


  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  wire [383 : 0] core_key;
  wire [1023 : 0] core_block;
  wire           core_ready;
  wire [383 : 0] core_tag;
  wire           core_tag_valid;
  reg [383 : 0]  tag_reg;
  reg [383 : 0]  kv_reg;
  reg [31  : 0]  tmp_read_data;

  //interface with client
  logic kv_key_write_en;
  logic [3:0] kv_key_write_offset;
  logic [31:0] kv_key_write_data;
  logic kv_src_write_en;
  logic [4:0] kv_src_write_offset;
  logic [31:0] kv_src_write_data;

  logic kv_key_done;
  logic kv_src_done;
  logic kv_dest_done;

  logic dest_keyvault;
  logic kv_ctrl_we;
  kv_reg_t kv_ctrl_reg;
  logic core_tag_we;
  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign core_block = {block_reg[00], block_reg[01], block_reg[02], block_reg[03],
                       block_reg[04], block_reg[05], block_reg[06], block_reg[07],
                       block_reg[08], block_reg[09], block_reg[10], block_reg[11],
                       block_reg[12], block_reg[13], block_reg[14], block_reg[15],
                       block_reg[16], block_reg[17], block_reg[18], block_reg[19],
                       block_reg[20], block_reg[21], block_reg[22], block_reg[23],
                       block_reg[24], block_reg[25], block_reg[26], block_reg[27],
                       block_reg[28], block_reg[29], block_reg[30], block_reg[31]};

  assign core_key = {key_reg[00], key_reg[01], key_reg[02], key_reg[03], key_reg[04], key_reg[05],
                     key_reg[06], key_reg[07], key_reg[08], key_reg[09], key_reg[10], key_reg[11]};

  assign read_data = tmp_read_data;

  //rising edge detect on core tag valid
  assign core_tag_we = core_tag_valid & ~tag_valid_reg;

  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  hmac_core core(
                 .clk(clk),
                 .reset_n(reset_n),

                 .init(init_reg),
                 .next(next_reg),

                 .key(core_key),

                 .block(core_block),

                 .ready(core_ready),
                 .tag(core_tag),
                 .tag_valid(core_tag_valid)
                );


  //----------------------------------------------------------------
  // reg_update
  //
  // Update functionality for all registers in the core.
  // All registers are positive edge triggered with asynchronous
  // active low reset. All registers have write enable.
  //----------------------------------------------------------------
  always @ (posedge clk or negedge reset_n)
    begin : reg_update
      integer i;

      if (!reset_n)
        begin
          for (i = 0 ; i < 32 ; i = i + 1)
            block_reg[i] <= 32'h0;

          for (i = 0 ; i < 12 ; i = i + 1)
            key_reg[i] <= 32'h0;

          init_reg      <= 1'h0;
          next_reg      <= 1'h0;
          tag_reg       <= 384'h0;
          kv_reg        <= '0;
          kv_ctrl_reg   <= '0;
          ready_reg     <= 0;
          tag_valid_reg <= 0;
        end
      else
        begin
          init_reg      <= init_new;
          next_reg      <= next_new;
          ready_reg     <= core_ready;
          tag_valid_reg <= core_tag_valid;

          //write to sw register
          if (core_tag_we & ~dest_keyvault)
            tag_reg <= core_tag;
          if (core_tag_we & dest_keyvault)
            kv_reg <= core_tag;
          if (key_we)
            key_reg[address[5 : 2]] <= write_data;
          if (kv_key_write_en)
            key_reg[kv_key_write_offset] <= kv_key_write_data;
          if (block_we)
            block_reg[address[6 : 2]] <= write_data;
          if (kv_src_write_en)
            block_reg[kv_src_write_offset] <= kv_src_write_data;
          if (kv_ctrl_we)
            kv_ctrl_reg <= write_data;
          //clear key sel and set key done when key has been copied
          if (kv_key_done) begin
            kv_ctrl_reg.key_sel_en <= '0;
            kv_ctrl_reg.key_done <= '1;
          end
          //clear src sel and set src done when src has been copied
          if (kv_src_done) begin
            kv_ctrl_reg.src_sel_en <= '0;
            kv_ctrl_reg.src_done <= '1;
          end
          //clear dest sel and set dest done when dest has been copied
          if (kv_dest_done) begin
            kv_ctrl_reg.dest_done <= '1;
          end
          if (next_new) begin
            kv_ctrl_reg.dest_done <= '0;
          end
        end
    end // reg_update


  //----------------------------------------------------------------
  // api_logic
  //
  // Implementation of the api logic. If cs is enabled will either
  // try to write to or read from the internal registers.
  //----------------------------------------------------------------
  always @*
    begin : api_logic
      init_new      = 0;
      next_new      = 0;
      key_we        = 0;
      block_we      = 0;
      kv_ctrl_we    = 0;
      tmp_read_data = 32'h0;

      if (cs)
        begin
          if (we)
            begin
              if (address == HMAC_ADDR_CTRL)
                begin
                  init_new     = write_data[HMAC_CTRL_INIT_BIT];
                  next_new     = write_data[HMAC_CTRL_NEXT_BIT];
                end

              if ((address >= HMAC_ADDR_KEY0) && (address <= HMAC_ADDR_KEY11))
                key_we = 1;

              if ((address >= HMAC_ADDR_BLOCK0) && (address <= HMAC_ADDR_BLOCK31))
                block_we = 1;

              if (address == HMAC_KV_CTRL)
                kv_ctrl_we = 1;
            end // if (we)

          else
            begin
              if ((address >= HMAC_ADDR_TAG0) && (address <= HMAC_ADDR_TAG11))
                tmp_read_data = tag_reg[(11 - ((address - HMAC_ADDR_TAG0) >> 2)) * 32 +: 32];

              case (address)
                // Read operations.
                HMAC_ADDR_NAME0:
                  tmp_read_data = HMAC_CORE_NAME;
                
                HMAC_ADDR_NAME1:
                  tmp_read_data = HMAC_CORE_NAME;

                HMAC_ADDR_VERSION0:
                  tmp_read_data = HMAC_CORE_VERSION;

                HMAC_ADDR_VERSION1:
                  tmp_read_data = HMAC_CORE_VERSION;

                HMAC_ADDR_STATUS:
                  tmp_read_data = {30'h0, tag_valid_reg, ready_reg};

                HMAC_KV_CTRL:
                  tmp_read_data = kv_ctrl_reg;

                default:
                  begin
                  end
              endcase // case (address)
            end
        end
    end // addr_decoder

//keyvault module
kv_client #(
    .DEST_WIDTH(384),
    .KEY_WIDTH(384),
    .SRC_WIDTH(1024),
    .HMAC_PAD(1)
)
kv_client_hmac
(
    .clk(clk),
    .rst_b(reset_n),
    //client control register
    .client_ctrl_reg(kv_ctrl_reg), 

    //interface with kv
    .kv_read(kv_read),
    .kv_write(kv_write),
    .kv_resp(kv_resp),

    //interface with client
    .key_write_en(kv_key_write_en),
    .key_write_offset(kv_key_write_offset),
    .key_write_data(kv_key_write_data),
    .src_write_en(kv_src_write_en),
    .src_write_offset(kv_src_write_offset),
    .src_write_data(kv_src_write_data),

    .dest_keyvault(dest_keyvault),
    .dest_data_avail(core_tag_we),
    .dest_data(kv_reg),

    .key_done(kv_key_done),
    .src_done(kv_src_done),
    .dest_done(kv_dest_done)
);
endmodule // hmac

//======================================================================
// EOF hmac.v
//======================================================================