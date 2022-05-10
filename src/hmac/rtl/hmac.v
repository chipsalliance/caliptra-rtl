//======================================================================
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

module hmac(
            // Clock and reset.
            input wire           clk,
            input wire           reset_n,

            // Control.
            input wire           cs,
            input wire           we,

            // Data ports.
            input wire  [31 : 0] address,
            input wire  [63 : 0] write_data,
            output wire [63 : 0] read_data
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

  reg [63 : 0] key_reg [0 : 3];
  reg          key_we;

  reg [63 : 0] block_reg [0 : 7];
  reg          block_we;


  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  wire [255 : 0] core_key;
  wire [511 : 0] core_block;
  wire           core_ready;
  wire [255 : 0] core_tag;
  wire           core_tag_valid;

  reg [255 : 0]  tag_reg;
  reg [63  : 0]  tmp_read_data;

  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign core_block = {block_reg[00], block_reg[01], block_reg[02], block_reg[03],
                       block_reg[04], block_reg[05], block_reg[06], block_reg[07]};

  assign core_key = {key_reg[00], key_reg[01], key_reg[02], key_reg[03]};

  assign read_data = tmp_read_data;


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
          for (i = 0 ; i < 8 ; i = i + 1)
            block_reg[i] <= 64'h0;

          for (i = 0 ; i < 4 ; i = i + 1)
            key_reg[i] <= 64'h0;

          init_reg      <= 1'h0;
          next_reg      <= 1'h0;
          tag_reg       <= 256'h0;
          ready_reg     <= 0;
          tag_valid_reg <= 0;
        end
      else
        begin
          init_reg      <= init_new;
          next_reg      <= next_new;
          ready_reg     <= core_ready;
          tag_valid_reg <= core_ready;

          if (core_tag_valid)
            tag_reg <= core_tag;

          if (key_we)
            key_reg[address[4 : 3]] <= write_data;

          if (block_we)
            block_reg[address[5 : 3]] <= write_data;
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
      tmp_read_data = 64'h0;

      if (cs)
        begin
          if (we)
            begin
              if (address == ADDR_CTRL)
                begin
                  init_new     = write_data[CTRL_INIT_BIT];
                  next_new     = write_data[CTRL_NEXT_BIT];
                end

              if ((address >= ADDR_KEY0) && (address <= ADDR_KEY3))
                key_we = 1;

              if ((address >= ADDR_BLOCK0) && (address <= ADDR_BLOCK7))
                block_we = 1;
            end // if (we)

          else
            begin
              if ((address >= ADDR_TAG0) && (address <= ADDR_TAG3))
                tmp_read_data = tag_reg[(3 - ((address - ADDR_TAG0) >> 3)) * 64 +: 64];

              case (address)
                // Read operations.
                ADDR_NAME:
                  tmp_read_data = CORE_NAME;

                ADDR_VERSION:
                  tmp_read_data = CORE_VERSION;

                ADDR_STATUS:
                  tmp_read_data = {62'h0, tag_valid_reg, ready_reg};

                default:
                  begin
                  end
              endcase // case (address)
            end
        end
    end // addr_decoder
endmodule // hmac

//======================================================================
// EOF hmac.v
//======================================================================