//======================================================================
// Updated by Caliptra team to modify data access width
//
// sha512.v
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

`default_nettype none

module sha512 #(
              parameter ADDR_WIDTH = 32,
              parameter DATA_WIDTH = 64
              )(
              // Clock and reset.
              input wire           clk,
              input wire           reset_n,

              // Control.
              input wire           cs,
              input wire           we,

              // Data ports.
              input wire  [ADDR_WIDTH-1 : 0] address,
              input wire  [DATA_WIDTH-1 : 0] write_data,
              output wire [DATA_WIDTH-1 : 0] read_data,
              output wire          error
             );

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  `include "sha512_param.sv"

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  reg init_reg;
  reg init_new;

  reg next_reg;
  reg next_new;

  reg ready_reg;

  reg work_factor_reg;
  reg work_factor_new;
  reg work_factor_we;

  reg [1 : 0] mode_reg;
  reg [1 : 0] mode_new;
  reg         mode_we;

  reg [31 : 0] work_factor_num_reg;
  reg          work_factor_num_we;

  localparam BLOCK_NO = 1024 / DATA_WIDTH;
  reg [DATA_WIDTH-1 : 0] block_reg [0 : BLOCK_NO-1];
  reg          block_we;

  reg [511 : 0] digest_reg;
  reg           digest_valid_reg;


  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  wire            core_ready;
  wire [1023 : 0] core_block;
  wire [511 : 0]  core_digest;
  wire            core_digest_valid;

  reg [DATA_WIDTH-1 : 0]  tmp_read_data;
  reg                     tmp_error;


  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  `ifdef DATA_BUS_64
    assign core_block = { block_reg[00], block_reg[01], block_reg[02], block_reg[03],
                          block_reg[04], block_reg[05], block_reg[06], block_reg[07],
                          block_reg[08], block_reg[09], block_reg[10], block_reg[11],
                          block_reg[12], block_reg[13], block_reg[14], block_reg[15]};
  `else
    assign core_block = { block_reg[00], block_reg[01], block_reg[02], block_reg[03],
                          block_reg[04], block_reg[05], block_reg[06], block_reg[07],
                          block_reg[08], block_reg[09], block_reg[10], block_reg[11],
                          block_reg[12], block_reg[13], block_reg[14], block_reg[15],
                          block_reg[16], block_reg[17], block_reg[18], block_reg[19],
                          block_reg[20], block_reg[21], block_reg[22], block_reg[23],
                          block_reg[24], block_reg[25], block_reg[26], block_reg[27],
                          block_reg[28], block_reg[29], block_reg[30], block_reg[31]};
  `endif

  assign read_data = tmp_read_data;
  assign error     = tmp_error;


  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  sha512_core core(
                   .clk(clk),
                   .reset_n(reset_n),

                   .init(init_reg),
                   .next(next_reg),
                   .mode(mode_reg),

                   .work_factor(work_factor_reg),
                   .work_factor_num(work_factor_num_reg),

                   .block(core_block),

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
  always @ (posedge clk or negedge reset_n)
    begin : reg_update
      integer i;

      if (!reset_n)
        begin
          for (i = 0 ; i < BLOCK_NO ; i = i + 1)
            block_reg[i] <= 0;

          init_reg            <= 1'h0;
          next_reg            <= 1'h0;
          mode_reg            <= MODE_SHA_512;
          work_factor_reg     <= 1'h0;
          work_factor_num_reg <= DEFAULT_WORK_FACTOR_NUM;
          ready_reg           <= 1'h0;
          digest_reg          <= 512'h0;
          digest_valid_reg    <= 1'h0;
        end
      else
        begin
          ready_reg        <= core_ready;
          digest_valid_reg <= core_digest_valid;
          init_reg         <= init_new;
          next_reg         <= next_new;

          if (mode_we)
            mode_reg <= mode_new;

          if (work_factor_we)
            work_factor_reg <= work_factor_new;

          if (work_factor_num_we)
            work_factor_num_reg <= write_data[31 : 0];

          if (core_digest_valid)
            digest_reg <= core_digest;

          if (block_we)
            `ifdef DATA_BUS_64
              block_reg[address[6 : 3]] <= write_data;
            `else
              block_reg[address[6 : 2]] <= write_data;
            `endif
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
      init_new           = 1'h0;
      next_new           = 1'h0;
      mode_new           = MODE_SHA_512;
      mode_we            = 1'h0;
      work_factor_new    = 1'h0;
      work_factor_we     = 1'h0;
      work_factor_num_we = 1'h0;
      block_we           = 1'h0;
      tmp_read_data      = '0;
      tmp_error          = 1'h0;

      if (cs)
        begin
          if (we)
            begin
              if ((address >= ADDR_BLOCK_START) && (address <= ADDR_BLOCK_END))
                block_we = 1'h1;

              case (address)
                ADDR_CTRL:
                  begin
                    init_new        = write_data[CTRL_INIT_BIT];
                    next_new        = write_data[CTRL_NEXT_BIT];
                    mode_new        = write_data[CTRL_MODE_HIGH_BIT : CTRL_MODE_LOW_BIT];
                    mode_we         = 1'h1;
                    work_factor_new = write_data[CTRL_WORK_FACTOR_BIT];
                    work_factor_we  = 1'h1;
                  end

                ADDR_WORK_FACTOR_NUM:
                  work_factor_num_we = 1'h1;

                default:
                    tmp_error = 1'h1;
              endcase // case (address)
            end // if (we)

          else
            begin
              
              if ((address >= ADDR_DIGEST_START) && (address <= ADDR_DIGEST_END))
                `ifdef DATA_BUS_64
                  tmp_read_data = digest_reg[(7 - ((address - ADDR_DIGEST_START) >> 3)) * DATA_WIDTH +: DATA_WIDTH];
                `else
                  tmp_read_data = digest_reg[(15 - ((address - ADDR_DIGEST_START) >> 2)) * DATA_WIDTH +: DATA_WIDTH];
                `endif

              if ((address >= ADDR_BLOCK_START) && (address <= ADDR_BLOCK_END))
                `ifdef DATA_BUS_64
                  tmp_read_data = block_reg[address[6 : 3]];
                `else
                  tmp_read_data = block_reg[address[6 : 2]];
                `endif
              
              case (address)
                ADDR_NAME0:
                  tmp_read_data = {CORE_NAME1, CORE_NAME0};

                ADDR_NAME1:
                  tmp_read_data = CORE_NAME1;

                ADDR_VERSION0:
                  tmp_read_data = {CORE_VERSION1, CORE_VERSION0};

                ADDR_VERSION1:
                  tmp_read_data = CORE_VERSION1;

                ADDR_CTRL:
                  tmp_read_data = {work_factor_reg, 3'b0, mode_reg, next_reg, init_reg};

                ADDR_STATUS:
                  tmp_read_data = {digest_valid_reg, ready_reg};

                ADDR_WORK_FACTOR_NUM:
                  tmp_read_data = work_factor_num_reg;

                default:
                  tmp_error = 1'h1;
              endcase // case (address)
            end
        end
    end // addr_decoder
endmodule // sha512

//======================================================================
// EOF sha512.v
//======================================================================
