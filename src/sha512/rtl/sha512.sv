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

`default_nettype none

module sha512
    import sha512_intr_regs_pkg::*;
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
  reg init_new;

  reg next_reg;
  reg next_new;

  reg ready_reg;

  reg [1 : 0] mode_reg;
  reg [1 : 0] mode_new;
  reg         mode_we;

  localparam BLOCK_NO = 1024 / DATA_WIDTH;
  reg [DATA_WIDTH-1 : 0] block_reg [0 : BLOCK_NO-1];
  reg          block_we;

  reg [511 : 0] digest_reg;
  reg           digest_valid_reg;

  // Interrupts
  logic intr_reg_we;
  logic [31:0] intr_reg_read_data;
  sha512_intr_regs__in_t hwif_in;
  sha512_intr_regs__out_t hwif_out;


  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  wire            core_ready;
  wire [1023 : 0] core_block;
  wire [511 : 0]  core_digest;
  wire            core_digest_valid;

  reg [DATA_WIDTH-1 : 0]  tmp_read_data;
  reg                     tmp_err;


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
  
  assign read_data = tmp_read_data;
  assign err    = tmp_err;


  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  sha512_core core(
                   .clk(clk),
                   .reset_n(reset_n),

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
  always @ (posedge clk or negedge reset_n)
    begin : reg_update
      integer ii;

      if (!reset_n)
        begin
          for (ii = 0 ; ii < BLOCK_NO ; ii = ii + 1)
            block_reg[ii] <= 0;

          init_reg            <= 1'h0;
          next_reg            <= 1'h0;
          mode_reg            <= MODE_SHA_512;
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

          if (core_digest_valid)
            digest_reg <= core_digest;

          if (block_we)
            block_reg[address[6 : 2]] <= write_data;
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
      block_we           = 1'h0;
      intr_reg_we        = 1'b0;
      tmp_read_data      = '0;
      tmp_err          = 1'h0;

      if (cs)
        begin
          if (we)
            begin
              if ((address >= ADDR_BLOCK_START) && (address <= ADDR_BLOCK_END))
                block_we = 1'h1;

              if ((address >= SHA512_ADDR_INTR_START) && (address <= SHA512_ADDR_INTR_END))
                intr_reg_we = 1'h1;

              case (address)
                ADDR_CTRL:
                  begin
                    init_new        = write_data[CTRL_INIT_BIT];
                    next_new        = write_data[CTRL_NEXT_BIT];
                    mode_new        = write_data[CTRL_MODE_HIGH_BIT : CTRL_MODE_LOW_BIT];
                    mode_we         = 1'h1;
                  end

                default:
                    tmp_err = 1'h1;
              endcase // case (address)
            end // if (we)

          else
            begin
              
              if ((address >= ADDR_DIGEST_START) && (address <= ADDR_DIGEST_END))
                tmp_read_data = digest_reg[(15 - ((address - ADDR_DIGEST_START) >> 2)) * DATA_WIDTH +: DATA_WIDTH];

              if ((address >= ADDR_BLOCK_START) && (address <= ADDR_BLOCK_END))
                tmp_read_data = block_reg[address[6 : 2]];
              
              if ((address >= SHA512_ADDR_INTR_START) && (address <= SHA512_ADDR_INTR_END))
                tmp_read_data = intr_reg_read_data;

              case (address)
                ADDR_NAME0:
                  tmp_read_data = CORE_NAME0;

                ADDR_NAME1:
                  tmp_read_data = CORE_NAME1;

                ADDR_VERSION0:
                  tmp_read_data = CORE_VERSION0;

                ADDR_VERSION1:
                  tmp_read_data = CORE_VERSION1;

                ADDR_CTRL:
                  tmp_read_data = {28'h0, mode_reg, next_reg, init_reg};

                ADDR_STATUS:
                  tmp_read_data = {30'h0, digest_valid_reg, ready_reg};

                default:
                  tmp_err = 1'h1;
              endcase // case (address)
            end
        end
    end // addr_decoder

// Interrupt Registers
sha512_intr_regs i_sha512_intr_regs (
    .clk(clk),
    .rst(1'b0),

    .s_cpuif_req         (cs                                      ),
    .s_cpuif_req_is_wr   (intr_reg_we                             ),
    .s_cpuif_addr        (address[SHA512_INTR_REGS_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data     (write_data                              ),
    .s_cpuif_req_stall_wr(                                        ),
    .s_cpuif_req_stall_rd(                                        ),
    .s_cpuif_rd_ack      (                                        ),
    .s_cpuif_rd_err      (                                        ),
    .s_cpuif_rd_data     (intr_reg_read_data                      ),
    .s_cpuif_wr_ack      (                                        ),
    .s_cpuif_wr_err      (                                        ),

    .hwif_in (hwif_in ),
    .hwif_out(hwif_out)
);

assign hwif_in.reset_b = reset_n;
assign hwif_in.error_reset_b = cptra_pwrgood;
assign hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = core_digest_valid & ~digest_valid_reg;

assign error_intr = hwif_out.intr_block_rf.error_global_intr_r.intr;
assign notif_intr = hwif_out.intr_block_rf.notif_global_intr_r.intr;


endmodule // sha512

//======================================================================
// EOF sha512.sv
//======================================================================
