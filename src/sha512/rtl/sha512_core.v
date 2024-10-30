//======================================================================
//
// sha512_core.v
// -------------
// Verilog 2001 implementation of the SHA-512 hash function.
// This is the internal core with wide interfaces.
//
//
// Author: Joachim Strombergson
// Copyright (c) 2014 Secworks Sweden AB
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

module sha512_core(
                   // Clock and reset.
                   input wire            clk,
                   input wire            reset_n,
                   input wire            zeroize,
                   // Control.
                   input wire            init_cmd,
                   input wire            next_cmd,
                   input wire            restore_cmd,
                   input wire [1 : 0]    mode,
                   
                   // Data port.
                   input wire [1023 : 0] block_msg,
                   input wire [511  : 0] restore_digest,

                   output wire           ready,
                   output wire [511 : 0] digest,
                   output wire           digest_valid
                  );


  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam SHA512_ROUNDS = 79;

  localparam CTRL_IDLE   = 2'h0;
  localparam CTRL_ROUNDS = 2'h1;
  localparam CTRL_DONE   = 2'h2;


  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  reg [63 : 0] a_reg;
  reg [63 : 0] a_new;
  reg [63 : 0] b_reg;
  reg [63 : 0] b_new;
  reg [63 : 0] c_reg;
  reg [63 : 0] c_new;
  reg [63 : 0] d_reg;
  reg [63 : 0] d_new;
  reg [63 : 0] e_reg;
  reg [63 : 0] e_new;
  reg [63 : 0] f_reg;
  reg [63 : 0] f_new;
  reg [63 : 0] g_reg;
  reg [63 : 0] g_new;
  reg [63 : 0] h_reg;
  reg [63 : 0] h_new;
  reg          a_h_we;

  reg [63 : 0] H0_reg;
  reg [63 : 0] H0_new;
  reg [63 : 0] H1_reg;
  reg [63 : 0] H1_new;
  reg [63 : 0] H2_reg;
  reg [63 : 0] H2_new;
  reg [63 : 0] H3_reg;
  reg [63 : 0] H3_new;
  reg [63 : 0] H4_reg;
  reg [63 : 0] H4_new;
  reg [63 : 0] H5_reg;
  reg [63 : 0] H5_new;
  reg [63 : 0] H6_reg;
  reg [63 : 0] H6_new;
  reg [63 : 0] H7_reg;
  reg [63 : 0] H7_new;
  reg          H_we;

  reg [6 : 0]  round_ctr_reg;
  reg [6 : 0]  round_ctr_new;
  reg          round_ctr_we;
  reg          round_ctr_inc;
  reg          round_ctr_rst;

  reg          ready_reg;
  reg          ready_new;
  reg          ready_we;

  reg          digest_valid_reg;
  reg          digest_valid_new;
  reg          digest_valid_we;

  reg [1 : 0]  sha512_ctrl_reg;
  reg [1 : 0]  sha512_ctrl_new;
  reg          sha512_ctrl_we;


  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  reg digest_init;
  reg digest_update;

  reg state_init;
  reg state_update;

  reg first_block;
  reg restore;

  reg [63 : 0] t1;
  reg [63 : 0] t2;

  wire [63 : 0] k_data;

  reg           w_init;
  reg           w_next;
  wire [63 : 0] w_data;

  wire [63 : 0] H0_0;
  wire [63 : 0] H0_1;
  wire [63 : 0] H0_2;
  wire [63 : 0] H0_3;
  wire [63 : 0] H0_4;
  wire [63 : 0] H0_5;
  wire [63 : 0] H0_6;
  wire [63 : 0] H0_7;


  //----------------------------------------------------------------
  // Module instantiantions.
  //----------------------------------------------------------------
  sha512_k_constants k_constants_inst(
                                      .addr(round_ctr_reg),
                                      .K_val(k_data)
                                     );


  sha512_h_constants h_constants_inst(
                                      .mode(mode),

                                      .H0(H0_0),
                                      .H1(H0_1),
                                      .H2(H0_2),
                                      .H3(H0_3),
                                      .H4(H0_4),
                                      .H5(H0_5),
                                      .H6(H0_6),
                                      .H7(H0_7)
                                     );


  sha512_w_mem w_mem_inst(
                          .clk(clk),
                          .reset_n(reset_n),
                          .zeroize(zeroize),

                          .block_msg(block_msg),

                          .init_cmd(w_init),
                          .next_cmd(w_next),
                          .w_val(w_data)
                         );


  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign ready = ready_reg;

  assign digest = {H0_reg, H1_reg, H2_reg, H3_reg,
                   H4_reg, H5_reg, H6_reg, H7_reg};

  assign digest_valid = digest_valid_reg;


  //----------------------------------------------------------------
  // reg_update
  // Update functionality for all registers in the core.
  // All registers are positive edge triggered with asynchronous
  // active low reset. All registers have write enable.
  //----------------------------------------------------------------
  always @ (posedge clk or negedge reset_n)
    begin : reg_update
      if (!reset_n)
        begin
          a_reg               <= 64'h0;
          b_reg               <= 64'h0;
          c_reg               <= 64'h0;
          d_reg               <= 64'h0;
          e_reg               <= 64'h0;
          f_reg               <= 64'h0;
          g_reg               <= 64'h0;
          h_reg               <= 64'h0;
          H0_reg              <= 64'h0;
          H1_reg              <= 64'h0;
          H2_reg              <= 64'h0;
          H3_reg              <= 64'h0;
          H4_reg              <= 64'h0;
          H5_reg              <= 64'h0;
          H6_reg              <= 64'h0;
          H7_reg              <= 64'h0;
          ready_reg           <= 1'b1;
          digest_valid_reg    <= 1'b0;
          round_ctr_reg       <= 7'h0;
          sha512_ctrl_reg     <= CTRL_IDLE;
        end

      else if (zeroize) 
        begin
          a_reg               <= 64'h0;
          b_reg               <= 64'h0;
          c_reg               <= 64'h0;
          d_reg               <= 64'h0;
          e_reg               <= 64'h0;
          f_reg               <= 64'h0;
          g_reg               <= 64'h0;
          h_reg               <= 64'h0;
          H0_reg              <= 64'h0;
          H1_reg              <= 64'h0;
          H2_reg              <= 64'h0;
          H3_reg              <= 64'h0;
          H4_reg              <= 64'h0;
          H5_reg              <= 64'h0;
          H6_reg              <= 64'h0;
          H7_reg              <= 64'h0;
          ready_reg           <= 1'b1;
          digest_valid_reg    <= 1'b0;
          round_ctr_reg       <= 7'h0;
          sha512_ctrl_reg     <= CTRL_IDLE;
        end

      else
        begin
          if (a_h_we)
            begin
              a_reg <= a_new;
              b_reg <= b_new;
              c_reg <= c_new;
              d_reg <= d_new;
              e_reg <= e_new;
              f_reg <= f_new;
              g_reg <= g_new;
              h_reg <= h_new;
            end

          if (H_we)
            begin
              H0_reg <= H0_new;
              H1_reg <= H1_new;
              H2_reg <= H2_new;
              H3_reg <= H3_new;
              H4_reg <= H4_new;
              H5_reg <= H5_new;
              H6_reg <= H6_new;
              H7_reg <= H7_new;
            end

          if (round_ctr_we)
            round_ctr_reg <= round_ctr_new;

          if (ready_we)
            ready_reg <= ready_new;

          if (digest_valid_we)
            digest_valid_reg <= digest_valid_new;

          if (sha512_ctrl_we)
            sha512_ctrl_reg <= sha512_ctrl_new;
        end
    end // reg_update


  //----------------------------------------------------------------
  // digest_logic
  //
  // The logic needed to init as well as update the digest.
  //----------------------------------------------------------------
  always @*
    begin : digest_logic
      H0_new = 64'h0;
      H1_new = 64'h0;
      H2_new = 64'h0;
      H3_new = 64'h0;
      H4_new = 64'h0;
      H5_new = 64'h0;
      H6_new = 64'h0;
      H7_new = 64'h0;
      H_we = 0;

      if (digest_init)
        begin
          H0_new = H0_0;
          H1_new = H0_1;
          H2_new = H0_2;
          H3_new = H0_3;
          H4_new = H0_4;
          H5_new = H0_5;
          H6_new = H0_6;
          H7_new = H0_7;
          H_we = 1;
        end
      else if (restore)
        begin
          H0_new  = restore_digest[511 : 448];
          H1_new  = restore_digest[447 : 384];
          H2_new  = restore_digest[383 : 320];
          H3_new  = restore_digest[319 : 256];
          H4_new  = restore_digest[255 : 192];
          H5_new  = restore_digest[191 : 128];
          H6_new  = restore_digest[127 :  64];
          H7_new  = restore_digest[63  :   0];
          H_we = 1;
        end

      if (digest_update)
        begin
          H0_new = H0_reg + a_reg;
          H1_new = H1_reg + b_reg;
          H2_new = H2_reg + c_reg;
          H3_new = H3_reg + d_reg;
          H4_new = H4_reg + e_reg;
          H5_new = H5_reg + f_reg;
          H6_new = H6_reg + g_reg;
          H7_new = H7_reg + h_reg;
          H_we = 1;
        end
    end // digest_logic


  //----------------------------------------------------------------
  // t1_logic
  //
  // The logic for the T1 function.
  //----------------------------------------------------------------
  always @*
    begin : t1_logic
      reg [63 : 0] sum1;
      reg [63 : 0] ch;

      sum1 = {e_reg[13 : 0], e_reg[63 : 14]} ^
             {e_reg[17 : 0], e_reg[63 : 18]} ^
             {e_reg[40 : 0], e_reg[63 : 41]};

      ch = (e_reg & f_reg) ^ ((~e_reg) & g_reg);

      t1 = h_reg + sum1 + ch + k_data + w_data;
    end // t1_logic


  //----------------------------------------------------------------
  // t2_logic
  //
  // The logic for the T2 function
  //----------------------------------------------------------------
  always @*
    begin : t2_logic
      reg [63 : 0] sum0;
      reg [63 : 0] maj;

      sum0 = {a_reg[27 : 0], a_reg[63 : 28]} ^
             {a_reg[33 : 0], a_reg[63 : 34]} ^
             {a_reg[38 : 0], a_reg[63 : 39]};

      maj = (a_reg & b_reg) ^ (a_reg & c_reg) ^ (b_reg & c_reg);

      t2 = sum0 + maj;
    end // t2_logic


  //----------------------------------------------------------------
  // state_logic
  //
  // The logic needed to init as well as update the state during
  // round processing.
  //----------------------------------------------------------------
  always @*
    begin : state_logic
      a_new  = 64'h0;
      b_new  = 64'h0;
      c_new  = 64'h0;
      d_new  = 64'h0;
      e_new  = 64'h0;
      f_new  = 64'h0;
      g_new  = 64'h0;
      h_new  = 64'h0;
      a_h_we = 0;

      if (state_init)
        begin
          if (first_block)
            begin
              a_new  = H0_0;
              b_new  = H0_1;
              c_new  = H0_2;
              d_new  = H0_3;
              e_new  = H0_4;
              f_new  = H0_5;
              g_new  = H0_6;
              h_new  = H0_7;
              a_h_we = 1;
            end
          else if (restore)
            begin
              a_new  = restore_digest[511 : 448];
              b_new  = restore_digest[447 : 384];
              c_new  = restore_digest[383 : 320];
              d_new  = restore_digest[319 : 256];
              e_new  = restore_digest[255 : 192];
              f_new  = restore_digest[191 : 128];
              g_new  = restore_digest[127 :  64];
              h_new  = restore_digest[63  :   0];
              a_h_we = 1;
            end
          else
            begin
              a_new  = H0_reg;
              b_new  = H1_reg;
              c_new  = H2_reg;
              d_new  = H3_reg;
              e_new  = H4_reg;
              f_new  = H5_reg;
              g_new  = H6_reg;
              h_new  = H7_reg;
              a_h_we = 1;
            end
        end

      if (state_update)
        begin
          a_new  = t1 + t2;
          b_new  = a_reg;
          c_new  = b_reg;
          d_new  = c_reg;
          e_new  = d_reg + t1;
          f_new  = e_reg;
          g_new  = f_reg;
          h_new  = g_reg;
          a_h_we = 1;
        end
    end // state_logic


  //----------------------------------------------------------------
  // round_ctr
  //
  // Update logic for the round counter, a monotonically
  // increasing counter with reset.
  //----------------------------------------------------------------
  always @*
    begin : round_ctr
      round_ctr_new = 7'h00;
      round_ctr_we  = 0;

      if (round_ctr_rst)
        begin
          round_ctr_new = 7'h00;
          round_ctr_we  = 1;
        end

      if (round_ctr_inc)
        begin
          round_ctr_new = round_ctr_reg + 1'b1;
          round_ctr_we  = 1;
        end
    end // round_ctr


  //----------------------------------------------------------------
  // sha512_ctrl_fsm
  //
  // Logic for the state machine controlling the core behaviour.
  //----------------------------------------------------------------
  always @*
    begin : sha512_ctrl_fsm
      digest_init         = 1'b0;
      digest_update       = 1'b0;
      state_init          = 1'b0;
      state_update        = 1'b0;
      first_block         = 1'b0;
      w_init              = 1'b0;
      w_next              = 1'b0;
      round_ctr_inc       = 1'b0;
      round_ctr_rst       = 1'b0;
      digest_valid_new    = 1'b0;
      digest_valid_we     = 1'b0;
      ready_new           = 1'b0;
      ready_we            = 1'b0;
      sha512_ctrl_new     = CTRL_IDLE;
      sha512_ctrl_we      = 1'b0;
      restore             = 1'b0;

      unique case (sha512_ctrl_reg)
        CTRL_IDLE:
          begin
            if (init_cmd)
              begin
                ready_new           = 1'b0;
                ready_we            = 1'b1;
                digest_init         = 1;
                w_init              = 1;
                state_init          = 1;
                first_block         = 1;
                round_ctr_rst       = 1;
                digest_valid_new    = 0;
                digest_valid_we     = 1;
                sha512_ctrl_new     = CTRL_ROUNDS;
                sha512_ctrl_we      = 1;
              end

            if (next_cmd)
              begin
                ready_new           = 1'b0;
                ready_we            = 1'b1;
                w_init              = 1;
                state_init          = 1;
                round_ctr_rst       = 1;
                digest_valid_new    = 0;
                digest_valid_we     = 1;
                sha512_ctrl_new     = CTRL_ROUNDS;
                sha512_ctrl_we      = 1;
                restore             = restore_cmd;
              end
          end


        CTRL_ROUNDS:
          begin
            w_next        = 1;
            state_update  = 1;
            round_ctr_inc = 1;

            if (round_ctr_reg == SHA512_ROUNDS)
              begin
                sha512_ctrl_new     = CTRL_DONE;
                sha512_ctrl_we      = 1;
              end
          end


        CTRL_DONE:
          begin
            ready_new        = 1'b1;
            ready_we         = 1'b1;
            digest_update    = 1'b1;
            digest_valid_new = 1'b1;
            digest_valid_we  = 1'b1;
            sha512_ctrl_new  = CTRL_IDLE;
            sha512_ctrl_we   = 1'b1;
          end


        default:
          begin
            digest_init         = 1'b0;
            digest_update       = 1'b0;
            state_init          = 1'b0;
            state_update        = 1'b0;
            first_block         = 1'b0;
            w_init              = 1'b0;
            w_next              = 1'b0;
            round_ctr_inc       = 1'b0;
            round_ctr_rst       = 1'b0;
            digest_valid_new    = 1'b0;
            digest_valid_we     = 1'b0;
            ready_new           = 1'b0;
            ready_we            = 1'b0;
            sha512_ctrl_new     = CTRL_IDLE;
            sha512_ctrl_we      = 1'b0;
          end

      endcase // case (sha512_ctrl_reg)
    end // sha512_ctrl_fsm

endmodule // sha512_core

//======================================================================
// EOF sha512_core.v
//======================================================================
