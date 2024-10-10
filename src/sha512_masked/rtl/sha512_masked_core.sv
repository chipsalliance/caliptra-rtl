//======================================================================
//
// sha512_masked_core.sv
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
//
//  Module:
//      sha512_masked_core.sv
//
// The embedded countermeasures for SHA512 is based on
// "Differential Power Analysis of HMAC Based on SHA-2, and Countermeasures"
// by McEvoy et. al.
//
// The countermeasures are added into the unmasked SHA512 implementation  
// from Secworks. 
// 
// For providing the required random values to mask intermediate values,
// we use a lightweight LFSR. Based on 
// "Spin Me Right Round Rotational Symmetry for FPGA-specific AES" by
// Wegener et. al., LFSR is sufficient for masking statistical randomness.
//======================================================================


module sha512_masked_core
                  import sha512_masked_defines_pkg::*;
                  (
                   // Clock and reset.
                   input wire            clk,
                   input wire            reset_n,
                   input wire            zeroize,
                   // Control.
                   input wire            init_cmd,
                   input wire            next_cmd,
                   input wire [1 : 0]    mode,
                   
                   // Data port.
                   input wire [191 : 0]  entropy,
                   

                   input wire [1023 : 0] block_msg,

                   output wire           ready,
                   output wire [511 : 0] digest,
                   output wire           digest_valid
                  );


  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam SHA512_ROUNDS = 79;
  localparam SHA512_RNDs   = 8;

  localparam CTRL_IDLE   = 2'h0;
  localparam CTRL_RND    = 2'h1;
  localparam CTRL_ROUNDS = 2'h2;
  localparam CTRL_DONE   = 2'h3;


  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  logic               masking_init;
  logic               masking_update;
  logic [23:0][63:0]  masking_rnd;
  logic [7:0][63:0]   rh_masking_rnd;
  logic [1023:0]      rw_masking_rnd;
  logic [9:0]         q_masking_rnd;

  logic init_reg_set;
  logic init_reg_reset;
  logic init_reg;

  masked_reg_t a_reg;
  masked_reg_t a_new;
  masked_reg_t b_reg;
  masked_reg_t b_new;
  masked_reg_t c_reg;
  masked_reg_t c_new;
  masked_reg_t d_reg;
  masked_reg_t d_new;
  masked_reg_t e_reg;
  masked_reg_t e_new;
  masked_reg_t f_reg;
  masked_reg_t f_new;
  masked_reg_t g_reg;
  masked_reg_t g_new;
  masked_reg_t h_reg;
  masked_reg_t h_new;
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

  reg [6 : 0]  rnd_ctr_reg;
  reg [6 : 0]  rnd_ctr_new;
  reg          rnd_ctr_we;
  reg          rnd_ctr_inc;
  reg          rnd_ctr_rst;
  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  reg digest_init;
  reg digest_update;

  reg state_init;
  reg state_update;

  reg first_block;

  masked_reg_t t1_b2a;
  masked_reg_t t2_b2a;
  masked_reg_t a_new_a2b;
  masked_reg_t e_new_a2b;

  wire [63 : 0] k_data;

  reg           w_init;
  reg           w_next;
  masked_reg_t  w_data;

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


  sha512_masked_w_mem w_mem_inst(
      .clk(clk),
      .reset_n(reset_n),
      .zeroize(zeroize),

      .block_msg(block_msg),
      .rw_masking_rnd(rw_masking_rnd),
      .entropy(entropy[4 : 0]),      

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

  genvar i;
  generate 
      for (i=0; i < 8; i++) begin : rh_masking_assign
          assign rh_masking_rnd[i] = masking_rnd[i];
      end
  endgenerate                           

  assign rw_masking_rnd = {masking_rnd[08], masking_rnd[09], masking_rnd[10], masking_rnd[11],
                           masking_rnd[12], masking_rnd[13], masking_rnd[14], masking_rnd[15],
                           masking_rnd[16], masking_rnd[17], masking_rnd[18], masking_rnd[19],
                           masking_rnd[20], masking_rnd[21], masking_rnd[22], masking_rnd[23]};
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
          a_reg               <= {64'h0, 64'h0};
          b_reg               <= {64'h0, 64'h0};
          c_reg               <= {64'h0, 64'h0};
          d_reg               <= {64'h0, 64'h0};
          e_reg               <= {64'h0, 64'h0};
          f_reg               <= {64'h0, 64'h0};
          g_reg               <= {64'h0, 64'h0};
          h_reg               <= {64'h0, 64'h0};
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
          rnd_ctr_reg         <= 7'h0;
          sha512_ctrl_reg     <= CTRL_IDLE;
          masking_rnd         <= '0;
        end

      else if (zeroize) 
        begin
          a_reg               <= {64'h0, 64'h0};
          b_reg               <= {64'h0, 64'h0};
          c_reg               <= {64'h0, 64'h0};
          d_reg               <= {64'h0, 64'h0};
          e_reg               <= {64'h0, 64'h0};
          f_reg               <= {64'h0, 64'h0};
          g_reg               <= {64'h0, 64'h0};
          h_reg               <= {64'h0, 64'h0};
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
          rnd_ctr_reg         <= 7'h0;
          sha512_ctrl_reg     <= CTRL_IDLE;
          masking_rnd         <= '0;
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
          
          if (rnd_ctr_we)
            rnd_ctr_reg <= rnd_ctr_new;

          if (ready_we)
            ready_reg <= ready_new;

          if (digest_valid_we)
            digest_valid_reg <= digest_valid_new;

          if (sha512_ctrl_we)
            sha512_ctrl_reg <= sha512_ctrl_new;
          
          if (masking_init) begin
            masking_rnd[3*rnd_ctr_reg[2 : 0]]   <= entropy[63  :   0];
            masking_rnd[3*rnd_ctr_reg[2 : 0]+1] <= entropy[127 :  64];
            masking_rnd[3*rnd_ctr_reg[2 : 0]+2] <= entropy[191 : 128];
          end
        end
    end // reg_update

    always @ (posedge clk or negedge reset_n)
      begin : init_reg_update
        if (!reset_n)
          init_reg        <= '0;
        else if (zeroize)
          init_reg        <= '0;
        else if (init_reg_set)
          init_reg        <= 1'b1;
        else if (init_reg_reset)
          init_reg        <= 1'b0;
      end // init_reg_update

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

      if (digest_update)
        begin
          H0_new = H0_reg + (a_reg.masked ^ a_reg.random);
          H1_new = H1_reg + (b_reg.masked ^ b_reg.random);
          H2_new = H2_reg + (c_reg.masked ^ c_reg.random);
          H3_new = H3_reg + (d_reg.masked ^ d_reg.random);
          H4_new = H4_reg + (e_reg.masked ^ e_reg.random);
          H5_new = H5_reg + (f_reg.masked ^ f_reg.random);
          H6_new = H6_reg + (g_reg.masked ^ g_reg.random);
          H7_new = H7_reg + (h_reg.masked ^ h_reg.random);
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
      masked_reg_t sum1;
      masked_reg_t ch;

      masked_reg_t k_data_s;

      masked_reg_t h_reg_b2a;
      masked_reg_t sum1_b2a;
      masked_reg_t ch_b2a;
      masked_reg_t k_data_b2a;
      masked_reg_t w_data_b2a;

      sum1 = {sigma1(e_reg.masked), sigma1(e_reg.random)};

      ch = masked_ch(e_reg, f_reg, g_reg); // (e_reg & f_reg) ^ ((~e_reg) & g_reg);
      
      k_data_s = {k_data, 64'h0};
      h_reg_b2a  = B2A_conv(h_reg,    q_masking_rnd[0]);
      sum1_b2a   = B2A_conv(sum1,     q_masking_rnd[1]);
      ch_b2a     = B2A_conv(ch,       q_masking_rnd[2]);
      k_data_b2a = B2A_conv(k_data_s, q_masking_rnd[3]);
      w_data_b2a = B2A_conv(w_data,   q_masking_rnd[4]);

      t1_b2a = masked_sum(h_reg_b2a, masked_sum(sum1_b2a, masked_sum(ch_b2a, masked_sum(k_data_b2a, w_data_b2a))));
    end // t1_logic


  //----------------------------------------------------------------
  // t2_logic
  //
  // The logic for the T2 function
  //----------------------------------------------------------------
  always @*
    begin : t2_logic
      masked_reg_t sum0;
      masked_reg_t maj;

      masked_reg_t sum0_b2a;
      masked_reg_t maj_b2a;

      sum0 = {sigma0(a_reg.masked), sigma0(a_reg.random)};

      maj = masked_maj(a_reg, b_reg, c_reg); // (a_reg & b_reg) ^ (a_reg & c_reg) ^ (b_reg & c_reg);

      sum0_b2a  = B2A_conv(sum0,  q_masking_rnd[5]);
      maj_b2a   = B2A_conv(maj,   q_masking_rnd[6]);

      t2_b2a = masked_sum(sum0_b2a, maj_b2a);
    end // t2_logic

  //----------------------------------------------------------------
  // A2B_logic
  //
  // The logic for the A2B function
  //----------------------------------------------------------------
  always @*
    begin : A2B_logic
      masked_reg_t d_reg_b2a;

      d_reg_b2a = B2A_conv(d_reg, q_masking_rnd[7]);

      a_new_a2b = A2B_conv(masked_sum(t1_b2a, t2_b2a),    q_masking_rnd[8]);
      e_new_a2b = A2B_conv(masked_sum(d_reg_b2a, t1_b2a), q_masking_rnd[9]);

    end // A2B_logic

  //----------------------------------------------------------------
  // state_logic
  //
  // The logic needed to init as well as update the state during
  // round processing.
  //----------------------------------------------------------------
  always @*
    begin : state_logic
      a_new  = {64'h0, 64'h0};
      b_new  = {64'h0, 64'h0};
      c_new  = {64'h0, 64'h0};
      d_new  = {64'h0, 64'h0};
      e_new  = {64'h0, 64'h0};
      f_new  = {64'h0, 64'h0};
      g_new  = {64'h0, 64'h0};
      h_new  = {64'h0, 64'h0};
      a_h_we = 0;

      if (state_init)
        begin
          if (first_block)
            begin
              a_new  = {H0_0 ^ rh_masking_rnd[0], rh_masking_rnd[0]};
              b_new  = {H0_1 ^ rh_masking_rnd[1], rh_masking_rnd[1]};
              c_new  = {H0_2 ^ rh_masking_rnd[2], rh_masking_rnd[2]};
              d_new  = {H0_3 ^ rh_masking_rnd[3], rh_masking_rnd[3]};
              e_new  = {H0_4 ^ rh_masking_rnd[4], rh_masking_rnd[4]};
              f_new  = {H0_5 ^ rh_masking_rnd[5], rh_masking_rnd[5]};
              g_new  = {H0_6 ^ rh_masking_rnd[6], rh_masking_rnd[6]};
              h_new  = {H0_7 ^ rh_masking_rnd[7], rh_masking_rnd[7]};
              a_h_we = 1;
            end
          else
            begin
              a_new  = {H0_reg ^ rh_masking_rnd[0], rh_masking_rnd[0]};
              b_new  = {H1_reg ^ rh_masking_rnd[1], rh_masking_rnd[1]};
              c_new  = {H2_reg ^ rh_masking_rnd[2], rh_masking_rnd[2]};
              d_new  = {H3_reg ^ rh_masking_rnd[3], rh_masking_rnd[3]};
              e_new  = {H4_reg ^ rh_masking_rnd[4], rh_masking_rnd[4]};
              f_new  = {H5_reg ^ rh_masking_rnd[5], rh_masking_rnd[5]};
              g_new  = {H6_reg ^ rh_masking_rnd[6], rh_masking_rnd[6]};
              h_new  = {H7_reg ^ rh_masking_rnd[7], rh_masking_rnd[7]};
              a_h_we = 1;
            end
        end

      if (state_update)
        begin
          a_new  = a_new_a2b;
          b_new  = a_reg;
          c_new  = b_reg;
          d_new  = c_reg;
          e_new  = e_new_a2b;
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
      round_ctr_new = '0;
      round_ctr_we  = 0;

      if (round_ctr_rst)
        begin
          round_ctr_new = '0;
          round_ctr_we  = 1;
        end

      if (round_ctr_inc)
        begin
          round_ctr_new = round_ctr_reg + 1'b1;
          round_ctr_we  = 1;
        end
    end // round_ctr

  //----------------------------------------------------------------
  // rnd_ctr
  //
  // Update logic for the rnd counter, a monotonically
  // increasing counter with reset.
  //----------------------------------------------------------------
  always @*
    begin : rnd_ctr
      rnd_ctr_new = '0;
      rnd_ctr_we  = 0;

      if (rnd_ctr_rst)
        begin
          rnd_ctr_new = '0;
          rnd_ctr_we  = 1;
        end

      if (rnd_ctr_inc)
        begin
          rnd_ctr_new = rnd_ctr_reg + 1'b1;
          rnd_ctr_we  = 1;
        end
    end // rnd_ctr

  //----------------------------------------------------------------
  // masking_rnd
  //
  // Update logic for the rw_masking_rnd and q_masking_rnd
  //----------------------------------------------------------------
  always @*
    begin : masking_random
      masking_init        = rnd_ctr_inc;
      masking_update      = round_ctr_inc;
      q_masking_rnd       = '0;

      if (masking_update) begin
        q_masking_rnd  = entropy[14 : 5];
      end
    end // masking_rnd

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
      rnd_ctr_inc         = 1'b0;
      rnd_ctr_rst         = 1'b0;
      init_reg_set        = 1'b0;
      init_reg_reset      = 1'b0;

      unique case (sha512_ctrl_reg)
        CTRL_IDLE:
          begin
            if (init_cmd | next_cmd)
              begin
                ready_new           = 1'b0;
                ready_we            = 1'b1;
                digest_valid_new    = 0;
                digest_valid_we     = 1;
                rnd_ctr_rst         = 1'b1;
                sha512_ctrl_new     = CTRL_RND;
                sha512_ctrl_we      = 1;
                init_reg_set        = init_cmd;
              end
          end

        CTRL_RND:
          begin
            rnd_ctr_inc             = 1;

            if (rnd_ctr_reg == SHA512_RNDs)
              begin
                w_init              = 1;
                state_init          = 1;
                round_ctr_rst       = 1;
                sha512_ctrl_new     = CTRL_ROUNDS;
                sha512_ctrl_we      = 1;
                init_reg_reset      = 1;

                if (init_reg)
                  begin
                    digest_init         = 1;
                    first_block         = 1;
                  end
              end
          end

        CTRL_ROUNDS:
          begin
            w_next              = 1;
            state_update        = 1;
            round_ctr_inc       = 1;

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
            rnd_ctr_inc         = 1'b0;
            rnd_ctr_rst         = 1'b0;
          end

      endcase // case (sha512_ctrl_reg)
    end // sha512_ctrl_fsm

endmodule // sha512_core

//======================================================================
// EOF sha512_core.v
//======================================================================
