//======================================================================
//
// sha512_masked_w_mem_regs.v
// -------------------
// The W memory for the SHA-512 core. This version uses 16
// 32-bit registers as a sliding window to generate the 64 words.
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

module sha512_masked_w_mem
                    import sha512_masked_defines_pkg::*;
                    (
                    input wire            clk,
                    input wire            reset_n,
                    input wire            zeroize,

                    input wire [1023 : 0] block_msg,
                    input wire [1023 : 0] rw_masking_rnd,
                    input wire [4 : 0]    entropy,

                    input wire            init_cmd,
                    input wire            next_cmd,
                    output wire masked_reg_t  w_val
                   );


  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  masked_reg_t w_mem [0 : 15];
  masked_reg_t w_mem00_new;
  masked_reg_t w_mem01_new;
  masked_reg_t w_mem02_new;
  masked_reg_t w_mem03_new;
  masked_reg_t w_mem04_new;
  masked_reg_t w_mem05_new;
  masked_reg_t w_mem06_new;
  masked_reg_t w_mem07_new;
  masked_reg_t w_mem08_new;
  masked_reg_t w_mem09_new;
  masked_reg_t w_mem10_new;
  masked_reg_t w_mem11_new;
  masked_reg_t w_mem12_new;
  masked_reg_t w_mem13_new;
  masked_reg_t w_mem14_new;
  masked_reg_t w_mem15_new;
  reg          w_mem_we;

  reg [6 : 0] w_ctr_reg;
  reg [6 : 0] w_ctr_new;
  reg         w_ctr_we;

  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  masked_reg_t w_tmp;
  masked_reg_t w_new;


  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign w_val = w_tmp;


  //----------------------------------------------------------------
  // reg_update
  // Update functionality for all registers in the core.
  // All registers are positive edge triggered with asynchronous
  // active low reset. All registers have write enable.
  //----------------------------------------------------------------
  always @ (posedge clk or negedge reset_n)
    begin : reg_update
      integer ii;

      if (!reset_n) begin
        for (ii = 0; ii < 16; ii = ii + 1)
          w_mem[ii] <= {64'h0, 64'h0};

        w_ctr_reg <= 7'h0;
      end
      else begin
        if (zeroize) begin
          for (ii = 0; ii < 16; ii = ii + 1)
            w_mem[ii] <= {64'h0, 64'h0};

          w_ctr_reg <= 7'h0;
        end
        else begin
          if (w_mem_we)
            begin
              w_mem[00] <= w_mem00_new;
              w_mem[01] <= w_mem01_new;
              w_mem[02] <= w_mem02_new;
              w_mem[03] <= w_mem03_new;
              w_mem[04] <= w_mem04_new;
              w_mem[05] <= w_mem05_new;
              w_mem[06] <= w_mem06_new;
              w_mem[07] <= w_mem07_new;
              w_mem[08] <= w_mem08_new;
              w_mem[09] <= w_mem09_new;
              w_mem[10] <= w_mem10_new;
              w_mem[11] <= w_mem11_new;
              w_mem[12] <= w_mem12_new;
              w_mem[13] <= w_mem13_new;
              w_mem[14] <= w_mem14_new;
              w_mem[15] <= w_mem15_new;
            end

          if (w_ctr_we)
              w_ctr_reg <= w_ctr_new;
        end
      end
    end // reg_update


  //----------------------------------------------------------------
  // select_w
  //
  // Mux for the external read operation. This is where we exract
  // the W variable.
  //----------------------------------------------------------------
  always @*
    begin : select_w
      if (w_ctr_reg < 16)
        w_tmp = w_mem[w_ctr_reg[3 : 0]];
      else
        w_tmp = w_new;
    end // select_w


  //----------------------------------------------------------------
  // w_new_logic
  //
  // Logic that calculates the next value to be inserted into
  // the sliding window of the memory.
  //----------------------------------------------------------------
      masked_reg_t w_0;
      masked_reg_t w_1;
      masked_reg_t w_9;
      masked_reg_t w_14;
      masked_reg_t d0;
      masked_reg_t d1;
      
      masked_reg_t w_0_b2a;
      masked_reg_t w_9_b2a;
      masked_reg_t d0_b2a;
      masked_reg_t d1_b2a;
      
  always @*
    begin : w_mem_update_logic


      w_mem00_new = {64'h0, 64'h0};
      w_mem01_new = {64'h0, 64'h0};
      w_mem02_new = {64'h0, 64'h0};
      w_mem03_new = {64'h0, 64'h0};
      w_mem04_new = {64'h0, 64'h0};
      w_mem05_new = {64'h0, 64'h0};
      w_mem06_new = {64'h0, 64'h0};
      w_mem07_new = {64'h0, 64'h0};
      w_mem08_new = {64'h0, 64'h0};
      w_mem09_new = {64'h0, 64'h0};
      w_mem10_new = {64'h0, 64'h0};
      w_mem11_new = {64'h0, 64'h0};
      w_mem12_new = {64'h0, 64'h0};
      w_mem13_new = {64'h0, 64'h0};
      w_mem14_new = {64'h0, 64'h0};
      w_mem15_new = {64'h0, 64'h0};
      w_mem_we    = 0;

      w_0  = w_mem[0];
      w_1  = w_mem[1];
      w_9  = w_mem[9];
      w_14 = w_mem[14];

      d0 = {ROT1(w_1.masked), ROT1(w_1.random)};

      d1 = {ROT14(w_14.masked), ROT14(w_14.random)};

      w_0_b2a = B2A_conv(w_0, entropy[0]);
      d0_b2a  = B2A_conv(d0,  entropy[1]);
      w_9_b2a = B2A_conv(w_9, entropy[2]);
      d1_b2a  = B2A_conv(d1,  entropy[3]);

      //w_new = w_0 + d0 + w_9 + d1;
      w_new = A2B_conv(masked_sum(w_0_b2a, masked_sum(d0_b2a, masked_sum(w_9_b2a, d1_b2a))), entropy[4]);

      if (init_cmd)
        begin
          w_mem00_new = {block_msg[1023 : 960] ^ rw_masking_rnd[1023 : 960], rw_masking_rnd[1023 : 960]};
          w_mem01_new = {block_msg[959  : 896] ^ rw_masking_rnd[959  : 896], rw_masking_rnd[959  : 896]};
          w_mem02_new = {block_msg[895  : 832] ^ rw_masking_rnd[895  : 832], rw_masking_rnd[895  : 832]};
          w_mem03_new = {block_msg[831  : 768] ^ rw_masking_rnd[831  : 768], rw_masking_rnd[831  : 768]};
          w_mem04_new = {block_msg[767  : 704] ^ rw_masking_rnd[767  : 704], rw_masking_rnd[767  : 704]};
          w_mem05_new = {block_msg[703  : 640] ^ rw_masking_rnd[703  : 640], rw_masking_rnd[703  : 640]};
          w_mem06_new = {block_msg[639  : 576] ^ rw_masking_rnd[639  : 576], rw_masking_rnd[639  : 576]};
          w_mem07_new = {block_msg[575  : 512] ^ rw_masking_rnd[575  : 512], rw_masking_rnd[575  : 512]};
          w_mem08_new = {block_msg[511  : 448] ^ rw_masking_rnd[511  : 448], rw_masking_rnd[511  : 448]};
          w_mem09_new = {block_msg[447  : 384] ^ rw_masking_rnd[447  : 384], rw_masking_rnd[447  : 384]};
          w_mem10_new = {block_msg[383  : 320] ^ rw_masking_rnd[383  : 320], rw_masking_rnd[383  : 320]};
          w_mem11_new = {block_msg[319  : 256] ^ rw_masking_rnd[319  : 256], rw_masking_rnd[319  : 256]};
          w_mem12_new = {block_msg[255  : 192] ^ rw_masking_rnd[255  : 192], rw_masking_rnd[255  : 192]};
          w_mem13_new = {block_msg[191  : 128] ^ rw_masking_rnd[191  : 128], rw_masking_rnd[191  : 128]};
          w_mem14_new = {block_msg[127  :  64] ^ rw_masking_rnd[127  :  64], rw_masking_rnd[127  :  64]};
          w_mem15_new = {block_msg[63   :   0] ^ rw_masking_rnd[63   :   0], rw_masking_rnd[63   :   0]};
          w_mem_we    = 1;
        end

      if (next_cmd && (w_ctr_reg > 15))
        begin
          w_mem00_new = w_mem[01];
          w_mem01_new = w_mem[02];
          w_mem02_new = w_mem[03];
          w_mem03_new = w_mem[04];
          w_mem04_new = w_mem[05];
          w_mem05_new = w_mem[06];
          w_mem06_new = w_mem[07];
          w_mem07_new = w_mem[08];
          w_mem08_new = w_mem[09];
          w_mem09_new = w_mem[10];
          w_mem10_new = w_mem[11];
          w_mem11_new = w_mem[12];
          w_mem12_new = w_mem[13];
          w_mem13_new = w_mem[14];
          w_mem14_new = w_mem[15];
          w_mem15_new = w_new;
          w_mem_we    = 1;
        end
    end // w_mem_update_logic


  //----------------------------------------------------------------
  // w_ctr
  // W schedule adress counter. Counts from 0x10 to 0x3f and
  // is used to expand the block into words.
  //----------------------------------------------------------------
  always @*
    begin : w_ctr
      w_ctr_new = 7'h0;
      w_ctr_we  = 1'h0;

      if (init_cmd)
        begin
          w_ctr_new = 7'h00;
          w_ctr_we  = 1'h1;
        end

      if (next_cmd)
        begin
          w_ctr_new = w_ctr_reg + 7'h01;
          w_ctr_we  = 1'h1;
        end
    end // w_ctr

endmodule // sha512_w_mem

//======================================================================
// EOF sha512_masked_w_mem.v
//======================================================================