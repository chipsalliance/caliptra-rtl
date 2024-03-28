// -------------------------------------------------
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------
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


import SHA512_masked_pkg::*;


module fv_sha512_masked_core_m(
  input logic rst,
  input logic clk,

  // Ports
  input logic SHA_Input_sync,
  input logic SHA_Input_notify,
  input st_SHA_Args SHA_Input,

  input logic out_notify,
  input logic unsigned [511:0] out,

  // Registers
  input a_sc_big_unsigned_64_8 H,
  input logic signed [31:0] SHA_Mode_in,
  input st_SHA_Args SHA_in,
  input a_st_masked_reg_t_16 W,
  input st_masked_reg_t a,
  input st_masked_reg_t b,
  input logic unsigned [1023:0] block_in,
  input st_masked_reg_t c,
  input st_masked_reg_t d,
  input st_masked_reg_t e,
  input st_masked_reg_t f,
  input st_masked_reg_t g,
  input st_masked_reg_t h,
  input logic signed [31:0] i,
  input logic init_cmd,
  input a_sc_big_unsigned_64_24 masking_rnd,
  input logic signed [31:0] p,

  // States
  input logic IDLE,
  input logic CTRL_RND,
  input logic SHA_Rounds,
  input logic DONE
);


default clocking default_clk @(posedge clk); endclocking


a_sc_big_unsigned_64_8 H_0_i = '{
  0: 64'd0,
  1: 64'd0,
  2: 64'd0,
  3: 64'd0,
  4: 64'd0,
  5: 64'd0,
  6: 64'd0,
  7: 64'd0
};

st_SHA_Args SHA_in_0_i = '{
  in: 1024'd0,
  entropy: 192'd0,
  SHA_Mode: 'sd0,
  init_cmd: 0,
  next_cmd: 0,
  zeroize: 0
};

a_st_masked_reg_t_16 W_0_i = '{
  0: '{ masked: 64'd0, random: 64'd0 },
  1: '{ masked: 64'd0, random: 64'd0 },
  2: '{ masked: 64'd0, random: 64'd0 },
  3: '{ masked: 64'd0, random: 64'd0 },
  4: '{ masked: 64'd0, random: 64'd0 },
  5: '{ masked: 64'd0, random: 64'd0 },
  6: '{ masked: 64'd0, random: 64'd0 },
  7: '{ masked: 64'd0, random: 64'd0 },
  8: '{ masked: 64'd0, random: 64'd0 },
  9: '{ masked: 64'd0, random: 64'd0 },
  10: '{ masked: 64'd0, random: 64'd0 },
  11: '{ masked: 64'd0, random: 64'd0 },
  12: '{ masked: 64'd0, random: 64'd0 },
  13: '{ masked: 64'd0, random: 64'd0 },
  14: '{ masked: 64'd0, random: 64'd0 },
  15: '{ masked: 64'd0, random: 64'd0 }
};

st_masked_reg_t a_0_i = '{
  masked: 64'd0,
  random: 64'd0
};

a_sc_big_unsigned_64_24 masking_rnd_0_i = '{
  0: 64'd0,
  1: 64'd0,
  2: 64'd0,
  3: 64'd0,
  4: 64'd0,
  5: 64'd0,
  6: 64'd0,
  7: 64'd0,
  8: 64'd0,
  9: 64'd0,
  10: 64'd0,
  11: 64'd0,
  12: 64'd0,
  13: 64'd0,
  14: 64'd0,
  15: 64'd0,
  16: 64'd0,
  17: 64'd0,
  18: 64'd0,
  19: 64'd0,
  20: 64'd0,
  21: 64'd0,
  22: 64'd0,
  23: 64'd0
};

a_sc_big_unsigned_64_24 masking_rnd_1_i = '{
  0: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd0) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd0) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd0) ? 64'(SHA_in.entropy) : masking_rnd['sd0]))),
  1: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd1) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd1) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd1) ? 64'(SHA_in.entropy) : masking_rnd['sd1]))),
  2: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd2) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd2) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd2) ? 64'(SHA_in.entropy) : masking_rnd['sd2]))),
  3: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd3) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd3) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd3) ? 64'(SHA_in.entropy) : masking_rnd['sd3]))),
  4: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd4) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd4) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd4) ? 64'(SHA_in.entropy) : masking_rnd['sd4]))),
  5: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd5) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd5) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd5) ? 64'(SHA_in.entropy) : masking_rnd['sd5]))),
  6: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd6) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd6) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd6) ? 64'(SHA_in.entropy) : masking_rnd['sd6]))),
  7: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd7) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd7) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd7) ? 64'(SHA_in.entropy) : masking_rnd['sd7]))),
  8: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd8) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd8) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd8) ? 64'(SHA_in.entropy) : masking_rnd['sd8]))),
  9: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd9) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd9) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd9) ? 64'(SHA_in.entropy) : masking_rnd['sd9]))),
  10: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd10) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd10) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd10) ? 64'(SHA_in.entropy) : masking_rnd['sd10]))),
  11: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd11) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd11) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd11) ? 64'(SHA_in.entropy) : masking_rnd['sd11]))),
  12: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd12) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd12) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd12) ? 64'(SHA_in.entropy) : masking_rnd['sd12]))),
  13: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd13) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd13) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd13) ? 64'(SHA_in.entropy) : masking_rnd['sd13]))),
  14: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd14) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd14) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd14) ? 64'(SHA_in.entropy) : masking_rnd['sd14]))),
  15: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd15) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd15) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd15) ? 64'(SHA_in.entropy) : masking_rnd['sd15]))),
  16: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd16) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd16) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd16) ? 64'(SHA_in.entropy) : masking_rnd['sd16]))),
  17: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd17) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd17) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd17) ? 64'(SHA_in.entropy) : masking_rnd['sd17]))),
  18: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd18) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd18) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd18) ? 64'(SHA_in.entropy) : masking_rnd['sd18]))),
  19: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd19) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd19) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd19) ? 64'(SHA_in.entropy) : masking_rnd['sd19]))),
  20: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd20) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd20) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd20) ? 64'(SHA_in.entropy) : masking_rnd['sd20]))),
  21: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd21) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd21) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd21) ? 64'(SHA_in.entropy) : masking_rnd['sd21]))),
  22: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd22) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd22) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd22) ? 64'(SHA_in.entropy) : masking_rnd['sd22]))),
  23: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd23) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd23) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd23) ? 64'(SHA_in.entropy) : masking_rnd['sd23])))
};

logic unsigned [63:0] slicer_0_i = slicer(block_in, 'sd0);

logic unsigned [63:0] slicer_1_i = slicer(block_in, 'sd1);

logic unsigned [63:0] slicer_2_i = slicer(block_in, 'sd2);

logic unsigned [63:0] slicer_3_i = slicer(block_in, 'sd3);

logic unsigned [63:0] slicer_4_i = slicer(block_in, 'sd4);

logic unsigned [63:0] slicer_5_i = slicer(block_in, 'sd5);

logic unsigned [63:0] slicer_6_i = slicer(block_in, 'sd6);

logic unsigned [63:0] slicer_7_i = slicer(block_in, 'sd7);

logic unsigned [63:0] slicer_8_i = slicer(block_in, 'sd8);

logic unsigned [63:0] slicer_9_i = slicer(block_in, 'sd9);

logic unsigned [63:0] slicer_10_i = slicer(block_in, 'sd10);

logic unsigned [63:0] slicer_11_i = slicer(block_in, 'sd11);

logic unsigned [63:0] slicer_12_i = slicer(block_in, 'sd12);

logic unsigned [63:0] slicer_13_i = slicer(block_in, 'sd13);

logic unsigned [63:0] slicer_14_i = slicer(block_in, 'sd14);

logic unsigned [63:0] slicer_15_i = slicer(block_in, 'sd15);

a_sc_big_unsigned_64_8 H_1_i = '{
  0: 64'h8C3D37C819544DA2,
  1: 64'h73E1996689DCD4D6,
  2: 64'h1DFAB7AE32FF9C82,
  3: 64'h679DD514582F9FCF,
  4: 64'hF6D2B697BD44DA8,
  5: 64'h77E36F7304C48942,
  6: 64'h3F9D85A86A1D36C8,
  7: 64'h1112E6AD91D692A1
};

a_st_masked_reg_t_16 W_1_i = '{
  0: '{ masked: (slicer_15_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd8) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd8) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd8) ? 64'(SHA_in.entropy) : masking_rnd['sd8])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd8) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd8) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd8) ? 64'(SHA_in.entropy) : masking_rnd['sd8]))) },
  1: '{ masked: (slicer_14_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd9) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd9) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd9) ? 64'(SHA_in.entropy) : masking_rnd['sd9])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd9) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd9) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd9) ? 64'(SHA_in.entropy) : masking_rnd['sd9]))) },
  2: '{ masked: (slicer_13_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd10) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd10) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd10) ? 64'(SHA_in.entropy) : masking_rnd['sd10])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd10) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd10) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd10) ? 64'(SHA_in.entropy) : masking_rnd['sd10]))) },
  3: '{ masked: (slicer_12_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd11) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd11) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd11) ? 64'(SHA_in.entropy) : masking_rnd['sd11])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd11) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd11) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd11) ? 64'(SHA_in.entropy) : masking_rnd['sd11]))) },
  4: '{ masked: (slicer_11_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd12) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd12) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd12) ? 64'(SHA_in.entropy) : masking_rnd['sd12])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd12) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd12) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd12) ? 64'(SHA_in.entropy) : masking_rnd['sd12]))) },
  5: '{ masked: (slicer_10_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd13) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd13) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd13) ? 64'(SHA_in.entropy) : masking_rnd['sd13])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd13) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd13) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd13) ? 64'(SHA_in.entropy) : masking_rnd['sd13]))) },
  6: '{ masked: (slicer_9_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd14) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd14) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd14) ? 64'(SHA_in.entropy) : masking_rnd['sd14])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd14) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd14) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd14) ? 64'(SHA_in.entropy) : masking_rnd['sd14]))) },
  7: '{ masked: (slicer_8_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd15) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd15) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd15) ? 64'(SHA_in.entropy) : masking_rnd['sd15])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd15) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd15) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd15) ? 64'(SHA_in.entropy) : masking_rnd['sd15]))) },
  8: '{ masked: (slicer_7_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd16) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd16) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd16) ? 64'(SHA_in.entropy) : masking_rnd['sd16])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd16) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd16) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd16) ? 64'(SHA_in.entropy) : masking_rnd['sd16]))) },
  9: '{ masked: (slicer_6_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd17) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd17) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd17) ? 64'(SHA_in.entropy) : masking_rnd['sd17])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd17) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd17) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd17) ? 64'(SHA_in.entropy) : masking_rnd['sd17]))) },
  10: '{ masked: (slicer_5_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd18) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd18) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd18) ? 64'(SHA_in.entropy) : masking_rnd['sd18])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd18) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd18) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd18) ? 64'(SHA_in.entropy) : masking_rnd['sd18]))) },
  11: '{ masked: (slicer_4_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd19) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd19) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd19) ? 64'(SHA_in.entropy) : masking_rnd['sd19])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd19) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd19) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd19) ? 64'(SHA_in.entropy) : masking_rnd['sd19]))) },
  12: '{ masked: (slicer_3_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd20) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd20) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd20) ? 64'(SHA_in.entropy) : masking_rnd['sd20])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd20) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd20) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd20) ? 64'(SHA_in.entropy) : masking_rnd['sd20]))) },
  13: '{ masked: (slicer_2_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd21) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd21) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd21) ? 64'(SHA_in.entropy) : masking_rnd['sd21])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd21) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd21) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd21) ? 64'(SHA_in.entropy) : masking_rnd['sd21]))) },
  14: '{ masked: (slicer_1_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd22) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd22) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd22) ? 64'(SHA_in.entropy) : masking_rnd['sd22])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd22) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd22) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd22) ? 64'(SHA_in.entropy) : masking_rnd['sd22]))) },
  15: '{ masked: (slicer_0_i ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd23) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd23) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd23) ? 64'(SHA_in.entropy) : masking_rnd['sd23])))), random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd23) ? 64'((SHA_in.entropy >> 192'd128)) : (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd23) ? 64'((SHA_in.entropy >> 192'd64)) : ((('sd3 * (p & 'sh7)) == 'sd23) ? 64'(SHA_in.entropy) : masking_rnd['sd23]))) }
};

st_masked_reg_t a_1_i = '{
  masked: (64'h8C3D37C819544DA2 ^ ((('sd3 * (p & 'sh7)) == 'sd0) ? 64'(SHA_in.entropy) : masking_rnd['sd0])),
  random: ((('sd3 * (p & 'sh7)) == 'sd0) ? 64'(SHA_in.entropy) : masking_rnd['sd0])
};

st_masked_reg_t b_0_i = '{
  masked: (64'h73E1996689DCD4D6 ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd1) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd1])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd1) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd1])
};

st_masked_reg_t c_0_i = '{
  masked: (64'h1DFAB7AE32FF9C82 ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd2) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd2])),
  random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd2) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd2])
};

st_masked_reg_t d_0_i = '{
  masked: (64'h679DD514582F9FCF ^ ((('sd3 * (p & 'sh7)) == 'sd3) ? 64'(SHA_in.entropy) : masking_rnd['sd3])),
  random: ((('sd3 * (p & 'sh7)) == 'sd3) ? 64'(SHA_in.entropy) : masking_rnd['sd3])
};

st_masked_reg_t e_0_i = '{
  masked: (64'hF6D2B697BD44DA8 ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd4) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd4])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd4) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd4])
};

st_masked_reg_t f_0_i = '{
  masked: (64'h77E36F7304C48942 ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd5) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd5])),
  random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd5) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd5])
};

st_masked_reg_t g_0_i = '{
  masked: (64'h3F9D85A86A1D36C8 ^ ((('sd3 * (p & 'sh7)) == 'sd6) ? 64'(SHA_in.entropy) : masking_rnd['sd6])),
  random: ((('sd3 * (p & 'sh7)) == 'sd6) ? 64'(SHA_in.entropy) : masking_rnd['sd6])
};

st_masked_reg_t h_0_i = '{
  masked: (64'h1112E6AD91D692A1 ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd7) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd7])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd7) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd7])
};

a_sc_big_unsigned_64_8 H_2_i = '{
  0: 64'h22312194FC2BF72C,
  1: 64'h9F555FA3C84C64C2,
  2: 64'h2393B86B6F53B151,
  3: 64'h963877195940EABD,
  4: 64'h96283EE2A88EFFE3,
  5: 64'hBE5E1E2553863992,
  6: 64'h2B0199FC2C85B8AA,
  7: 64'hEB72DDC81C52CA2
};

st_masked_reg_t a_2_i = '{
  masked: (64'h22312194FC2BF72C ^ ((('sd3 * (p & 'sh7)) == 'sd0) ? 64'(SHA_in.entropy) : masking_rnd['sd0])),
  random: ((('sd3 * (p & 'sh7)) == 'sd0) ? 64'(SHA_in.entropy) : masking_rnd['sd0])
};

st_masked_reg_t b_1_i = '{
  masked: (64'h9F555FA3C84C64C2 ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd1) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd1])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd1) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd1])
};

st_masked_reg_t c_1_i = '{
  masked: (64'h2393B86B6F53B151 ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd2) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd2])),
  random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd2) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd2])
};

st_masked_reg_t d_1_i = '{
  masked: (64'h963877195940EABD ^ ((('sd3 * (p & 'sh7)) == 'sd3) ? 64'(SHA_in.entropy) : masking_rnd['sd3])),
  random: ((('sd3 * (p & 'sh7)) == 'sd3) ? 64'(SHA_in.entropy) : masking_rnd['sd3])
};

st_masked_reg_t e_1_i = '{
  masked: (64'h96283EE2A88EFFE3 ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd4) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd4])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd4) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd4])
};

st_masked_reg_t f_1_i = '{
  masked: (64'hBE5E1E2553863992 ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd5) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd5])),
  random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd5) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd5])
};

st_masked_reg_t g_1_i = '{
  masked: (64'h2B0199FC2C85B8AA ^ ((('sd3 * (p & 'sh7)) == 'sd6) ? 64'(SHA_in.entropy) : masking_rnd['sd6])),
  random: ((('sd3 * (p & 'sh7)) == 'sd6) ? 64'(SHA_in.entropy) : masking_rnd['sd6])
};

st_masked_reg_t h_1_i = '{
  masked: (64'hEB72DDC81C52CA2 ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd7) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd7])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd7) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd7])
};

a_sc_big_unsigned_64_8 H_3_i = '{
  0: 64'h6A09E667F3BCC908,
  1: 64'hBB67AE8584CAA73B,
  2: 64'h3C6EF372FE94F82B,
  3: 64'hA54FF53A5F1D36F1,
  4: 64'h510E527FADE682D1,
  5: 64'h9B05688C2B3E6C1F,
  6: 64'h1F83D9ABFB41BD6B,
  7: 64'h5BE0CD19137E2179
};

st_masked_reg_t a_3_i = '{
  masked: (64'h6A09E667F3BCC908 ^ ((('sd3 * (p & 'sh7)) == 'sd0) ? 64'(SHA_in.entropy) : masking_rnd['sd0])),
  random: ((('sd3 * (p & 'sh7)) == 'sd0) ? 64'(SHA_in.entropy) : masking_rnd['sd0])
};

st_masked_reg_t b_2_i = '{
  masked: (64'hBB67AE8584CAA73B ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd1) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd1])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd1) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd1])
};

st_masked_reg_t c_2_i = '{
  masked: (64'h3C6EF372FE94F82B ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd2) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd2])),
  random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd2) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd2])
};

st_masked_reg_t d_2_i = '{
  masked: (64'hA54FF53A5F1D36F1 ^ ((('sd3 * (p & 'sh7)) == 'sd3) ? 64'(SHA_in.entropy) : masking_rnd['sd3])),
  random: ((('sd3 * (p & 'sh7)) == 'sd3) ? 64'(SHA_in.entropy) : masking_rnd['sd3])
};

st_masked_reg_t e_2_i = '{
  masked: (64'h510E527FADE682D1 ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd4) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd4])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd4) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd4])
};

st_masked_reg_t f_2_i = '{
  masked: (64'h9B05688C2B3E6C1F ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd5) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd5])),
  random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd5) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd5])
};

st_masked_reg_t g_2_i = '{
  masked: (64'h1F83D9ABFB41BD6B ^ ((('sd3 * (p & 'sh7)) == 'sd6) ? 64'(SHA_in.entropy) : masking_rnd['sd6])),
  random: ((('sd3 * (p & 'sh7)) == 'sd6) ? 64'(SHA_in.entropy) : masking_rnd['sd6])
};

st_masked_reg_t h_2_i = '{
  masked: (64'h5BE0CD19137E2179 ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd7) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd7])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd7) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd7])
};

a_sc_big_unsigned_64_8 H_4_i = '{
  0: 64'hCBBB9D5DC1059ED8,
  1: 64'h629A292A367CD507,
  2: 64'h9159015A3070DD17,
  3: 64'h152FECD8F70E5939,
  4: 64'h67332667FFC00B31,
  5: 64'h8EB44A8768581511,
  6: 64'hDB0C2E0D64F98FA7,
  7: 64'h47B5481DBEFA4FA4
};

st_masked_reg_t a_4_i = '{
  masked: (64'hCBBB9D5DC1059ED8 ^ ((('sd3 * (p & 'sh7)) == 'sd0) ? 64'(SHA_in.entropy) : masking_rnd['sd0])),
  random: ((('sd3 * (p & 'sh7)) == 'sd0) ? 64'(SHA_in.entropy) : masking_rnd['sd0])
};

st_masked_reg_t b_3_i = '{
  masked: (64'h629A292A367CD507 ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd1) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd1])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd1) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd1])
};

st_masked_reg_t c_3_i = '{
  masked: (64'h9159015A3070DD17 ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd2) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd2])),
  random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd2) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd2])
};

st_masked_reg_t d_3_i = '{
  masked: (64'h152FECD8F70E5939 ^ ((('sd3 * (p & 'sh7)) == 'sd3) ? 64'(SHA_in.entropy) : masking_rnd['sd3])),
  random: ((('sd3 * (p & 'sh7)) == 'sd3) ? 64'(SHA_in.entropy) : masking_rnd['sd3])
};

st_masked_reg_t e_3_i = '{
  masked: (64'h67332667FFC00B31 ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd4) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd4])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd4) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd4])
};

st_masked_reg_t f_3_i = '{
  masked: (64'h8EB44A8768581511 ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd5) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd5])),
  random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd5) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd5])
};

st_masked_reg_t g_3_i = '{
  masked: (64'hDB0C2E0D64F98FA7 ^ ((('sd3 * (p & 'sh7)) == 'sd6) ? 64'(SHA_in.entropy) : masking_rnd['sd6])),
  random: ((('sd3 * (p & 'sh7)) == 'sd6) ? 64'(SHA_in.entropy) : masking_rnd['sd6])
};

st_masked_reg_t h_3_i = '{
  masked: (64'h47B5481DBEFA4FA4 ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd7) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd7])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd7) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd7])
};

st_masked_reg_t a_5_i = '{
  masked: (H[64'd0] ^ ((('sd3 * (p & 'sh7)) == 'sd0) ? 64'(SHA_in.entropy) : masking_rnd['sd0])),
  random: ((('sd3 * (p & 'sh7)) == 'sd0) ? 64'(SHA_in.entropy) : masking_rnd['sd0])
};

st_masked_reg_t b_4_i = '{
  masked: (H[64'd1] ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd1) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd1])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd1) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd1])
};

st_masked_reg_t c_4_i = '{
  masked: (H[64'd2] ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd2) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd2])),
  random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd2) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd2])
};

st_masked_reg_t d_4_i = '{
  masked: (H[64'd3] ^ ((('sd3 * (p & 'sh7)) == 'sd3) ? 64'(SHA_in.entropy) : masking_rnd['sd3])),
  random: ((('sd3 * (p & 'sh7)) == 'sd3) ? 64'(SHA_in.entropy) : masking_rnd['sd3])
};

st_masked_reg_t e_4_i = '{
  masked: (H[64'd4] ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd4) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd4])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd4) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd4])
};

st_masked_reg_t f_4_i = '{
  masked: (H[64'd5] ^ (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd5) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd5])),
  random: (((('sd3 * (p & 'sh7)) + 'sd2) == 'sd5) ? 64'((SHA_in.entropy >> 192'd128)) : masking_rnd['sd5])
};

st_masked_reg_t g_4_i = '{
  masked: (H[64'd6] ^ ((('sd3 * (p & 'sh7)) == 'sd6) ? 64'(SHA_in.entropy) : masking_rnd['sd6])),
  random: ((('sd3 * (p & 'sh7)) == 'sd6) ? 64'(SHA_in.entropy) : masking_rnd['sd6])
};

st_masked_reg_t h_4_i = '{
  masked: (H[64'd7] ^ (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd7) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd7])),
  random: (((('sd3 * (p & 'sh7)) + 'sd1) == 'sd7) ? 64'((SHA_in.entropy >> 192'd64)) : masking_rnd['sd7])
};

logic ent_shift_0_i = ent_shift(SHA_in.entropy, 192'd32);

logic ent_shift_1_i = ent_shift(SHA_in.entropy, 192'd64);

logic ent_shift_2_i = ent_shift(SHA_in.entropy, 192'd128);

logic ent_shift_3_i = ent_shift(SHA_in.entropy, 192'd256);

logic ent_shift_4_i = ent_shift(SHA_in.entropy, 192'd512);

logic ent_shift_5_i = ent_shift(SHA_in.entropy, 192'd1024);

logic ent_shift_6_i = ent_shift(SHA_in.entropy, 192'd2048);

logic ent_shift_7_i = ent_shift(SHA_in.entropy, 192'd4096);

logic ent_shift_8_i = ent_shift(SHA_in.entropy, 192'd8192);

logic ent_shift_9_i = ent_shift(SHA_in.entropy, 192'd16384);

logic unsigned [63:0] T1_m_0_i = T1_m(e.masked, e.random, f.masked, f.random, g.masked, g.random, h.masked, h.random, K[i], W[i].masked, W[i].random, 0, 128'd0, 64'd0, ent_shift_0_i, ent_shift_1_i, ent_shift_2_i, ent_shift_3_i, ent_shift_4_i, 'sd0);

logic unsigned [63:0] T1_r_0_i = T1_r(e.random, g.random, h.random, W[i].random);

logic unsigned [63:0] T2_m_0_i = T2_m(a.masked, a.random, b.masked, b.random, c.masked, c.random, 0, 128'd0, 64'd0, ent_shift_5_i, ent_shift_6_i, 'sd0);

logic unsigned [63:0] T2_r_0_i = T2_r(a.random, b.random);

logic unsigned [63:0] B2A_conv_0_i = B2A_conv(d.masked, d.random, ent_shift_7_i, 0, 128'd0, 64'd0, 'sd0);

st_masked_reg_t a_6_i = '{
  masked: A2B_conv(64'((T1_m_0_i + T2_m_0_i)), 64'((T1_r_0_i + T2_r_0_i)), ent_shift_8_i, 0, 128'd0, 64'd0, 'sd0),
  random: (T1_r_0_i + T2_r_0_i)
};

st_masked_reg_t e_5_i = '{
  masked: A2B_conv(64'((B2A_conv_0_i + T1_m_0_i)), 64'((d.random + T1_r_0_i)), ent_shift_9_i, 0, 128'd0, 64'd0, 'sd0),
  random: (d.random + T1_r_0_i)
};

logic unsigned [63:0] compute_w_random_0_i = compute_w_random(W[64'd14].random, W[64'd9].random, W[64'd1].random, W[64'd0].random);

logic unsigned [63:0] compute_w_masked_0_i = compute_w_masked(W[64'd14], W[64'd9], W[64'd1], W[64'd0], SHA_in.entropy, 0, 128'd0, 64'd0, 'sd0, compute_w_random_0_i);

logic unsigned [63:0] T1_m_1_i = T1_m(e.masked, e.random, f.masked, f.random, g.masked, g.random, h.masked, h.random, K[i], compute_w_masked_0_i, compute_w_random_0_i, 0, 128'd0, 64'd0, ent_shift_0_i, ent_shift_1_i, ent_shift_2_i, ent_shift_3_i, ent_shift_4_i, 'sd0);

logic unsigned [63:0] T1_r_1_i = T1_r(e.random, g.random, h.random, compute_w_random_0_i);

a_st_masked_reg_t_16 W_2_i = '{
  0: '{ masked: W['sd1].masked, random: W['sd1].random },
  1: '{ masked: W['sd2].masked, random: W['sd2].random },
  2: '{ masked: W['sd3].masked, random: W['sd3].random },
  3: '{ masked: W['sd4].masked, random: W['sd4].random },
  4: '{ masked: W['sd5].masked, random: W['sd5].random },
  5: '{ masked: W['sd6].masked, random: W['sd6].random },
  6: '{ masked: W['sd7].masked, random: W['sd7].random },
  7: '{ masked: W['sd8].masked, random: W['sd8].random },
  8: '{ masked: W['sd9].masked, random: W['sd9].random },
  9: '{ masked: W['sd10].masked, random: W['sd10].random },
  10: '{ masked: W['sd11].masked, random: W['sd11].random },
  11: '{ masked: W['sd12].masked, random: W['sd12].random },
  12: '{ masked: W['sd13].masked, random: W['sd13].random },
  13: '{ masked: W['sd14].masked, random: W['sd14].random },
  14: '{ masked: W['sd15].masked, random: W['sd15].random },
  15: '{ masked: compute_w_masked(W[64'd14], W[64'd9], W[64'd1], W[64'd0], SHA_in.entropy, 0, 128'd0, 64'd0, 'sd0, compute_w_random_0_i), random: compute_w_random(W[64'd14].random, W[64'd9].random, W[64'd1].random, W[64'd0].random) }
};

st_masked_reg_t a_7_i = '{
  masked: A2B_conv(64'((T1_m_1_i + T2_m_0_i)), 64'((T1_r_1_i + T2_r_0_i)), ent_shift_8_i, 0, 128'd0, 64'd0, 'sd0),
  random: (T1_r_1_i + T2_r_0_i)
};

st_masked_reg_t e_6_i = '{
  masked: A2B_conv(64'((B2A_conv_0_i + T1_m_1_i)), 64'((d.random + T1_r_1_i)), ent_shift_9_i, 0, 128'd0, 64'd0, 'sd0),
  random: (d.random + T1_r_1_i)
};

a_sc_big_unsigned_64_8 H_5_i = '{
  0: (H[64'd0] + (a.masked ^ a.random)),
  1: (H['sd1] + (b.masked ^ b.random)),
  2: (H['sd2] + (c.masked ^ c.random)),
  3: (H['sd3] + (d.masked ^ d.random)),
  4: (H['sd4] + (e.masked ^ e.random)),
  5: (H['sd5] + (f.masked ^ f.random)),
  6: (H['sd6] + (g.masked ^ g.random)),
  7: (H['sd7] + (h.masked ^ h.random))
};


sequence reset_sequence;
  !rst ##1 rst;
endsequence


reset_a: assert property (reset_p);
property reset_p;
  $past(!rst) |->
  IDLE &&
  H == H_0_i &&
  W == W_0_i &&
  a == a_0_i &&
  b == a_0_i &&
  c == a_0_i &&
  d == a_0_i &&
  e == a_0_i &&
  f == a_0_i &&
  g == a_0_i &&
  h == a_0_i &&
  i == 'sd0 &&
  masking_rnd == masking_rnd_0_i &&
  p == 'sd0 &&
  SHA_Input_notify == 1 &&
  out_notify == 0;
endproperty


CTRL_RND_to_CTRL_RND_a: assert property (disable iff(!rst) CTRL_RND_to_CTRL_RND_p);
property CTRL_RND_to_CTRL_RND_p;
  CTRL_RND &&
  (('sd1 + p) < 'sd9)
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
  ##1
  CTRL_RND &&
  H == $past(H, 1) &&
  W == $past(W, 1) &&
  a == $past(a, 1) &&
  b == $past(b, 1) &&
  c == $past(c, 1) &&
  d == $past(d, 1) &&
  e == $past(e, 1) &&
  f == $past(f, 1) &&
  g == $past(g, 1) &&
  h == $past(h, 1) &&
  i == $past(i, 1) &&
  masking_rnd == $past(masking_rnd_1_i, 1) &&
  p == ('sd1 + $past(p, 1));
endproperty


CTRL_RND_to_SHA_Rounds_a: assert property (disable iff(!rst) CTRL_RND_to_SHA_Rounds_p);
property CTRL_RND_to_SHA_Rounds_p;
  CTRL_RND &&
  (('sd1 + p) >= 'sd9) &&
  init_cmd &&
  (SHA_Mode_in == 'sd0)
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H_1_i, 1) &&
  W == $past(W_1_i, 1) &&
  a == $past(a_1_i, 1) &&
  b == $past(b_0_i, 1) &&
  c == $past(c_0_i, 1) &&
  d == $past(d_0_i, 1) &&
  e == $past(e_0_i, 1) &&
  f == $past(f_0_i, 1) &&
  g == $past(g_0_i, 1) &&
  h == $past(h_0_i, 1) &&
  i == 'sd0 &&
  masking_rnd == $past(masking_rnd_1_i, 1) &&
  p == ('sd1 + $past(p, 1));
endproperty


CTRL_RND_to_SHA_Rounds_1_a: assert property (disable iff(!rst) CTRL_RND_to_SHA_Rounds_1_p);
property CTRL_RND_to_SHA_Rounds_1_p;
  CTRL_RND &&
  (('sd1 + p) >= 'sd9) &&
  init_cmd &&
  (SHA_Mode_in == 'sd1)
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H_2_i, 1) &&
  W == $past(W_1_i, 1) &&
  a == $past(a_2_i, 1) &&
  b == $past(b_1_i, 1) &&
  c == $past(c_1_i, 1) &&
  d == $past(d_1_i, 1) &&
  e == $past(e_1_i, 1) &&
  f == $past(f_1_i, 1) &&
  g == $past(g_1_i, 1) &&
  h == $past(h_1_i, 1) &&
  i == 'sd0 &&
  masking_rnd == $past(masking_rnd_1_i, 1) &&
  p == ('sd1 + $past(p, 1));
endproperty


CTRL_RND_to_SHA_Rounds_2_a: assert property (disable iff(!rst) CTRL_RND_to_SHA_Rounds_2_p);
property CTRL_RND_to_SHA_Rounds_2_p;
  CTRL_RND &&
  (('sd1 + p) >= 'sd9) &&
  init_cmd &&
  (SHA_Mode_in == 'sd3)
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H_3_i, 1) &&
  W == $past(W_1_i, 1) &&
  a == $past(a_3_i, 1) &&
  b == $past(b_2_i, 1) &&
  c == $past(c_2_i, 1) &&
  d == $past(d_2_i, 1) &&
  e == $past(e_2_i, 1) &&
  f == $past(f_2_i, 1) &&
  g == $past(g_2_i, 1) &&
  h == $past(h_2_i, 1) &&
  i == 'sd0 &&
  masking_rnd == $past(masking_rnd_1_i, 1) &&
  p == ('sd1 + $past(p, 1));
endproperty


CTRL_RND_to_SHA_Rounds_3_a: assert property (disable iff(!rst) CTRL_RND_to_SHA_Rounds_3_p);
property CTRL_RND_to_SHA_Rounds_3_p;
  CTRL_RND &&
  (('sd1 + p) >= 'sd9) &&
  init_cmd &&
  (SHA_Mode_in != 'sd0) &&
  (SHA_Mode_in != 'sd1) &&
  (SHA_Mode_in != 'sd3)
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H_4_i, 1) &&
  W == $past(W_1_i, 1) &&
  a == $past(a_4_i, 1) &&
  b == $past(b_3_i, 1) &&
  c == $past(c_3_i, 1) &&
  d == $past(d_3_i, 1) &&
  e == $past(e_3_i, 1) &&
  f == $past(f_3_i, 1) &&
  g == $past(g_3_i, 1) &&
  h == $past(h_3_i, 1) &&
  i == 'sd0 &&
  masking_rnd == $past(masking_rnd_1_i, 1) &&
  p == ('sd1 + $past(p, 1));
endproperty


CTRL_RND_to_SHA_Rounds_4_a: assert property (disable iff(!rst) CTRL_RND_to_SHA_Rounds_4_p);
property CTRL_RND_to_SHA_Rounds_4_p;
  CTRL_RND &&
  (('sd1 + p) >= 'sd9) &&
  !init_cmd
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H, 1) &&
  W == $past(W_1_i, 1) &&
  a == $past(a_5_i, 1) &&
  b == $past(b_4_i, 1) &&
  c == $past(c_4_i, 1) &&
  d == $past(d_4_i, 1) &&
  e == $past(e_4_i, 1) &&
  f == $past(f_4_i, 1) &&
  g == $past(g_4_i, 1) &&
  h == $past(h_4_i, 1) &&
  i == 'sd0 &&
  masking_rnd == $past(masking_rnd_1_i, 1) &&
  p == ('sd1 + $past(p, 1));
endproperty


DONE_to_IDLE_a: assert property (disable iff(!rst) DONE_to_IDLE_p);
property DONE_to_IDLE_p;
  DONE
|->
  ##1
  IDLE &&
  H == $past(H_5_i, 1) &&
  W == $past(W, 1) &&
  a == $past(a, 1) &&
  b == $past(b, 1) &&
  c == $past(c, 1) &&
  d == $past(d, 1) &&
  e == $past(e, 1) &&
  f == $past(f, 1) &&
  g == $past(g, 1) &&
  h == $past(h, 1) &&
  i == $past(i, 1) &&
  masking_rnd == $past(masking_rnd, 1) &&
  out == 512'(((512'(((512'(((512'(((512'(((512'(((512'(((512'((($past(H['sd7], 1) + ($past(h.masked, 1) ^ $past(h.random, 1))) << 64'd448)) >> 512'd64) + (($past(H['sd6], 1) + ($past(g.masked, 1) ^ $past(g.random, 1))) << 64'd448))) >> 512'd64) + (($past(H['sd5], 1) + ($past(f.masked, 1) ^ $past(f.random, 1))) << 64'd448))) >> 512'd64) + (($past(H['sd4], 1) + ($past(e.masked, 1) ^ $past(e.random, 1))) << 64'd448))) >> 512'd64) + (($past(H['sd3], 1) + ($past(d.masked, 1) ^ $past(d.random, 1))) << 64'd448))) >> 512'd64) + (($past(H['sd2], 1) + ($past(c.masked, 1) ^ $past(c.random, 1))) << 64'd448))) >> 512'd64) + (($past(H['sd1], 1) + ($past(b.masked, 1) ^ $past(b.random, 1))) << 64'd448))) >> 512'd64) + (($past(H[64'd0], 1) + ($past(a.masked, 1) ^ $past(a.random, 1))) << 64'd448))) &&
  p == $past(p, 1) &&
  SHA_Input_notify == 1 &&
  out_notify == 1;
endproperty


IDLE_to_CTRL_RND_a: assert property (disable iff(!rst) IDLE_to_CTRL_RND_p);
property IDLE_to_CTRL_RND_p;
  IDLE &&
  SHA_Input_sync
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
  ##1
  CTRL_RND &&
  H == $past(H, 1) &&
  W == $past(W, 1) &&
  a == $past(a, 1) &&
  b == $past(b, 1) &&
  c == $past(c, 1) &&
  d == $past(d, 1) &&
  e == $past(e, 1) &&
  f == $past(f, 1) &&
  g == $past(g, 1) &&
  h == $past(h, 1) &&
  i == $past(i, 1) &&
  masking_rnd == $past(masking_rnd, 1) &&
  p == 'sd0;
endproperty


SHA_Rounds_to_DONE_a: assert property (disable iff(!rst) SHA_Rounds_to_DONE_p);
property SHA_Rounds_to_DONE_p;
  SHA_Rounds &&
  (i >= 'sd16) &&
  (('sd1 + i) >= 'sd80)
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
  ##1
  DONE &&
  H == $past(H, 1) &&
  W == $past(W_2_i, 1) &&
  a == $past(a_7_i, 1) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == $past(e_6_i, 1) &&
  f == $past(e, 1) &&
  g == $past(f, 1) &&
  h == $past(g, 1) &&
  i == ('sd1 + $past(i, 1)) &&
  masking_rnd == $past(masking_rnd, 1) &&
  p == $past(p, 1);
endproperty


SHA_Rounds_to_SHA_Rounds_a: assert property (disable iff(!rst) SHA_Rounds_to_SHA_Rounds_p);
property SHA_Rounds_to_SHA_Rounds_p;
  SHA_Rounds &&
  (i < 'sd16)
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H, 1) &&
  W == $past(W, 1) &&
  a == $past(a_6_i, 1) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == $past(e_5_i, 1) &&
  f == $past(e, 1) &&
  g == $past(f, 1) &&
  h == $past(g, 1) &&
  i == ('sd1 + $past(i, 1)) &&
  masking_rnd == $past(masking_rnd, 1) &&
  p == $past(p, 1);
endproperty


SHA_Rounds_to_SHA_Rounds_1_a: assert property (disable iff(!rst) SHA_Rounds_to_SHA_Rounds_1_p);
property SHA_Rounds_to_SHA_Rounds_1_p;
  SHA_Rounds &&
  (i >= 'sd16) &&
  (('sd1 + i) < 'sd80)
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H, 1) &&
  W == $past(W_2_i, 1) &&
  a == $past(a_7_i, 1) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == $past(e_6_i, 1) &&
  f == $past(e, 1) &&
  g == $past(f, 1) &&
  h == $past(g, 1) &&
  i == ('sd1 + $past(i, 1)) &&
  masking_rnd == $past(masking_rnd, 1) &&
  p == $past(p, 1);
endproperty


IDLE_wait_a: assert property (disable iff(!rst) IDLE_wait_p);
property IDLE_wait_p;
  IDLE &&
  !SHA_Input_sync
|->
  ##1
  IDLE &&
  H == $past(H, 1) &&
  W == $past(W, 1) &&
  a == $past(a, 1) &&
  b == $past(b, 1) &&
  c == $past(c, 1) &&
  d == $past(d, 1) &&
  e == $past(e, 1) &&
  f == $past(f, 1) &&
  g == $past(g, 1) &&
  h == $past(h, 1) &&
  i == $past(i, 1) &&
  masking_rnd == $past(masking_rnd, 1) &&
  p == $past(p, 1) &&
  SHA_Input_notify == 1 &&
  out_notify == 0;
endproperty


endmodule


module fv_sha512_masked_core_wrap_m;


default clocking default_clk @(posedge (sha512_masked_core.clk)); endclocking


st_SHA_Args SHA_Input = '{
  in: (sha512_masked_core.block_msg),
  entropy: (sha512_masked_core.entropy),
  SHA_Mode: (sha512_masked_core.mode),
  init_cmd: (sha512_masked_core.init_cmd),
  next_cmd: (sha512_masked_core.next_cmd),
  zeroize: (sha512_masked_core.zeroize)
};
a_sc_big_unsigned_64_8 H = '{
  0: (sha512_masked_core.H0_reg),
  1: (sha512_masked_core.H1_reg),
  2: (sha512_masked_core.H2_reg),
  3: (sha512_masked_core.H3_reg),
  4: (sha512_masked_core.H4_reg),
  5: (sha512_masked_core.H5_reg),
  6: (sha512_masked_core.H6_reg),
  7: (sha512_masked_core.H7_reg)
};
st_SHA_Args SHA_in = '{
  in: (sha512_masked_core.block_msg),
  entropy: (sha512_masked_core.entropy),
  SHA_Mode: (sha512_masked_core.mode),
  init_cmd: (sha512_masked_core.init_cmd),
  next_cmd: (sha512_masked_core.next_cmd),
  zeroize: (sha512_masked_core.zeroize)
};
a_st_masked_reg_t_16 W = '{
  0: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[00].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[00].random)
  },
  1: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[01].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[01].random)
  },
  2: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[2].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[2].random)
  },
  3: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[3].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[3].random)
  },
  4: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[4].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[4].random)
  },
  5: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[5].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[5].random)
  },
  6: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[6].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[6].random)
  },
  7: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[7].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[7].random)
  },
  8: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[8].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[8].random)
  },
  9: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[9].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[9].random)
  },
  10: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[10].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[10].random)
  },
  11: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[11].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[11].random)
  },
  12: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[12].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[12].random)
  },
  13: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[13].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[13].random)
  },
  14: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[14].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[14].random)
  },
  15: '{
    masked: (sha512_masked_core.w_mem_inst.w_mem[15].masked),
    random: (sha512_masked_core.w_mem_inst.w_mem[15].random)
  }
};
st_masked_reg_t a = '{
  masked: (sha512_masked_core.a_reg.masked),
  random: (sha512_masked_core.a_reg.random)
};
st_masked_reg_t b = '{
  masked: (sha512_masked_core.b_reg.masked),
  random: (sha512_masked_core.b_reg.random)
};
st_masked_reg_t c = '{
  masked: (sha512_masked_core.c_reg.masked),
  random: (sha512_masked_core.c_reg.random)
};
st_masked_reg_t d = '{
  masked: (sha512_masked_core.d_reg.masked),
  random: (sha512_masked_core.d_reg.random)
};
st_masked_reg_t e = '{
  masked: (sha512_masked_core.e_reg.masked),
  random: (sha512_masked_core.e_reg.random)
};
st_masked_reg_t f = '{
  masked: (sha512_masked_core.f_reg.masked),
  random: (sha512_masked_core.f_reg.random)
};
st_masked_reg_t g = '{
  masked: (sha512_masked_core.g_reg.masked),
  random: (sha512_masked_core.g_reg.random)
};
st_masked_reg_t h = '{
  masked: (sha512_masked_core.h_reg.masked),
  random: (sha512_masked_core.h_reg.random)
};
a_sc_big_unsigned_64_24 masking_rnd = '{
  0: (sha512_masked_core.masking_rnd[0]),
  1: (sha512_masked_core.masking_rnd[1]),
  2: (sha512_masked_core.masking_rnd[2]),
  3: (sha512_masked_core.masking_rnd[3]),
  4: (sha512_masked_core.masking_rnd[4]),
  5: (sha512_masked_core.masking_rnd[5]),
  6: (sha512_masked_core.masking_rnd[6]),
  7: (sha512_masked_core.masking_rnd[7]),
  8: (sha512_masked_core.masking_rnd[8]),
  9: (sha512_masked_core.masking_rnd[9]),
  10: (sha512_masked_core.masking_rnd[10]),
  11: (sha512_masked_core.masking_rnd[11]),
  12: (sha512_masked_core.masking_rnd[12]),
  13: (sha512_masked_core.masking_rnd[13]),
  14: (sha512_masked_core.masking_rnd[14]),
  15: (sha512_masked_core.masking_rnd[15]),
  16: (sha512_masked_core.masking_rnd[16]),
  17: (sha512_masked_core.masking_rnd[17]),
  18: (sha512_masked_core.masking_rnd[18]),
  19: (sha512_masked_core.masking_rnd[19]),
  20: (sha512_masked_core.masking_rnd[20]),
  21: (sha512_masked_core.masking_rnd[21]),
  22: (sha512_masked_core.masking_rnd[22]),
  23: (sha512_masked_core.masking_rnd[23])
};


fv_sha512_masked_core_m fv_sha512_masked_core(
  .rst((sha512_masked_core.reset_n)  && !(sha512_masked_core.zeroize)),
  .clk(sha512_masked_core.clk),

  // Ports
  .SHA_Input_sync(((sha512_masked_core.init_cmd) || (sha512_masked_core.next_cmd))),
  .SHA_Input_notify(sha512_masked_core.ready),
  .SHA_Input(SHA_Input),

  .out_notify((sha512_masked_core.digest_valid) && ((sha512_masked_core.sha512_ctrl_reg==2'h0) && $past(sha512_masked_core.sha512_ctrl_reg==2'h3) )),
  .out(sha512_masked_core.digest),

  // Registers
  .H(H),
  .SHA_Mode_in(sha512_masked_core.mode),
  .SHA_in(SHA_in),
  .W(W),
  .a(a),
  .b(b),
  .block_in(sha512_masked_core.block_msg),
  .c(c),
  .d(d),
  .e(e),
  .f(f),
  .g(g),
  .h(h),
  .i(sha512_masked_core.round_ctr_reg),
  .init_cmd(sha512_masked_core.init_reg),
  .masking_rnd(masking_rnd),
  .p(sha512_masked_core.rnd_ctr_reg),

  // States
  .IDLE(sha512_masked_core.sha512_ctrl_reg==2'h0),
  .CTRL_RND(sha512_masked_core.sha512_ctrl_reg==2'h1),
  .SHA_Rounds(sha512_masked_core.sha512_ctrl_reg==2'h2),
  .DONE(sha512_masked_core.sha512_ctrl_reg==2'h3)
);


endmodule


bind sha512_masked_core fv_sha512_masked_core_wrap_m fv_sha512_masked_core_wrap();
