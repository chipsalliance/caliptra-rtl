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
 
import sha512_masked_pkg::*;


module fv_sha512_masked_m(
  input bit rst,
  input bit clk,

  // Inputs
  input st_SHA_Args sha_in_struct,
  input bit unsigned [73:0] lfsr_in,

  // Outputs
  input bit unsigned [511:0] digest_out,

  // Valid signals
  input bit block_in_valid,
  input bit digest_valid,
  
  // Ready signals
  input bit block_in_ready,

  // Registers
  input a_sc_big_unsigned_64_8 H,
  input bit signed [31:0] block_sha_mode,
  input a_sc_big_unsigned_64_16 W,
  input st_masked_reg_t a,
  input st_masked_reg_t b,
  input bit unsigned [1023:0] block_in,
  input st_masked_reg_t c,
  input st_masked_reg_t d,
  input st_masked_reg_t e,
  input st_masked_reg_t f,
  input st_masked_reg_t g,
  input st_masked_reg_t h,
  input bit signed [31:0] i,
  input bit block_init,
  input bit unsigned [73:0] lfsr_rnd,
  input bit signed [31:0] rnd_cnt_reg,
  input a_sc_big_unsigned_64_8 rh_masking_rnd,

  // States
  input bit IDLE,
  input bit CTRL_RND,
  input bit SHA_Rounds,
  input bit DONE
);


default clocking default_clk @(posedge clk); endclocking


a_sc_big_unsigned_64_8 H_0 = '{
  0: 64'd0,
  1: 64'd0,
  2: 64'd0,
  3: 64'd0,
  4: 64'd0,
  5: 64'd0,
  6: 64'd0,
  7: 64'd0
};

a_sc_big_unsigned_64_16 W_0 = '{
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
  15: 64'd0
};

st_masked_reg_t a_0 = '{
  masked: 64'd0,
  random: 64'd0
};

a_sc_big_unsigned_64_8 rh_masking_rnd_0 = '{
  0: ((rnd_cnt_reg == 'sd0) ? lfsr_in : rh_masking_rnd['sd0]),
  1: ((rnd_cnt_reg == 'sd1) ? lfsr_in : rh_masking_rnd['sd1]),
  2: ((rnd_cnt_reg == 'sd2) ? lfsr_in : rh_masking_rnd['sd2]),
  3: ((rnd_cnt_reg == 'sd3) ? lfsr_in : rh_masking_rnd['sd3]),
  4: ((rnd_cnt_reg == 'sd4) ? lfsr_in : rh_masking_rnd['sd4]),
  5: ((rnd_cnt_reg == 'sd5) ? lfsr_in : rh_masking_rnd['sd5]),
  6: ((rnd_cnt_reg == 'sd6) ? lfsr_in : rh_masking_rnd['sd6]),
  7: ((rnd_cnt_reg == 'sd7) ? lfsr_in : rh_masking_rnd['sd7])
};

a_sc_big_unsigned_64_8 H_1 = '{
  0: 64'h8C3D37C819544DA2,
  1: 64'h73E1996689DCD4D6,
  2: 64'h1DFAB7AE32FF9C82,
  3: 64'h679DD514582F9FCF,
  4: 64'hF6D2B697BD44DA8,
  5: 64'h77E36F7304C48942,
  6: 64'h3F9D85A86A1D36C8,
  7: 64'h1112E6AD91D692A1
};

a_sc_big_unsigned_64_16 W_1 = '{
  0: slicer(block_in, 'sd15),
  1: slicer(block_in, 'sd14),
  2: slicer(block_in, 'sd13),
  3: slicer(block_in, 'sd12),
  4: slicer(block_in, 'sd11),
  5: slicer(block_in, 'sd10),
  6: slicer(block_in, 'sd9),
  7: slicer(block_in, 'sd8),
  8: slicer(block_in, 'sd7),
  9: slicer(block_in, 'sd6),
  10: slicer(block_in, 'sd5),
  11: slicer(block_in, 'sd4),
  12: slicer(block_in, 'sd3),
  13: slicer(block_in, 'sd2),
  14: slicer(block_in, 'sd1),
  15: slicer(block_in, 'sd0)
};

st_masked_reg_t a_1 = '{
  masked: (64'h8C3D37C819544DA2 ^ (0 ? lfsr_in : rh_masking_rnd['sd0])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd0])
};

st_masked_reg_t b_0 = '{
  masked: (64'h73E1996689DCD4D6 ^ (0 ? lfsr_in : rh_masking_rnd['sd1])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd1])
};

st_masked_reg_t c_0 = '{
  masked: (64'h1DFAB7AE32FF9C82 ^ (0 ? lfsr_in : rh_masking_rnd['sd2])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd2])
};

st_masked_reg_t d_0 = '{
  masked: (64'h679DD514582F9FCF ^ (0 ? lfsr_in : rh_masking_rnd['sd3])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd3])
};

st_masked_reg_t e_0 = '{
  masked: (64'hF6D2B697BD44DA8 ^ (0 ? lfsr_in : rh_masking_rnd['sd4])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd4])
};

st_masked_reg_t f_0 = '{
  masked: (64'h77E36F7304C48942 ^ (0 ? lfsr_in : rh_masking_rnd['sd5])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd5])
};

st_masked_reg_t g_0 = '{
  masked: (64'h3F9D85A86A1D36C8 ^ (0 ? lfsr_in : rh_masking_rnd['sd6])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd6])
};

st_masked_reg_t h_0 = '{
  masked: (64'h1112E6AD91D692A1 ^ (0 ? lfsr_in : rh_masking_rnd['sd7])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd7])
};

a_sc_big_unsigned_64_8 rh_masking_rnd_1 = '{
  0: lfsr_in,
  1: rh_masking_rnd['sd1],
  2: rh_masking_rnd['sd2],
  3: rh_masking_rnd['sd3],
  4: rh_masking_rnd['sd4],
  5: rh_masking_rnd['sd5],
  6: rh_masking_rnd['sd6],
  7: rh_masking_rnd['sd7]
};

a_sc_big_unsigned_64_8 H_2 = '{
  0: 64'h22312194FC2BF72C,
  1: 64'h9F555FA3C84C64C2,
  2: 64'h2393B86B6F53B151,
  3: 64'h963877195940EABD,
  4: 64'h96283EE2A88EFFE3,
  5: 64'hBE5E1E2553863992,
  6: 64'h2B0199FC2C85B8AA,
  7: 64'hEB72DDC81C52CA2
};

st_masked_reg_t a_2 = '{
  masked: (64'h22312194FC2BF72C ^ (0 ? lfsr_in : rh_masking_rnd['sd0])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd0])
};

st_masked_reg_t b_1 = '{
  masked: (64'h9F555FA3C84C64C2 ^ (0 ? lfsr_in : rh_masking_rnd['sd1])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd1])
};

st_masked_reg_t c_1 = '{
  masked: (64'h2393B86B6F53B151 ^ (0 ? lfsr_in : rh_masking_rnd['sd2])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd2])
};

st_masked_reg_t d_1 = '{
  masked: (64'h963877195940EABD ^ (0 ? lfsr_in : rh_masking_rnd['sd3])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd3])
};

st_masked_reg_t e_1 = '{
  masked: (64'h96283EE2A88EFFE3 ^ (0 ? lfsr_in : rh_masking_rnd['sd4])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd4])
};

st_masked_reg_t f_1 = '{
  masked: (64'hBE5E1E2553863992 ^ (0 ? lfsr_in : rh_masking_rnd['sd5])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd5])
};

st_masked_reg_t g_1 = '{
  masked: (64'h2B0199FC2C85B8AA ^ (0 ? lfsr_in : rh_masking_rnd['sd6])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd6])
};

st_masked_reg_t h_1 = '{
  masked: (64'hEB72DDC81C52CA2 ^ (0 ? lfsr_in : rh_masking_rnd['sd7])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd7])
};

a_sc_big_unsigned_64_8 H_3 = '{
  0: 64'h6A09E667F3BCC908,
  1: 64'hBB67AE8584CAA73B,
  2: 64'h3C6EF372FE94F82B,
  3: 64'hA54FF53A5F1D36F1,
  4: 64'h510E527FADE682D1,
  5: 64'h9B05688C2B3E6C1F,
  6: 64'h1F83D9ABFB41BD6B,
  7: 64'h5BE0CD19137E2179
};

st_masked_reg_t a_3 = '{
  masked: (64'h6A09E667F3BCC908 ^ (0 ? lfsr_in : rh_masking_rnd['sd0])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd0])
};

st_masked_reg_t b_2 = '{
  masked: (64'hBB67AE8584CAA73B ^ (0 ? lfsr_in : rh_masking_rnd['sd1])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd1])
};

st_masked_reg_t c_2 = '{
  masked: (64'h3C6EF372FE94F82B ^ (0 ? lfsr_in : rh_masking_rnd['sd2])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd2])
};

st_masked_reg_t d_2 = '{
  masked: (64'hA54FF53A5F1D36F1 ^ (0 ? lfsr_in : rh_masking_rnd['sd3])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd3])
};

st_masked_reg_t e_2 = '{
  masked: (64'h510E527FADE682D1 ^ (0 ? lfsr_in : rh_masking_rnd['sd4])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd4])
};

st_masked_reg_t f_2 = '{
  masked: (64'h9B05688C2B3E6C1F ^ (0 ? lfsr_in : rh_masking_rnd['sd5])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd5])
};

st_masked_reg_t g_2 = '{
  masked: (64'h1F83D9ABFB41BD6B ^ (0 ? lfsr_in : rh_masking_rnd['sd6])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd6])
};

st_masked_reg_t h_2 = '{
  masked: (64'h5BE0CD19137E2179 ^ (0 ? lfsr_in : rh_masking_rnd['sd7])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd7])
};

a_sc_big_unsigned_64_8 H_4 = '{
  0: 64'hCBBB9D5DC1059ED8,
  1: 64'h629A292A367CD507,
  2: 64'h9159015A3070DD17,
  3: 64'h152FECD8F70E5939,
  4: 64'h67332667FFC00B31,
  5: 64'h8EB44A8768581511,
  6: 64'hDB0C2E0D64F98FA7,
  7: 64'h47B5481DBEFA4FA4
};

st_masked_reg_t a_4 = '{
  masked: (64'hCBBB9D5DC1059ED8 ^ (0 ? lfsr_in : rh_masking_rnd['sd0])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd0])
};

st_masked_reg_t b_3 = '{
  masked: (64'h629A292A367CD507 ^ (0 ? lfsr_in : rh_masking_rnd['sd1])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd1])
};

st_masked_reg_t c_3 = '{
  masked: (64'h9159015A3070DD17 ^ (0 ? lfsr_in : rh_masking_rnd['sd2])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd2])
};

st_masked_reg_t d_3 = '{
  masked: (64'h152FECD8F70E5939 ^ (0 ? lfsr_in : rh_masking_rnd['sd3])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd3])
};

st_masked_reg_t e_3 = '{
  masked: (64'h67332667FFC00B31 ^ (0 ? lfsr_in : rh_masking_rnd['sd4])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd4])
};

st_masked_reg_t f_3 = '{
  masked: (64'h8EB44A8768581511 ^ (0 ? lfsr_in : rh_masking_rnd['sd5])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd5])
};

st_masked_reg_t g_3 = '{
  masked: (64'hDB0C2E0D64F98FA7 ^ (0 ? lfsr_in : rh_masking_rnd['sd6])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd6])
};

st_masked_reg_t h_3 = '{
  masked: (64'h47B5481DBEFA4FA4 ^ (0 ? lfsr_in : rh_masking_rnd['sd7])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd7])
};

st_masked_reg_t a_5 = '{
  masked: (H[64'd0] ^ (0 ? lfsr_in : rh_masking_rnd['sd0])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd0])
};

st_masked_reg_t b_4 = '{
  masked: (H[64'd1] ^ (0 ? lfsr_in : rh_masking_rnd['sd1])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd1])
};

st_masked_reg_t c_4 = '{
  masked: (H[64'd2] ^ (0 ? lfsr_in : rh_masking_rnd['sd2])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd2])
};

st_masked_reg_t d_4 = '{
  masked: (H[64'd3] ^ (0 ? lfsr_in : rh_masking_rnd['sd3])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd3])
};

st_masked_reg_t e_4 = '{
  masked: (H[64'd4] ^ (0 ? lfsr_in : rh_masking_rnd['sd4])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd4])
};

st_masked_reg_t f_4 = '{
  masked: (H[64'd5] ^ (0 ? lfsr_in : rh_masking_rnd['sd5])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd5])
};

st_masked_reg_t g_4 = '{
  masked: (H[64'd6] ^ (0 ? lfsr_in : rh_masking_rnd['sd6])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd6])
};

st_masked_reg_t h_4 = '{
  masked: (H[64'd7] ^ (0 ? lfsr_in : rh_masking_rnd['sd7])),
  random: (0 ? lfsr_in : rh_masking_rnd['sd7])
};

st_masked_reg_t a_6 = '{
  masked: A2B_conv(64'((T1_m(e.masked, e.random, f.masked, f.random, g.masked, g.random, h.masked, h.random, K[i], (W[i] ^ 64'(lfsr_rnd)), 64'(lfsr_rnd), 0, 128'd0, 64'd0, (((lfsr_rnd >> 74'd64) & 74'h1) == 74'd1), ((((lfsr_rnd >> 74'd64) >> 74'd1) & 74'h1) == 74'd1), (((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), ((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), (((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), 'sd10) + T2_m(a.masked, a.random, b.masked, b.random, c.masked, c.random, 0, 128'd0, 64'd0, ((((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), (((((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), 'sd10))), 64'((T1_r(e.random, g.random, h.random, 64'(lfsr_rnd)) + T2_r(a.random, b.random))), (((((((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), 0, 128'd0, 64'd0, 'sd10),
  random: (T1_r(e.random, g.random, h.random, 64'(lfsr_rnd)) + T2_r(a.random, b.random))
};

st_masked_reg_t e_5 = '{
  masked: A2B_conv(64'((B2A_conv(d.masked, d.random, ((((((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), 0, 128'd0, 64'd0, 'sd10) + T1_m(e.masked, e.random, f.masked, f.random, g.masked, g.random, h.masked, h.random, K[i], (W[i] ^ 64'(lfsr_rnd)), 64'(lfsr_rnd), 0, 128'd0, 64'd0, (((lfsr_rnd >> 74'd64) & 74'h1) == 74'd1), ((((lfsr_rnd >> 74'd64) >> 74'd1) & 74'h1) == 74'd1), (((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), ((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), (((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), 'sd10))), 64'((d.random + T1_r(e.random, g.random, h.random, 64'(lfsr_rnd)))), ((((((((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), 0, 128'd0, 64'd0, 'sd10),
  random: (d.random + T1_r(e.random, g.random, h.random, 64'(lfsr_rnd)))
};

a_sc_big_unsigned_64_16 W_2 = '{
  0: W['sd1],
  1: W['sd2],
  2: W['sd3],
  3: W['sd4],
  4: W['sd5],
  5: W['sd6],
  6: W['sd7],
  7: W['sd8],
  8: W['sd9],
  9: W['sd10],
  10: W['sd11],
  11: W['sd12],
  12: W['sd13],
  13: W['sd14],
  14: W['sd15],
  15: compute_w(W[64'd14], W[64'd9], W[64'd1], W[64'd0])
};

st_masked_reg_t a_7 = '{
  masked: A2B_conv(64'((T1_m(e.masked, e.random, f.masked, f.random, g.masked, g.random, h.masked, h.random, K[i], (compute_w(W[64'd14], W[64'd9], W[64'd1], W[64'd0]) ^ 64'(lfsr_rnd)), 64'(lfsr_rnd), 0, 128'd0, 64'd0, (((lfsr_rnd >> 74'd64) & 74'h1) == 74'd1), ((((lfsr_rnd >> 74'd64) >> 74'd1) & 74'h1) == 74'd1), (((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), ((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), (((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), 'sd10) + T2_m(a.masked, a.random, b.masked, b.random, c.masked, c.random, 0, 128'd0, 64'd0, ((((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), (((((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), 'sd10))), 64'((T1_r(e.random, g.random, h.random, 64'(lfsr_rnd)) + T2_r(a.random, b.random))), (((((((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), 0, 128'd0, 64'd0, 'sd10),
  random: (T1_r(e.random, g.random, h.random, 64'(lfsr_rnd)) + T2_r(a.random, b.random))
};

st_masked_reg_t e_6 = '{
  masked: A2B_conv(64'((B2A_conv(d.masked, d.random, ((((((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), 0, 128'd0, 64'd0, 'sd10) + T1_m(e.masked, e.random, f.masked, f.random, g.masked, g.random, h.masked, h.random, K[i], (compute_w(W[64'd14], W[64'd9], W[64'd1], W[64'd0]) ^ 64'(lfsr_rnd)), 64'(lfsr_rnd), 0, 128'd0, 64'd0, (((lfsr_rnd >> 74'd64) & 74'h1) == 74'd1), ((((lfsr_rnd >> 74'd64) >> 74'd1) & 74'h1) == 74'd1), (((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), ((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), (((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), 'sd10))), 64'((d.random + T1_r(e.random, g.random, h.random, 64'(lfsr_rnd)))), ((((((((((((lfsr_rnd >> 74'd64) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) >> 74'd1) & 74'h1) == 74'd1), 0, 128'd0, 64'd0, 'sd10),
  random: (d.random + T1_r(e.random, g.random, h.random, 64'(lfsr_rnd)))
};

a_sc_big_unsigned_64_8 H_5 = '{
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
  $past(!rst) && rst |->
  IDLE &&
  H == H_0 &&
  W == W_0 &&
  a == a_0 &&
  b == a_0 &&
  c == a_0 &&
  d == a_0 &&
  e == a_0 &&
  f == a_0 &&
  g == a_0 &&
  h == a_0 &&
  i == 'sd0 &&
  rnd_cnt_reg == 'sd0 &&
  rh_masking_rnd == H_0 &&
  block_in_ready == 1 &&
  digest_valid == 0;
endproperty


CTRL_RND_to_CTRL_RND_a: assert property (disable iff(!rst) CTRL_RND_to_CTRL_RND_p);
property CTRL_RND_to_CTRL_RND_p;
  CTRL_RND &&
  (('sd1 + rnd_cnt_reg) < 'sd9)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
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
  rnd_cnt_reg == ('sd1 + $past(rnd_cnt_reg, 1)) &&
  rh_masking_rnd == $past(rh_masking_rnd_0, 1);
endproperty


CTRL_RND_to_SHA_Rounds_224_a: assert property (disable iff(!rst) CTRL_RND_to_SHA_Rounds_224_p);
property CTRL_RND_to_SHA_Rounds_224_p;
  CTRL_RND &&
  (('sd1 + rnd_cnt_reg) >= 'sd9) &&
  block_init &&
  (block_sha_mode == 'sd0)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H_1, 1) &&
  W == $past(W_1, 1) &&
  a == $past(a_1, 1) &&
  b == $past(b_0, 1) &&
  c == $past(c_0, 1) &&
  d == $past(d_0, 1) &&
  e == $past(e_0, 1) &&
  f == $past(f_0, 1) &&
  g == $past(g_0, 1) &&
  h == $past(h_0, 1) &&
  i == 'sd0 &&
  rnd_cnt_reg == ('sd1 + $past(rnd_cnt_reg, 1)) &&
  rh_masking_rnd == $past(rh_masking_rnd_1, 1);
endproperty


CTRL_RND_to_SHA_Rounds_256_a: assert property (disable iff(!rst) CTRL_RND_to_SHA_Rounds_256_p);
property CTRL_RND_to_SHA_Rounds_256_p;
  CTRL_RND &&
  (('sd1 + rnd_cnt_reg) >= 'sd9) &&
  block_init &&
  (block_sha_mode == 'sd1)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H_2, 1) &&
  W == $past(W_1, 1) &&
  a == $past(a_2, 1) &&
  b == $past(b_1, 1) &&
  c == $past(c_1, 1) &&
  d == $past(d_1, 1) &&
  e == $past(e_1, 1) &&
  f == $past(f_1, 1) &&
  g == $past(g_1, 1) &&
  h == $past(h_1, 1) &&
  i == 'sd0 &&
  rnd_cnt_reg == ('sd1 + $past(rnd_cnt_reg, 1)) &&
  rh_masking_rnd == $past(rh_masking_rnd_1, 1);
endproperty


CTRL_RND_to_SHA_Rounds_512_a: assert property (disable iff(!rst) CTRL_RND_to_SHA_Rounds_512_p);
property CTRL_RND_to_SHA_Rounds_512_p;
  CTRL_RND &&
  (('sd1 + rnd_cnt_reg) >= 'sd9) &&
  block_init &&
  (block_sha_mode == 'sd3)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H_3, 1) &&
  W == $past(W_1, 1) &&
  a == $past(a_3, 1) &&
  b == $past(b_2, 1) &&
  c == $past(c_2, 1) &&
  d == $past(d_2, 1) &&
  e == $past(e_2, 1) &&
  f == $past(f_2, 1) &&
  g == $past(g_2, 1) &&
  h == $past(h_2, 1) &&
  i == 'sd0 &&
  rnd_cnt_reg == ('sd1 + $past(rnd_cnt_reg, 1)) &&
  rh_masking_rnd == $past(rh_masking_rnd_1, 1);
endproperty


CTRL_RND_to_SHA_Rounds_384_a: assert property (disable iff(!rst) CTRL_RND_to_SHA_Rounds_384_p);
property CTRL_RND_to_SHA_Rounds_384_p;
  CTRL_RND &&
  (('sd1 + rnd_cnt_reg) >= 'sd9) &&
  block_init &&
  (block_sha_mode != 'sd0) &&
  (block_sha_mode != 'sd1) &&
  (block_sha_mode != 'sd3)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H_4, 1) &&
  W == $past(W_1, 1) &&
  a == $past(a_4, 1) &&
  b == $past(b_3, 1) &&
  c == $past(c_3, 1) &&
  d == $past(d_3, 1) &&
  e == $past(e_3, 1) &&
  f == $past(f_3, 1) &&
  g == $past(g_3, 1) &&
  h == $past(h_3, 1) &&
  i == 'sd0 &&
  rnd_cnt_reg == ('sd1 + $past(rnd_cnt_reg, 1)) &&
  rh_masking_rnd == $past(rh_masking_rnd_1, 1);
endproperty


CTRL_RND_to_SHA_Rounds_next_a: assert property (disable iff(!rst) CTRL_RND_to_SHA_Rounds_next_p);
property CTRL_RND_to_SHA_Rounds_next_p;
  CTRL_RND &&
  (('sd1 + rnd_cnt_reg) >= 'sd9) &&
  !block_init
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H, 1) &&
  W == $past(W_1, 1) &&
  a == $past(a_5, 1) &&
  b == $past(b_4, 1) &&
  c == $past(c_4, 1) &&
  d == $past(d_4, 1) &&
  e == $past(e_4, 1) &&
  f == $past(f_4, 1) &&
  g == $past(g_4, 1) &&
  h == $past(h_4, 1) &&
  i == 'sd0 &&
  rnd_cnt_reg == ('sd1 + $past(rnd_cnt_reg, 1)) &&
  rh_masking_rnd == $past(rh_masking_rnd_1, 1);
endproperty


DONE_to_IDLE_a: assert property (disable iff(!rst) DONE_to_IDLE_p);
property DONE_to_IDLE_p;
  DONE
|->
  ##1
  IDLE &&
  H == $past(H_5, 1) &&
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
  digest_out == $past(compute_digest(H[64'd7], h.masked, h.random, H[64'd6], g.masked, g.random, H[64'd5], f.masked, f.random, H[64'd4], e.masked, e.random, H[64'd3], d.masked, d.random, H[64'd2], c.masked, c.random, H[64'd1], b.masked, b.random, H[64'd0], a.masked, a.random)) &&
  rnd_cnt_reg == $past(rnd_cnt_reg, 1) &&
  rh_masking_rnd == $past(rh_masking_rnd, 1) &&
  block_in_ready == 1 &&
  digest_valid == 1;
endproperty


IDLE_to_CTRL_RND_a: assert property (disable iff(!rst) IDLE_to_CTRL_RND_p);
property IDLE_to_CTRL_RND_p;
  IDLE &&
  block_in_valid
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
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
  rnd_cnt_reg == 'sd0 &&
  rh_masking_rnd == $past(rh_masking_rnd, 1);
endproperty


SHA_Rounds_to_DONE_a: assert property (disable iff(!rst) SHA_Rounds_to_DONE_p);
property SHA_Rounds_to_DONE_p;
  SHA_Rounds &&
  (i >= 'sd16) &&
  (('sd1 + i) >= 'sd80)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  DONE &&
  H == $past(H, 1) &&
  W == $past(W_2, 1) &&
  a == $past(a_7, 1) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == $past(e_6, 1) &&
  f == $past(e, 1) &&
  g == $past(f, 1) &&
  h == $past(g, 1) &&
  i == ('sd1 + $past(i, 1)) &&
  rnd_cnt_reg == $past(rnd_cnt_reg, 1) &&
  rh_masking_rnd == $past(rh_masking_rnd, 1);
endproperty


SHA_Rounds_to_SHA_Rounds_before_16_a: assert property (disable iff(!rst) SHA_Rounds_to_SHA_Rounds_before_16_p);
property SHA_Rounds_to_SHA_Rounds_before_16_p;
  SHA_Rounds &&
  (i < 'sd16) &&
  (('sd1 + i) < 'sd80)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H, 1) &&
  W == $past(W, 1) &&
  a == $past(a_6, 1) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == $past(e_5, 1) &&
  f == $past(e, 1) &&
  g == $past(f, 1) &&
  h == $past(g, 1) &&
  i == ('sd1 + $past(i, 1)) &&
  rnd_cnt_reg == $past(rnd_cnt_reg, 1) &&
  rh_masking_rnd == $past(rh_masking_rnd, 1);
endproperty


SHA_Rounds_to_SHA_Rounds_after_16_a: assert property (disable iff(!rst) SHA_Rounds_to_SHA_Rounds_after_16_p);
property SHA_Rounds_to_SHA_Rounds_after_16_p;
  SHA_Rounds &&
  (i >= 'sd16) &&
  (('sd1 + i) < 'sd80)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H == $past(H, 1) &&
  W == $past(W_2, 1) &&
  a == $past(a_7, 1) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == $past(e_6, 1) &&
  f == $past(e, 1) &&
  g == $past(f, 1) &&
  h == $past(g, 1) &&
  i == ('sd1 + $past(i, 1)) &&
  rnd_cnt_reg == $past(rnd_cnt_reg, 1) &&
  rh_masking_rnd == $past(rh_masking_rnd, 1);
endproperty


IDLE_wait_a: assert property (disable iff(!rst) IDLE_wait_p);
property IDLE_wait_p;
  IDLE &&
  !block_in_valid
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
  rnd_cnt_reg == $past(rnd_cnt_reg, 1) &&
  rh_masking_rnd == $past(rh_masking_rnd, 1) &&
  block_in_ready == 1 &&
  digest_valid == $past(digest_valid);
endproperty


endmodule


module fv_SHA512_masked_wrapper_m;


default clocking default_clk @(posedge (sha512_masked_core.clk)); endclocking


st_SHA_Args sha_in_struct = '{
  in:        (sha512_masked_core.block_msg),
  SHA_Mode:  (sha512_masked_core.mode),
  init_cmd:  (sha512_masked_core.init_cmd),
  next_cmd:  (sha512_masked_core.next_cmd),
  zeroize:   (sha512_masked_core.zeroize)
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
a_sc_big_unsigned_64_16 W = '{
  0: (sha512_masked_core.w_mem_inst.w_mem[00]),
  1: (sha512_masked_core.w_mem_inst.w_mem[01]),
  2: (sha512_masked_core.w_mem_inst.w_mem[02]),
  3: (sha512_masked_core.w_mem_inst.w_mem[03]),
  4: (sha512_masked_core.w_mem_inst.w_mem[04]),
  5: (sha512_masked_core.w_mem_inst.w_mem[05]),
  6: (sha512_masked_core.w_mem_inst.w_mem[06]),
  7: (sha512_masked_core.w_mem_inst.w_mem[07]),
  8: (sha512_masked_core.w_mem_inst.w_mem[08]),
  9: (sha512_masked_core.w_mem_inst.w_mem[09]),
  10: (sha512_masked_core.w_mem_inst.w_mem[10]),
  11: (sha512_masked_core.w_mem_inst.w_mem[11]),
  12: (sha512_masked_core.w_mem_inst.w_mem[12]),
  13: (sha512_masked_core.w_mem_inst.w_mem[13]),
  14: (sha512_masked_core.w_mem_inst.w_mem[14]),
  15: (sha512_masked_core.w_mem_inst.w_mem[15])
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
a_sc_big_unsigned_64_8 rh_masking_rnd = '{
  0: (sha512_masked_core.rh_masking_rnd[0]),
  1: (sha512_masked_core.rh_masking_rnd[1]),
  2: (sha512_masked_core.rh_masking_rnd[2]),
  3: (sha512_masked_core.rh_masking_rnd[3]),
  4: (sha512_masked_core.rh_masking_rnd[4]),
  5: (sha512_masked_core.rh_masking_rnd[5]),
  6: (sha512_masked_core.rh_masking_rnd[6]),
  7: (sha512_masked_core.rh_masking_rnd[7])
};


fv_sha512_masked_m fv_sha512_masked(
  .rst((sha512_masked_core.reset_n)  && !(sha512_masked_core.zeroize)),
  .clk(sha512_masked_core.clk),

  // Inputs
  .sha_in_struct(sha_in_struct),
  .lfsr_in(sha512_masked_core.lfsr_inst.rnd),

  // Outputs
  .digest_out(sha512_masked_core.digest),

  // Valid signals
  .block_in_valid(((sha512_masked_core.init_cmd) || (sha512_masked_core.next_cmd))),
  .digest_valid(sha512_masked_core.digest_valid),

  // Ready signals
  .block_in_ready(sha512_masked_core.ready),

  // Registers
  .H(H),
  .block_sha_mode(sha512_masked_core.mode),
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
  .block_init(sha512_masked_core.init_reg),
  .lfsr_rnd(sha512_masked_core.lfsr_rnd),
  .rnd_cnt_reg(sha512_masked_core.rnd_ctr_reg),
  .rh_masking_rnd(rh_masking_rnd),

  // States
  .IDLE(sha512_masked_core.sha512_ctrl_reg==2'h0),
  .CTRL_RND(sha512_masked_core.sha512_ctrl_reg==2'h1),
  .SHA_Rounds(sha512_masked_core.sha512_ctrl_reg==2'h2),
  .DONE(sha512_masked_core.sha512_ctrl_reg==2'h3)
);


endmodule


bind sha512_masked_core fv_SHA512_masked_wrapper_m fv_SHA512_masked_wrapper();
