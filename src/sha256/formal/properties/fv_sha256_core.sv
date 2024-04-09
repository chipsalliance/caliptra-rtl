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

import fv_sha256_core_pkg::*;

module fv_sha_256_core_m(
  input bit rst,
  input bit clk,
  input bit unsigned [31:0] digest_out_0,
  input bit unsigned [31:0] digest_out_1,
  input bit unsigned [31:0] digest_out_2,
  input bit unsigned [31:0] digest_out_3,
  input bit unsigned [31:0] digest_out_4,
  input bit unsigned [31:0] digest_out_5,
  input bit unsigned [31:0] digest_out_6,
  input bit unsigned [31:0] digest_out_7,
  input bit block_init,
  input bit block_mode,
  input bit block_next,
  input bit unsigned [31:0] block_in_0,
  input bit unsigned [31:0] block_in_1,
  input bit unsigned [31:0] block_in_2,
  input bit unsigned [31:0] block_in_3,
  input bit unsigned [31:0] block_in_4,
  input bit unsigned [31:0] block_in_5,
  input bit unsigned [31:0] block_in_6,
  input bit unsigned [31:0] block_in_7,
  input bit unsigned [31:0] block_in_8,
  input bit unsigned [31:0] block_in_9,
  input bit unsigned [31:0] block_in_10,
  input bit unsigned [31:0] block_in_11,
  input bit unsigned [31:0] block_in_12,
  input bit unsigned [31:0] block_in_13,
  input bit unsigned [31:0] block_in_14,
  input bit unsigned [31:0] block_in_15,
  input bit block_zeroize,
  input bit block_in_valid,
  input bit digest_valid,
  input bit block_in_ready,
  input bit unsigned [5:0] i,
  input bit unsigned [31:0] W_0,
  input bit unsigned [31:0] W_1,
  input bit unsigned [31:0] W_2,
  input bit unsigned [31:0] W_3,
  input bit unsigned [31:0] W_4,
  input bit unsigned [31:0] W_5,
  input bit unsigned [31:0] W_6,
  input bit unsigned [31:0] W_7,
  input bit unsigned [31:0] W_8,
  input bit unsigned [31:0] W_9,
  input bit unsigned [31:0] W_10,
  input bit unsigned [31:0] W_11,
  input bit unsigned [31:0] W_12,
  input bit unsigned [31:0] W_13,
  input bit unsigned [31:0] W_14,
  input bit unsigned [31:0] W_15,
  input bit unsigned [31:0] H_0,
  input bit unsigned [31:0] H_1,
  input bit unsigned [31:0] H_2,
  input bit unsigned [31:0] H_3,
  input bit unsigned [31:0] H_4,
  input bit unsigned [31:0] H_5,
  input bit unsigned [31:0] H_6,
  input bit unsigned [31:0] H_7,
  input bit unsigned [31:0] a,
  input bit unsigned [31:0] b,
  input bit unsigned [31:0] c,
  input bit unsigned [31:0] d,
  input bit unsigned [31:0] e,
  input bit unsigned [31:0] f,
  input bit unsigned [31:0] g,
  input bit unsigned [31:0] h,
  input bit idle,
  input bit ctrl_rotationss,
  input bit ctrl_done
);


default clocking default_clk @(posedge clk); endclocking
logic [15:0][31:0] w;
logic [3:0] j;

assign j = i[3:0];
assign w = {W_15,W_14,W_13,W_12,W_11,W_10,W_9,W_8,W_7,W_6,W_5,W_4,W_3,W_2,W_1,W_0};

sequence reset_sequence;
  !rst ##1 rst;
endsequence


reset_a: assert property (reset_p);
property reset_p;
  reset_sequence |->
  idle &&
  i == 'sd0 &&
  W_0 == 0 &&
  W_10 == 0 &&
  W_11 == 0 &&
  W_12 == 0 &&
  W_13 == 0 &&
  W_14 == 0 &&
  W_15 == 0 &&
  W_1 == 0 &&
  W_2 == 0 &&
  W_3 == 0 &&
  W_4 == 0 &&
  W_5 == 0 &&
  W_6 == 0 &&
  W_7 == 0 &&
  W_8 == 0 &&
  W_9 == 0 &&
  H_0 == 0 &&
  H_1 == 0 &&
  H_2 == 0 &&
  H_3 == 0 &&
  H_4 == 0 &&
  H_5 == 0 &&
  H_6 == 0 &&
  H_7 == 0 &&
  a == 0 &&
  b == 0 &&
  c == 0 &&
  d == 0 &&
  e == 0 &&
  f == 0 &&
  g == 0 &&
  h == 0 &&
  digest_valid == 0 &&
  block_in_ready == 1;
endproperty


DONE_to_IDLE_a: assert property (disable iff(!rst) DONE_to_IDLE_p);
property DONE_to_IDLE_p;
  ctrl_done
|->
  ##1
  idle &&
  digest_out_0 == ($past(a, 1) + $past(H_0, 1)) &&
  digest_out_1 == ($past(b, 1) + $past(H_1, 1)) &&
  digest_out_2 == ($past(c, 1) + $past(H_2, 1)) &&
  digest_out_3 == ($past(d, 1) + $past(H_3, 1)) &&
  digest_out_4 == ($past(e, 1) + $past(H_4, 1)) &&
  digest_out_5 == ($past(f, 1) + $past(H_5, 1)) &&
  digest_out_6 == ($past(g, 1) + $past(H_6, 1)) &&
  digest_out_7 == ($past(h, 1) + $past(H_7, 1)) &&
  i == $past(i, 1) &&
  W_0 == $past(W_0, 1) &&
  W_10 == $past(W_10, 1) &&
  W_11 == $past(W_11, 1) &&
  W_12 == $past(W_12, 1) &&
  W_13 == $past(W_13, 1) &&
  W_14 == $past(W_14, 1) &&
  W_15 == $past(W_15, 1) &&
  W_1 == $past(W_1, 1) &&
  W_2 == $past(W_2, 1) &&
  W_3 == $past(W_3, 1) &&
  W_4 == $past(W_4, 1) &&
  W_5 == $past(W_5, 1) &&
  W_6 == $past(W_6, 1) &&
  W_7 == $past(W_7, 1) &&
  W_8 == $past(W_8, 1) &&
  W_9 == $past(W_9, 1) &&
  H_0 == ($past(a, 1) + $past(H_0, 1)) &&
  H_1 == ($past(b, 1) + $past(H_1, 1)) &&
  H_2 == ($past(c, 1) + $past(H_2, 1)) &&
  H_3 == ($past(d, 1) + $past(H_3, 1)) &&
  H_4 == ($past(e, 1) + $past(H_4, 1)) &&
  H_5 == ($past(f, 1) + $past(H_5, 1)) &&
  H_6 == ($past(g, 1) + $past(H_6, 1)) &&
  H_7 == ($past(h, 1) + $past(H_7, 1)) &&
  a == $past(a, 1) &&
  b == $past(b, 1) &&
  c == $past(c, 1) &&
  d == $past(d, 1) &&
  e == $past(e, 1) &&
  f == $past(f, 1) &&
  g == $past(g, 1) &&
  h == $past(h, 1) &&
  digest_valid == 1 &&
  block_in_ready == 1;
endproperty


SHA_Rounds_to_DONE_a: assert property (disable iff(!rst) SHA_Rounds_to_DONE_p);
property SHA_Rounds_to_DONE_p;
  ctrl_rotationss &&
  (i >= 'sd16) &&
  (('sd1 + i) >= 'sd64)
|->
  ##1 (digest_valid == 0) and
  ##1 (block_in_ready == 0) and
  ##1
  ctrl_done &&
  i == 'sd0 &&
  W_0 == $past(W_1, 1) &&
  W_10 == $past(W_11, 1) &&
  W_11 == $past(W_12, 1) &&
  W_12 == $past(W_13, 1) &&
  W_13 == $past(W_14, 1) &&
  W_14 == $past(W_15, 1) &&
  W_15 == $past(compute_w(W_14,W_9,W_1,W_0)) &&
  W_1 == $past(W_2, 1) &&
  W_2 == $past(W_3, 1) &&
  W_3 == $past(W_4, 1) &&
  W_4 == $past(W_5, 1) &&
  W_5 == $past(W_6, 1) &&
  W_6 == $past(W_7, 1) &&
  W_7 == $past(W_8, 1) &&
  W_8 == $past(W_9, 1) &&
  W_9 == $past(W_10, 1) &&
  H_0 == $past(H_0, 1) &&
  H_1 == $past(H_1, 1) &&
  H_2 == $past(H_2, 1) &&
  H_3 == $past(H_3, 1) &&
  H_4 == $past(H_4, 1) &&
  H_5 == $past(H_5, 1) &&
  H_6 == $past(H_6, 1) &&
  H_7 == $past(H_7, 1) &&
  a == $past(newa(mult_xor(a, 2, 13, 22),majority(a,b,c),Summ(compute_w(W_14,W_9,W_1,W_0),K[i],h,choose(e,f,g),mult_xor(e, 6, 11, 25)))) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == $past(newe(d,Summ(compute_w(W_14,W_9,W_1,W_0),K[i],h,choose(e,f,g),mult_xor(e,6,11,25)))) &&
  f == $past(e, 1) &&
  g == $past(f, 1) &&
  h == $past(g, 1);
endproperty


SHA_Rounds_to_SHA_Rounds_before_16_a: assert property (disable iff(!rst) SHA_Rounds_to_SHA_Rounds_before_16_p);
property SHA_Rounds_to_SHA_Rounds_before_16_p;
  ctrl_rotationss &&
  (i < 'sd16)
|->
  ##1 (digest_valid == 0) and
  ##1 (block_in_ready == 0) and
  ##1
  ctrl_rotationss &&
  i == ('sd1 + $past(i, 1)) &&
  W_0 == $past(W_0, 1) &&
  W_10 == $past(W_10, 1) &&
  W_11 == $past(W_11, 1) &&
  W_12 == $past(W_12, 1) &&
  W_13 == $past(W_13, 1) &&
  W_14 == $past(W_14, 1) &&
  W_15 == $past(W_15, 1) &&
  W_1 == $past(W_1, 1) &&
  W_2 == $past(W_2, 1) &&
  W_3 == $past(W_3, 1) &&
  W_4 == $past(W_4, 1) &&
  W_5 == $past(W_5, 1) &&
  W_6 == $past(W_6, 1) &&
  W_7 == $past(W_7, 1) &&
  W_8 == $past(W_8, 1) &&
  W_9 == $past(W_9, 1) &&
  H_0 == $past(H_0, 1) &&
  H_1 == $past(H_1, 1) &&
  H_2 == $past(H_2, 1) &&
  H_3 == $past(H_3, 1) &&
  H_4 == $past(H_4, 1) &&
  H_5 == $past(H_5, 1) &&
  H_6 == $past(H_6, 1) &&
  H_7 == $past(H_7, 1) &&
  a == $past(newa(mult_xor(a, 2, 13, 22),majority(a,b,c),Summ(w[j],K[i],h,choose(e,f,g),mult_xor(e, 6, 11, 25)))) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == $past(newe(d,Summ(w[j],K[i],h,choose(e,f,g),mult_xor(e,6,11,25)))) &&
  f == $past(e, 1) &&
  g == $past(f, 1) &&
  h == $past(g, 1);
endproperty


SHA_Rounds_to_SHA_Rounds_after_16_a: assert property (disable iff(!rst) SHA_Rounds_to_SHA_Rounds_after_16_p);
property SHA_Rounds_to_SHA_Rounds_after_16_p;
  ctrl_rotationss &&
  (i >= 'sd16) &&
  (('sd1 + i) < 'sd64)
|->
  ##1 (digest_valid == 0) and
  ##1 (block_in_ready == 0) and
  ##1
  ctrl_rotationss &&
  i == ('sd1 + $past(i, 1)) &&
  W_0 == $past(W_1, 1) &&
  W_10 == $past(W_11, 1) &&
  W_11 == $past(W_12, 1) &&
  W_12 == $past(W_13, 1) &&
  W_13 == $past(W_14, 1) &&
  W_14 == $past(W_15, 1) &&
  W_15 == $past(compute_w(W_14,W_9,W_1,W_0)) &&
  W_1 == $past(W_2, 1) &&
  W_2 == $past(W_3, 1) &&
  W_3 == $past(W_4, 1) &&
  W_4 == $past(W_5, 1) &&
  W_5 == $past(W_6, 1) &&
  W_6 == $past(W_7, 1) &&
  W_7 == $past(W_8, 1) &&
  W_8 == $past(W_9, 1) &&
  W_9 == $past(W_10, 1) &&
  H_0 == $past(H_0, 1) &&
  H_1 == $past(H_1, 1) &&
  H_2 == $past(H_2, 1) &&
  H_3 == $past(H_3, 1) &&
  H_4 == $past(H_4, 1) &&
  H_5 == $past(H_5, 1) &&
  H_6 == $past(H_6, 1) &&
  H_7 == $past(H_7, 1) &&
  a == $past(newa(mult_xor(a, 2, 13, 22),majority(a,b,c),Summ(compute_w(W_14,W_9,W_1,W_0),K[i],h,choose(e,f,g),mult_xor(e, 6, 11, 25)))) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == $past(newe(d,Summ(compute_w(W_14,W_9,W_1,W_0),K[i],h,choose(e,f,g),mult_xor(e,6,11,25)))) &&
  f == $past(e, 1) &&
  g == $past(f, 1) &&
  h == $past(g, 1);
endproperty


IDLE_to_SHA_Rounds_224_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_224_p);
property IDLE_to_SHA_Rounds_224_p;
  idle &&
  block_in_valid &&
  block_init &&
  !block_mode
|->
  ##1 (digest_valid == 0) and
  ##1 (block_in_ready == 0) and
  ##1
  ctrl_rotationss &&
  i == 'sd0 &&
  W_0 == $past(block_in_15, 1) &&
  W_10 == $past(block_in_5, 1) &&
  W_11 == $past(block_in_4, 1) &&
  W_12 == $past(block_in_3, 1) &&
  W_13 == $past(block_in_2, 1) &&
  W_14 == $past(block_in_1, 1) &&
  W_15 == $past(block_in_0, 1) &&
  W_1 == $past(block_in_14, 1) &&
  W_2 == $past(block_in_13, 1) &&
  W_3 == $past(block_in_12, 1) &&
  W_4 == $past(block_in_11, 1) &&
  W_5 == $past(block_in_10, 1) &&
  W_6 == $past(block_in_9, 1) &&
  W_7 == $past(block_in_8, 1) &&
  W_8 == $past(block_in_7, 1) &&
  W_9 == $past(block_in_6, 1) &&
  H_0 == 32'd3238371032 &&
  H_1 == 32'd914150663 &&
  H_2 == 32'd812702999 &&
  H_3 == 32'd4144912697 &&
  H_4 == 32'd4290775857 &&
  H_5 == 32'd1750603025 &&
  H_6 == 32'd1694076839 &&
  H_7 == 32'd3204075428 &&
  a == 32'd3238371032 &&
  b == 32'd914150663 &&
  c == 32'd812702999 &&
  d == 32'd4144912697 &&
  e == 32'd4290775857 &&
  f == 32'd1750603025 &&
  g == 32'd1694076839 &&
  h == 32'd3204075428;
endproperty


IDLE_to_SHA_Rounds_256_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_256_p);
property IDLE_to_SHA_Rounds_256_p;
  idle &&
  block_in_valid &&
  block_init &&
  block_mode
|->
  ##1 (digest_valid == 0) and
  ##1 (block_in_ready == 0) and
  ##1
  ctrl_rotationss &&
  i == 'sd0 &&
  W_0 == $past(block_in_15, 1) &&
  W_10 == $past(block_in_5, 1) &&
  W_11 == $past(block_in_4, 1) &&
  W_12 == $past(block_in_3, 1) &&
  W_13 == $past(block_in_2, 1) &&
  W_14 == $past(block_in_1, 1) &&
  W_15 == $past(block_in_0, 1) &&
  W_1 == $past(block_in_14, 1) &&
  W_2 == $past(block_in_13, 1) &&
  W_3 == $past(block_in_12, 1) &&
  W_4 == $past(block_in_11, 1) &&
  W_5 == $past(block_in_10, 1) &&
  W_6 == $past(block_in_9, 1) &&
  W_7 == $past(block_in_8, 1) &&
  W_8 == $past(block_in_7, 1) &&
  W_9 == $past(block_in_6, 1) &&
  H_0 == 32'd1779033703 &&
  H_1 == 32'd3144134277 &&
  H_2 == 32'd1013904242 &&
  H_3 == 32'd2773480762 &&
  H_4 == 32'd1359893119 &&
  H_5 == 32'd2600822924 &&
  H_6 == 32'd528734635 &&
  H_7 == 32'd1541459225 &&
  a == 32'd1779033703 &&
  b == 32'd3144134277 &&
  c == 32'd1013904242 &&
  d == 32'd2773480762 &&
  e == 32'd1359893119 &&
  f == 32'd2600822924 &&
  g == 32'd528734635 &&
  h == 32'd1541459225;
endproperty


IDLE_to_SHA_Rounds_next_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_next_p);
property IDLE_to_SHA_Rounds_next_p;
  idle &&
  block_in_valid &&
  !block_init
|->
  ##1 (digest_valid == 0) and
  ##1 (block_in_ready == 0) and
  ##1
  ctrl_rotationss &&
  i == 'sd0 &&
  W_0 == $past(block_in_15, 1) &&
  W_10 == $past(block_in_5, 1) &&
  W_11 == $past(block_in_4, 1) &&
  W_12 == $past(block_in_3, 1) &&
  W_13 == $past(block_in_2, 1) &&
  W_14 == $past(block_in_1, 1) &&
  W_15 == $past(block_in_0, 1) &&
  W_1 == $past(block_in_14, 1) &&
  W_2 == $past(block_in_13, 1) &&
  W_3 == $past(block_in_12, 1) &&
  W_4 == $past(block_in_11, 1) &&
  W_5 == $past(block_in_10, 1) &&
  W_6 == $past(block_in_9, 1) &&
  W_7 == $past(block_in_8, 1) &&
  W_8 == $past(block_in_7, 1) &&
  W_9 == $past(block_in_6, 1) &&
  H_0 == $past(H_0, 1) &&
  H_1 == $past(H_1, 1) &&
  H_2 == $past(H_2, 1) &&
  H_3 == $past(H_3, 1) &&
  H_4 == $past(H_4, 1) &&
  H_5 == $past(H_5, 1) &&
  H_6 == $past(H_6, 1) &&
  H_7 == $past(H_7, 1) &&
  a == $past(H_0, 1) &&
  b == $past(H_1, 1) &&
  c == $past(H_2, 1) &&
  d == $past(H_3, 1) &&
  e == $past(H_4, 1) &&
  f == $past(H_5, 1) &&
  g == $past(H_6, 1) &&
  h == $past(H_7, 1);
endproperty


idle_wait_a: assert property (disable iff(!rst) idle_wait_p);
property idle_wait_p;
  idle &&
  !block_in_valid
|->
  ##1
  idle &&
  i == $past(i, 1) &&
  W_0 == $past(W_0, 1) &&
  W_10 == $past(W_10, 1) &&
  W_11 == $past(W_11, 1) &&
  W_12 == $past(W_12, 1) &&
  W_13 == $past(W_13, 1) &&
  W_14 == $past(W_14, 1) &&
  W_15 == $past(W_15, 1) &&
  W_1 == $past(W_1, 1) &&
  W_2 == $past(W_2, 1) &&
  W_3 == $past(W_3, 1) &&
  W_4 == $past(W_4, 1) &&
  W_5 == $past(W_5, 1) &&
  W_6 == $past(W_6, 1) &&
  W_7 == $past(W_7, 1) &&
  W_8 == $past(W_8, 1) &&
  W_9 == $past(W_9, 1) &&
  H_0 == $past(H_0, 1) &&
  H_1 == $past(H_1, 1) &&
  H_2 == $past(H_2, 1) &&
  H_3 == $past(H_3, 1) &&
  H_4 == $past(H_4, 1) &&
  H_5 == $past(H_5, 1) &&
  H_6 == $past(H_6, 1) &&
  H_7 == $past(H_7, 1) &&
  a == $past(a, 1) &&
  b == $past(b, 1) &&
  c == $past(c, 1) &&
  d == $past(d, 1) &&
  e == $past(e, 1) &&
  f == $past(f, 1) &&
  g == $past(g, 1) &&
  h == $past(h, 1) &&
  digest_valid == $past(digest_valid) &&
  block_in_ready == 1;
endproperty


endmodule



bind sha256_core fv_sha_256_core_m fv_sha256_core(
  .rst(sha256_core.reset_n && !sha256_core.zeroize),
  .clk(sha256_core.clk),
  .digest_out_0(sha256_core.digest [255:224]),
  .digest_out_1(sha256_core.digest [223:192]),
  .digest_out_2(sha256_core.digest [191:160]),
  .digest_out_3(sha256_core.digest [159:128]),
  .digest_out_4(sha256_core.digest [127:96]),
  .digest_out_5(sha256_core.digest [95:64]),
  .digest_out_6(sha256_core.digest [63:32]),
  .digest_out_7(sha256_core.digest [31:0]),
  .block_init(sha256_core.init_cmd),
  .block_mode(sha256_core.mode),
  .block_next(sha256_core.next_cmd),
  .block_in_0(sha256_core.block_msg[31:0]),
  .block_in_1(sha256_core.block_msg[63:32]),
  .block_in_2(sha256_core.block_msg[95:64]),
  .block_in_3(sha256_core.block_msg[127:96]),
  .block_in_4(sha256_core.block_msg[159:128]),
  .block_in_5(sha256_core.block_msg[191:160]),
  .block_in_6(sha256_core.block_msg[223:192]),
  .block_in_7(sha256_core.block_msg[255:224]),
  .block_in_8(sha256_core.block_msg[287:256]),
  .block_in_9(sha256_core.block_msg[319:288]),
  .block_in_10(sha256_core.block_msg[351:320]),
  .block_in_11(sha256_core.block_msg[383:352]),
  .block_in_12(sha256_core.block_msg[415:384]),
  .block_in_13(sha256_core.block_msg[447:416]),
  .block_in_14(sha256_core.block_msg[479:448]),
  .block_in_15(sha256_core.block_msg[511:480]),
  .block_zeroize(sha256_core.zeroize),
  .block_in_valid((sha256_core.init_cmd) || (sha256_core.next_cmd)),
  .digest_valid(sha256_core.digest_valid),
  .block_in_ready(sha256_core.ready),
  .i(sha256_core.t_ctr_reg),
  .W_0(sha256_core.w_mem_inst.w_mem[00]),
  .W_1(sha256_core.w_mem_inst.w_mem[01]),
  .W_2(sha256_core.w_mem_inst.w_mem[02]),
  .W_3(sha256_core.w_mem_inst.w_mem[03]),
  .W_4(sha256_core.w_mem_inst.w_mem[04]),
  .W_5(sha256_core.w_mem_inst.w_mem[05]),
  .W_6(sha256_core.w_mem_inst.w_mem[06]),
  .W_7(sha256_core.w_mem_inst.w_mem[07]),
  .W_8(sha256_core.w_mem_inst.w_mem[08]),
  .W_9(sha256_core.w_mem_inst.w_mem[09]),
  .W_10(sha256_core.w_mem_inst.w_mem[10]),
  .W_11(sha256_core.w_mem_inst.w_mem[11]),
  .W_12(sha256_core.w_mem_inst.w_mem[12]),
  .W_13(sha256_core.w_mem_inst.w_mem[13]),
  .W_14(sha256_core.w_mem_inst.w_mem[14]),
  .W_15(sha256_core.w_mem_inst.w_mem[15]),
  .H_0(sha256_core.H0_reg),
  .H_1(sha256_core.H1_reg),
  .H_2(sha256_core.H2_reg),
  .H_3(sha256_core.H3_reg),
  .H_4(sha256_core.H4_reg),
  .H_5(sha256_core.H5_reg),
  .H_6(sha256_core.H6_reg),
  .H_7(sha256_core.H7_reg),
  .a(sha256_core.a_reg),
  .b(sha256_core.b_reg),
  .c(sha256_core.c_reg),
  .d(sha256_core.d_reg),
  .e(sha256_core.e_reg),
  .f(sha256_core.f_reg),
  .g(sha256_core.g_reg),
  .h(sha256_core.h_reg),
  .idle(sha256_core.sha256_ctrl_reg==2'h0),
  .ctrl_rotationss(sha256_core.sha256_ctrl_reg==2'h1),
  .ctrl_done(sha256_core.sha256_ctrl_reg==2'h2)
);
