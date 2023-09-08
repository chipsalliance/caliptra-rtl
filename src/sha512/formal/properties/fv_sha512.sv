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

import fv_sha512_pkg::*;


module fv_sha_512_m(
  input bit rst,
  input bit clk,
  input bit unsigned [1023:0] block_in,
  input bit signed [31:0] block_sha_mode,
  input bit block_init,
  input bit block_next,
  input bit block_zeroize,
  input bit unsigned [511:0] digest_out,
  input bit block_in_valid,
  input bit block_in_ready,
  input bit digest_valid,
  input bit unsigned [63:0] H_0,
  input bit unsigned [63:0] H_1,
  input bit unsigned [63:0] H_2,
  input bit unsigned [63:0] H_3,
  input bit unsigned [63:0] H_4,
  input bit unsigned [63:0] H_5,
  input bit unsigned [63:0] H_6,
  input bit unsigned [63:0] H_7,
  input bit unsigned [63:0] W_0,
  input bit unsigned [63:0] W_1,
  input bit unsigned [63:0] W_2,
  input bit unsigned [63:0] W_3,
  input bit unsigned [63:0] W_4,
  input bit unsigned [63:0] W_5,
  input bit unsigned [63:0] W_6,
  input bit unsigned [63:0] W_7,
  input bit unsigned [63:0] W_8,
  input bit unsigned [63:0] W_9,
  input bit unsigned [63:0] W_10,
  input bit unsigned [63:0] W_11,
  input bit unsigned [63:0] W_12,
  input bit unsigned [63:0] W_13,
  input bit unsigned [63:0] W_14,
  input bit unsigned [63:0] W_15,
  input bit unsigned [63:0] a,
  input bit unsigned [63:0] b,
  input bit unsigned [63:0] c,
  input bit unsigned [63:0] d,
  input bit unsigned [63:0] e,
  input bit unsigned [63:0] f,
  input bit unsigned [63:0] g,
  input bit unsigned [63:0] h,
  input bit unsigned [6:0] i,
  input bit IDLE,
  input bit SHA_Rounds,
  input bit DONE
);


default clocking default_clk @(posedge clk); endclocking

logic [15:0][63:0] W;
logic [3:0] j;

assign j = i[3:0];
assign W = {W_15,W_14,W_13,W_12,W_11,W_10,W_9,W_8,W_7,W_6,W_5,W_4,W_3,W_2,W_1,W_0};


sequence reset_sequence;
  !rst ##1 rst;
endsequence


reset_a: assert property (reset_p);
property reset_p;
  reset_sequence |->
  IDLE &&
  H_0 == 64'd0 &&
  H_1 == 64'd0 &&
  H_2 == 64'd0 &&
  H_3 == 64'd0 &&
  H_4 == 64'd0 &&
  H_5 == 64'd0 &&
  H_6 == 64'd0 &&
  H_7 == 64'd0 &&
  W_0 == 64'd0 &&
  W_10 == 64'd0 &&
  W_11 == 64'd0 &&
  W_12 == 64'd0 &&
  W_13 == 64'd0 &&
  W_14 == 64'd0 &&
  W_15 == 64'd0 &&
  W_1 == 64'd0 &&
  W_2 == 64'd0 &&
  W_3 == 64'd0 &&
  W_4 == 64'd0 &&
  W_5 == 64'd0 &&
  W_6 == 64'd0 &&
  W_7 == 64'd0 &&
  W_8 == 64'd0 &&
  W_9 == 64'd0 &&
  a == 64'd0 &&
  b == 64'd0 &&
  c == 64'd0 &&
  d == 64'd0 &&
  e == 64'd0 &&
  f == 64'd0 &&
  g == 64'd0 &&
  h == 64'd0 &&
  i == 'sd0 &&
  block_in_ready == 1 &&
  digest_valid == 0;
endproperty


DONE_to_IDLE_a: assert property (disable iff(!rst) DONE_to_IDLE_p);
property DONE_to_IDLE_p;
  DONE
|->
  ##1
  IDLE &&
  H_0 == 64'(($past(H_0, 1) + $past(a, 1))) &&
  H_1 == 64'(($past(H_1, 1) + $past(b, 1))) &&
  H_2 == 64'(($past(H_2, 1) + $past(c, 1))) &&
  H_3 == 64'(($past(H_3, 1) + $past(d, 1))) &&
  H_4 == 64'(($past(H_4, 1) + $past(e, 1))) &&
  H_5 == 64'(($past(H_5, 1) + $past(f, 1))) &&
  H_6 == 64'(($past(H_6, 1) + $past(g, 1))) &&
  H_7 == 64'(($past(H_7, 1) + $past(h, 1))) &&
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
  a == $past(a, 1) &&
  b == $past(b, 1) &&
  c == $past(c, 1) &&
  d == $past(d, 1) &&
  e == $past(e, 1) &&
  f == $past(f, 1) &&
  g == $past(g, 1) &&
  h == $past(h, 1) &&
  i == $past(i, 1) &&
  digest_out == $past(compute_digest(H_7,h,H_6,g,H_5,f,H_4,e,H_3,d,H_2,c,H_1,b,H_0,a)) &&
  block_in_ready == 1 &&
  digest_valid == 1;
endproperty


IDLE_to_SHA_Rounds_224_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_224_p);
property IDLE_to_SHA_Rounds_224_p;
  IDLE &&
  block_in_valid &&
  block_init &&
  (block_sha_mode == 'sd224)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H_0 == 64'd10105294471447203234 &&
  H_1 == 64'd8350123849800275158 &&
  H_2 == 64'd2160240930085379202 &&
  H_3 == 64'd7466358040605728719 &&
  H_4 == 64'd1111592415079452072 &&
  H_5 == 64'd8638871050018654530 &&
  H_6 == 64'd4583966954114332360 &&
  H_7 == 64'd1230299281376055969 &&
  W_0 == slicer($past(block_in, 1), 32'sd15) &&
  W_10 == slicer($past(block_in, 1),32'sd5) &&
  W_11 == slicer($past(block_in, 1),32'sd4) &&
  W_12 == slicer($past(block_in, 1),32'sd3) &&
  W_13 == slicer($past(block_in, 1),32'sd2) &&
  W_14 == slicer($past(block_in, 1),32'sd1) &&
  W_15 == slicer($past(block_in, 1),32'sd0) &&
  W_1 == slicer($past(block_in, 1), 32'sd14) &&
  W_2 == slicer($past(block_in, 1), 32'sd13) &&
  W_3 == slicer($past(block_in, 1), 32'sd12) &&
  W_4 == slicer($past(block_in, 1), 32'sd11) &&
  W_5 == slicer($past(block_in, 1), 32'sd10) &&
  W_6 == slicer($past(block_in, 1), 32'sd9) &&
  W_7 == slicer($past(block_in, 1), 32'sd8) &&
  W_8 == slicer($past(block_in, 1), 32'sd7) &&
  W_9 == slicer($past(block_in, 1), 32'sd6) &&
  a == 64'd10105294471447203234 &&
  b == 64'd8350123849800275158 &&
  c == 64'd2160240930085379202 &&
  d == 64'd7466358040605728719 &&
  e == 64'd1111592415079452072 &&
  f == 64'd8638871050018654530 &&
  g == 64'd4583966954114332360 &&
  h == 64'd1230299281376055969 &&
  i == 'sd0;
endproperty


IDLE_to_SHA_Rounds_256_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_256_p);
property IDLE_to_SHA_Rounds_256_p;
  IDLE &&
  block_in_valid &&
  block_init &&
  (block_sha_mode == 'sd256)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H_0 == 64'd2463787394917988140 &&
  H_1 == 64'd11481187982095705282 &&
  H_2 == 64'd2563595384472711505 &&
  H_3 == 64'd10824532655140301501 &&
  H_4 == 64'd10819967247969091555 &&
  H_5 == 64'd13717434660681038226 &&
  H_6 == 64'd3098927326965381290 &&
  H_7 == 64'd1060366662362279074 &&
  W_0 == slicer($past(block_in, 1), 32'sd15) &&
  W_10 == slicer($past(block_in, 1),32'sd5) &&
  W_11 == slicer($past(block_in, 1),32'sd4) &&
  W_12 == slicer($past(block_in, 1),32'sd3) &&
  W_13 == slicer($past(block_in, 1),32'sd2) &&
  W_14 == slicer($past(block_in, 1),32'sd1) &&
  W_15 == slicer($past(block_in, 1),32'sd0) &&
  W_1 == slicer($past(block_in, 1), 32'sd14) &&
  W_2 == slicer($past(block_in, 1), 32'sd13) &&
  W_3 == slicer($past(block_in, 1), 32'sd12) &&
  W_4 == slicer($past(block_in, 1), 32'sd11) &&
  W_5 == slicer($past(block_in, 1), 32'sd10) &&
  W_6 == slicer($past(block_in, 1), 32'sd9) &&
  W_7 == slicer($past(block_in, 1), 32'sd8) &&
  W_8 == slicer($past(block_in, 1), 32'sd7) &&
  W_9 == slicer($past(block_in, 1), 32'sd6) &&
  a == 64'd2463787394917988140 &&
  b == 64'd11481187982095705282 &&
  c == 64'd2563595384472711505 &&
  d == 64'd10824532655140301501 &&
  e == 64'd10819967247969091555 &&
  f == 64'd13717434660681038226 &&
  g == 64'd3098927326965381290 &&
  h == 64'd1060366662362279074 &&
  i == 'sd0;
endproperty


IDLE_to_SHA_Rounds_512_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_512_p);
property IDLE_to_SHA_Rounds_512_p;
  IDLE &&
  block_in_valid &&
  block_init &&
  (block_sha_mode == 'sd512)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H_0 == 64'd7640891576956012808 &&
  H_1 == 64'd13503953896175478587 &&
  H_2 == 64'd4354685564936845355 &&
  H_3 == 64'd11912009170470909681 &&
  H_4 == 64'd5840696475078001361 &&
  H_5 == 64'd11170449401992604703 &&
  H_6 == 64'd2270897969802886507 &&
  H_7 == 64'd6620516959819538809 &&
  W_0 == slicer($past(block_in, 1), 32'sd15) &&
  W_10 == slicer($past(block_in, 1),32'sd5) &&
  W_11 == slicer($past(block_in, 1),32'sd4) &&
  W_12 == slicer($past(block_in, 1),32'sd3) &&
  W_13 == slicer($past(block_in, 1),32'sd2) &&
  W_14 == slicer($past(block_in, 1),32'sd1) &&
  W_15 == slicer($past(block_in, 1),32'sd0) &&
  W_1 == slicer($past(block_in, 1), 32'sd14) &&
  W_2 == slicer($past(block_in, 1), 32'sd13) &&
  W_3 == slicer($past(block_in, 1), 32'sd12) &&
  W_4 == slicer($past(block_in, 1), 32'sd11) &&
  W_5 == slicer($past(block_in, 1), 32'sd10) &&
  W_6 == slicer($past(block_in, 1), 32'sd9) &&
  W_7 == slicer($past(block_in, 1), 32'sd8) &&
  W_8 == slicer($past(block_in, 1), 32'sd7) &&
  W_9 == slicer($past(block_in, 1), 32'sd6) &&
  a == 64'd7640891576956012808 &&
  b == 64'd13503953896175478587 &&
  c == 64'd4354685564936845355 &&
  d == 64'd11912009170470909681 &&
  e == 64'd5840696475078001361 &&
  f == 64'd11170449401992604703 &&
  g == 64'd2270897969802886507 &&
  h == 64'd6620516959819538809 &&
  i == 'sd0;
endproperty


IDLE_to_SHA_Rounds_384_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_384_p);
property IDLE_to_SHA_Rounds_384_p;
  IDLE &&
  block_in_valid &&
  block_init &&
  block_sha_mode == 'sd384
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H_0 == 64'd14680500436340154072 &&
  H_1 == 64'd7105036623409894663 &&
  H_2 == 64'd10473403895298186519 &&
  H_3 == 64'd1526699215303891257 &&
  H_4 == 64'd7436329637833083697 &&
  H_5 == 64'd10282925794625328401 &&
  H_6 == 64'd15784041429090275239 &&
  H_7 == 64'd5167115440072839076 &&
  W_0 == slicer($past(block_in, 1), 32'sd15) &&
  W_10 == slicer($past(block_in, 1),32'sd5) &&
  W_11 == slicer($past(block_in, 1),32'sd4) &&
  W_12 == slicer($past(block_in, 1),32'sd3) &&
  W_13 == slicer($past(block_in, 1),32'sd2) &&
  W_14 == slicer($past(block_in, 1),32'sd1) &&
  W_15 == slicer($past(block_in, 1),32'sd0) &&
  W_1 == slicer($past(block_in, 1), 32'sd14) &&
  W_2 == slicer($past(block_in, 1), 32'sd13) &&
  W_3 == slicer($past(block_in, 1), 32'sd12) &&
  W_4 == slicer($past(block_in, 1), 32'sd11) &&
  W_5 == slicer($past(block_in, 1), 32'sd10) &&
  W_6 == slicer($past(block_in, 1), 32'sd9) &&
  W_7 == slicer($past(block_in, 1), 32'sd8) &&
  W_8 == slicer($past(block_in, 1), 32'sd7) &&
  W_9 == slicer($past(block_in, 1), 32'sd6) &&
  a == 64'd14680500436340154072 &&
  b == 64'd7105036623409894663 &&
  c == 64'd10473403895298186519 &&
  d == 64'd1526699215303891257 &&
  e == 64'd7436329637833083697 &&
  f == 64'd10282925794625328401 &&
  g == 64'd15784041429090275239 &&
  h == 64'd5167115440072839076 &&
  i == 'sd0;
endproperty


IDLE_to_SHA_Rounds_next_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_next_p);
property IDLE_to_SHA_Rounds_next_p;
  IDLE &&
  block_in_valid &&
  !block_init
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H_0 == $past(H_0, 1) &&
  H_1 == $past(H_1, 1) &&
  H_2 == $past(H_2, 1) &&
  H_3 == $past(H_3, 1) &&
  H_4 == $past(H_4, 1) &&
  H_5 == $past(H_5, 1) &&
  H_6 == $past(H_6, 1) &&
  H_7 == $past(H_7, 1) &&
  W_0 == slicer($past(block_in, 1), 32'sd15) &&
  W_10 == slicer($past(block_in, 1),32'sd5) &&
  W_11 == slicer($past(block_in, 1),32'sd4) &&
  W_12 == slicer($past(block_in, 1),32'sd3) &&
  W_13 == slicer($past(block_in, 1),32'sd2) &&
  W_14 == slicer($past(block_in, 1),32'sd1) &&
  W_15 == slicer($past(block_in, 1),32'sd0) &&
  W_1 == slicer($past(block_in, 1), 32'sd14) &&
  W_2 == slicer($past(block_in, 1), 32'sd13) &&
  W_3 == slicer($past(block_in, 1), 32'sd12) &&
  W_4 == slicer($past(block_in, 1), 32'sd11) &&
  W_5 == slicer($past(block_in, 1), 32'sd10) &&
  W_6 == slicer($past(block_in, 1), 32'sd9) &&
  W_7 == slicer($past(block_in, 1), 32'sd8) &&
  W_8 == slicer($past(block_in, 1), 32'sd7) &&
  W_9 == slicer($past(block_in, 1), 32'sd6) &&
  a == $past(H_0, 1) &&
  b == $past(H_1, 1) &&
  c == $past(H_2, 1) &&
  d == $past(H_3, 1) &&
  e == $past(H_4, 1) &&
  f == $past(H_5, 1) &&
  g == $past(H_6, 1) &&
  h == $past(H_7, 1) &&
  i == 'sd0;
endproperty


SHA_Rounds_to_DONE_a: assert property (disable iff(!rst) SHA_Rounds_to_DONE_p);
property SHA_Rounds_to_DONE_p;
  SHA_Rounds &&
  (('sd1 + i) >= 'sd80)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  DONE &&
  H_0 == $past(H_0, 1) &&
  H_1 == $past(H_1, 1) &&
  H_2 == $past(H_2, 1) &&
  H_3 == $past(H_3, 1) &&
  H_4 == $past(H_4, 1) &&
  H_5 == $past(H_5, 1) &&
  H_6 == $past(H_6, 1) &&
  H_7 == $past(H_7, 1) &&
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
  a == $past(64'(T1(e,f,g,h,K[i],compute_w(W_14,W_9,W_1,W_0))+T2(a,b,c))) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == $past(64'(d+T1(e,f,g,h,K[i],compute_w(W_14,W_9,W_1,W_0)))) &&
  f == $past(e, 1) &&
  g == $past(f, 1) &&
  h == $past(g, 1) &&
  i == ('sd1 + $past(i, 1));
endproperty


SHA_Rounds_to_SHA_Rounds_before_16_a: assert property (disable iff(!rst) SHA_Rounds_to_SHA_Rounds_p);
property SHA_Rounds_to_SHA_Rounds_p;
  SHA_Rounds &&
  (i < 'sd16)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H_0 == $past(H_0, 1) &&
  H_1 == $past(H_1, 1) &&
  H_2 == $past(H_2, 1) &&
  H_3 == $past(H_3, 1) &&
  H_4 == $past(H_4, 1) &&
  H_5 == $past(H_5, 1) &&
  H_6 == $past(H_6, 1) &&
  H_7 == $past(H_7, 1) &&
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
  a == $past(64'(T1(e,f,g,h,K[i],W[j])+T2(a,b,c))) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == $past(64'(d+T1(e,f,g,h,K[i],W[j]))) &&
  f == $past(e, 1) &&
  g == $past(f, 1) &&
  h == $past(g, 1) &&
  i == ('sd1 + $past(i, 1));
endproperty


SHA_Rounds_to_SHA_Rounds_after_16_a: assert property (disable iff(!rst) SHA_Rounds_to_SHA_Rounds_1_p);
property SHA_Rounds_to_SHA_Rounds_1_p;
  SHA_Rounds &&
  (i >= 'sd16) &&
  (('sd1 + i) < 'sd80)
|->
  ##1 (block_in_ready == 0) and
  ##1 (digest_valid == 0) and
  ##1
  SHA_Rounds &&
  H_0 == $past(H_0, 1) &&
  H_1 == $past(H_1, 1) &&
  H_2 == $past(H_2, 1) &&
  H_3 == $past(H_3, 1) &&
  H_4 == $past(H_4, 1) &&
  H_5 == $past(H_5, 1) &&
  H_6 == $past(H_6, 1) &&
  H_7 == $past(H_7, 1) &&
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
  a == $past(64'(T1(e,f,g,h,K[i],compute_w(W_14,W_9,W_1,W_0))+T2(a,b,c))) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == $past(64'(d+T1(e,f,g,h,K[i],compute_w(W_14,W_9,W_1,W_0)))) &&
  f == $past(e, 1) &&
  g == $past(f, 1) &&
  h == $past(g, 1) &&
  i == ('sd1 + $past(i, 1));
endproperty


IDLE_wait_a: assert property (disable iff(!rst) IDLE_wait_p);
property IDLE_wait_p;
  IDLE &&
  !block_in_valid
|->
  ##1
  IDLE &&
  H_0 == $past(H_0, 1) &&
  H_1 == $past(H_1, 1) &&
  H_2 == $past(H_2, 1) &&
  H_3 == $past(H_3, 1) &&
  H_4 == $past(H_4, 1) &&
  H_5 == $past(H_5, 1) &&
  H_6 == $past(H_6, 1) &&
  H_7 == $past(H_7, 1) &&
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
  a == $past(a, 1) &&
  b == $past(b, 1) &&
  c == $past(c, 1) &&
  d == $past(d, 1) &&
  e == $past(e, 1) &&
  f == $past(f, 1) &&
  g == $past(g, 1) &&
  h == $past(h, 1) &&
  i == $past(i, 1) &&
  block_in_ready == 1 &&
  digest_valid == $past(digest_valid);
endproperty


endmodule

 bind sha512_core fv_sha_512_m fv_sha512(
  .rst((reset_n)  && !(zeroize)),
  .clk(clk),
  .block_in(block_msg),
  .block_sha_mode((mode==0)?224:(mode==1)?256:(mode==2)?384:512),
  .block_init(init_cmd),
  .block_next(next_cmd),
  .block_zeroize(zeroize),
  .digest_out(digest),
  .block_in_valid(((init_cmd) || (next_cmd))),
  .block_in_ready(ready),
  .digest_valid((digest_valid) ),
  .H_0(H0_reg),
  .H_1(H1_reg),
  .H_2(H2_reg),
  .H_3(H3_reg),
  .H_4(H4_reg),
  .H_5(H5_reg),
  .H_6(H6_reg),
  .H_7(H7_reg),
  .W_0(w_mem_inst.w_mem[00]),
  .W_1(w_mem_inst.w_mem[01]),
  .W_2(w_mem_inst.w_mem[02]),
  .W_3(w_mem_inst.w_mem[03]),
  .W_4(w_mem_inst.w_mem[04]),
  .W_5(w_mem_inst.w_mem[05]),
  .W_6(w_mem_inst.w_mem[06]),
  .W_7(w_mem_inst.w_mem[07]),
  .W_8(w_mem_inst.w_mem[08]),
  .W_9(w_mem_inst.w_mem[09]),
  .W_10(w_mem_inst.w_mem[10]),
  .W_11(w_mem_inst.w_mem[11]),
  .W_12(w_mem_inst.w_mem[12]),
  .W_13(w_mem_inst.w_mem[13]),
  .W_14(w_mem_inst.w_mem[14]),
  .W_15(w_mem_inst.w_mem[15]),
  .a(a_reg),
  .b(b_reg),
  .c(c_reg),
  .d(d_reg),
  .e(e_reg),
  .f(f_reg),
  .g(g_reg),
  .h(h_reg),
  .i(round_ctr_reg),
  .IDLE(sha512_ctrl_reg==2'h0),
  .SHA_Rounds(sha512_ctrl_reg==2'h1),
  .DONE(sha512_ctrl_reg==2'h2)
);

