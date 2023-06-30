// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Created on 21.06.2023 at 10:50
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------
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

import fv_sha512_pkg::*;


module fv_sha_512_m(
  input bit rst,
  input bit clk,
  input bit unsigned [1023:0] block_in,
  input bit unsigned [31:0] block_sha_mode,
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


IDLE_to_SHA_Rounds_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_p);
property IDLE_to_SHA_Rounds_p;
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


IDLE_to_SHA_Rounds_1_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_1_p);
property IDLE_to_SHA_Rounds_1_p;
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


IDLE_to_SHA_Rounds_2_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_2_p);
property IDLE_to_SHA_Rounds_2_p;
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


IDLE_to_SHA_Rounds_3_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_3_p);
property IDLE_to_SHA_Rounds_3_p;
  IDLE &&
  block_in_valid &&
  block_init &&
  (block_sha_mode != 'sd224) &&
  (block_sha_mode != 'sd256) &&
  (block_sha_mode != 'sd512)
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


IDLE_to_SHA_Rounds_4_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_4_p);
property IDLE_to_SHA_Rounds_4_p;
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
  (i >= 'sd16) &&
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


SHA_Rounds_to_SHA_Rounds_a: assert property (disable iff(!rst) SHA_Rounds_to_SHA_Rounds_p);
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


SHA_Rounds_to_SHA_Rounds_1_a: assert property (disable iff(!rst) SHA_Rounds_to_SHA_Rounds_1_p);
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
  .rst((sha512_core.reset_n)  && !(sha512_core.zeroize)),
  .clk(sha512_core.clk),
  .block_in(sha512_core.block_msg),
  .block_sha_mode(get_block_sha_mode(sha512_core.mode)),
  .block_init(sha512_core.init_cmd),
  .block_next(sha512_core.next_cmd),
  .block_zeroize(sha512_core.zeroize),
  .digest_out(sha512_core.digest),
  .block_in_valid(((sha512_core.init_cmd) || (sha512_core.next_cmd))),
  .block_in_ready(sha512_core.ready),
  .digest_valid((sha512_core.digest_valid) ),
  .H_0(sha512_core.H0_reg),
  .H_1(sha512_core.H1_reg),
  .H_2(sha512_core.H2_reg),
  .H_3(sha512_core.H3_reg),
  .H_4(sha512_core.H4_reg),
  .H_5(sha512_core.H5_reg),
  .H_6(sha512_core.H6_reg),
  .H_7(sha512_core.H7_reg),
  .W_0(sha512_core.w_mem_inst.w_mem[00]),
  .W_1(sha512_core.w_mem_inst.w_mem[01]),
  .W_2(sha512_core.w_mem_inst.w_mem[02]),
  .W_3(sha512_core.w_mem_inst.w_mem[03]),
  .W_4(sha512_core.w_mem_inst.w_mem[04]),
  .W_5(sha512_core.w_mem_inst.w_mem[05]),
  .W_6(sha512_core.w_mem_inst.w_mem[06]),
  .W_7(sha512_core.w_mem_inst.w_mem[07]),
  .W_8(sha512_core.w_mem_inst.w_mem[08]),
  .W_9(sha512_core.w_mem_inst.w_mem[09]),
  .W_10(sha512_core.w_mem_inst.w_mem[10]),
  .W_11(sha512_core.w_mem_inst.w_mem[11]),
  .W_12(sha512_core.w_mem_inst.w_mem[12]),
  .W_13(sha512_core.w_mem_inst.w_mem[13]),
  .W_14(sha512_core.w_mem_inst.w_mem[14]),
  .W_15(sha512_core.w_mem_inst.w_mem[15]),
  .a(sha512_core.a_reg),
  .b(sha512_core.b_reg),
  .c(sha512_core.c_reg),
  .d(sha512_core.d_reg),
  .e(sha512_core.e_reg),
  .f(sha512_core.f_reg),
  .g(sha512_core.g_reg),
  .h(sha512_core.h_reg),
  .i(sha512_core.round_ctr_reg),
  .IDLE(sha512_core.sha512_ctrl_reg==2'h0),
  .SHA_Rounds(sha512_core.sha512_ctrl_reg==2'h1),
  .DONE(sha512_core.sha512_ctrl_reg==2'h2)
);

