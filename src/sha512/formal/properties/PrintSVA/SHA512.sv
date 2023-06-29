// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Created on 23.06.2023 at 13:11
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------


import global_package::*;


`include "fv_constraints.sv"


sequence hold(l, e);
  (l===e, l=e);
endsequence


module SHA512_verification(
  input bit rst,
  input bit clk,
  input bit unsigned [1023:0] SHA_Input_sig_in,
  input bit signed [31:0] SHA_Input_sig_SHA_Mode,
  input bit SHA_Input_sig_init,
  input bit SHA_Input_sig_next,
  input bit SHA_Input_sig_zeroize,
  input bit unsigned [511:0] out_sig,
  input bit SHA_Input_sync,
  input bit SHA_Input_notify,
  input bit out_notify,
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
  input bit signed [31:0] i,
  input bit IDLE,
  input bit SHA_Rounds,
  input bit DONE
);


default clocking default_clk @(posedge clk); endclocking


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
  SHA_Input_notify == 1 &&
  out_notify == 0;
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
  out_sig == 512'(((512'(((512'(((512'(((512'(((512'(((512'((((64'(($past(H_7, 1) + $past(h, 1))) << 64'd448) >> 512'd64) + (64'(($past(H_6, 1) + $past(g, 1))) << 64'd448))) >> 512'd64) + (64'(($past(H_5, 1) + $past(f, 1))) << 64'd448))) >> 512'd64) + (64'(($past(H_4, 1) + $past(e, 1))) << 64'd448))) >> 512'd64) + (64'(($past(H_3, 1) + $past(d, 1))) << 64'd448))) >> 512'd64) + (64'(($past(H_2, 1) + $past(c, 1))) << 64'd448))) >> 512'd64) + (64'(($past(H_1, 1) + $past(b, 1))) << 64'd448))) >> 512'd64) + (64'(($past(H_0, 1) + $past(a, 1))) << 64'd448))) &&
  SHA_Input_notify == 1 &&
  out_notify == 1;
endproperty


IDLE_to_SHA_Rounds_a: assert property (disable iff(!rst) IDLE_to_SHA_Rounds_p);
property IDLE_to_SHA_Rounds_p;
  IDLE &&
  SHA_Input_sync &&
  SHA_Input_sig_init &&
  (SHA_Input_sig_SHA_Mode == 'sd224)
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
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
  W_0 == slicer($past(SHA_Input_sig_in, 1), 64'sd15) &&
  W_10 == slicer($past(SHA_Input_sig_in, 1), 64'sd5) &&
  W_11 == slicer($past(SHA_Input_sig_in, 1), 64'sd4) &&
  W_12 == slicer($past(SHA_Input_sig_in, 1), 64'sd3) &&
  W_13 == slicer($past(SHA_Input_sig_in, 1), 64'sd2) &&
  W_14 == slicer($past(SHA_Input_sig_in, 1), 64'sd1) &&
  W_15 == slicer($past(SHA_Input_sig_in, 1), 64'sd0) &&
  W_1 == slicer($past(SHA_Input_sig_in, 1), 64'sd14) &&
  W_2 == slicer($past(SHA_Input_sig_in, 1), 64'sd13) &&
  W_3 == slicer($past(SHA_Input_sig_in, 1), 64'sd12) &&
  W_4 == slicer($past(SHA_Input_sig_in, 1), 64'sd11) &&
  W_5 == slicer($past(SHA_Input_sig_in, 1), 64'sd10) &&
  W_6 == slicer($past(SHA_Input_sig_in, 1), 64'sd9) &&
  W_7 == slicer($past(SHA_Input_sig_in, 1), 64'sd8) &&
  W_8 == slicer($past(SHA_Input_sig_in, 1), 64'sd7) &&
  W_9 == slicer($past(SHA_Input_sig_in, 1), 64'sd6) &&
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
  SHA_Input_sync &&
  SHA_Input_sig_init &&
  (SHA_Input_sig_SHA_Mode == 'sd256)
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
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
  W_0 == slicer($past(SHA_Input_sig_in, 1), 64'sd15) &&
  W_10 == slicer($past(SHA_Input_sig_in, 1), 64'sd5) &&
  W_11 == slicer($past(SHA_Input_sig_in, 1), 64'sd4) &&
  W_12 == slicer($past(SHA_Input_sig_in, 1), 64'sd3) &&
  W_13 == slicer($past(SHA_Input_sig_in, 1), 64'sd2) &&
  W_14 == slicer($past(SHA_Input_sig_in, 1), 64'sd1) &&
  W_15 == slicer($past(SHA_Input_sig_in, 1), 64'sd0) &&
  W_1 == slicer($past(SHA_Input_sig_in, 1), 64'sd14) &&
  W_2 == slicer($past(SHA_Input_sig_in, 1), 64'sd13) &&
  W_3 == slicer($past(SHA_Input_sig_in, 1), 64'sd12) &&
  W_4 == slicer($past(SHA_Input_sig_in, 1), 64'sd11) &&
  W_5 == slicer($past(SHA_Input_sig_in, 1), 64'sd10) &&
  W_6 == slicer($past(SHA_Input_sig_in, 1), 64'sd9) &&
  W_7 == slicer($past(SHA_Input_sig_in, 1), 64'sd8) &&
  W_8 == slicer($past(SHA_Input_sig_in, 1), 64'sd7) &&
  W_9 == slicer($past(SHA_Input_sig_in, 1), 64'sd6) &&
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
  SHA_Input_sync &&
  SHA_Input_sig_init &&
  (SHA_Input_sig_SHA_Mode == 'sd512)
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
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
  W_0 == slicer($past(SHA_Input_sig_in, 1), 64'sd15) &&
  W_10 == slicer($past(SHA_Input_sig_in, 1), 64'sd5) &&
  W_11 == slicer($past(SHA_Input_sig_in, 1), 64'sd4) &&
  W_12 == slicer($past(SHA_Input_sig_in, 1), 64'sd3) &&
  W_13 == slicer($past(SHA_Input_sig_in, 1), 64'sd2) &&
  W_14 == slicer($past(SHA_Input_sig_in, 1), 64'sd1) &&
  W_15 == slicer($past(SHA_Input_sig_in, 1), 64'sd0) &&
  W_1 == slicer($past(SHA_Input_sig_in, 1), 64'sd14) &&
  W_2 == slicer($past(SHA_Input_sig_in, 1), 64'sd13) &&
  W_3 == slicer($past(SHA_Input_sig_in, 1), 64'sd12) &&
  W_4 == slicer($past(SHA_Input_sig_in, 1), 64'sd11) &&
  W_5 == slicer($past(SHA_Input_sig_in, 1), 64'sd10) &&
  W_6 == slicer($past(SHA_Input_sig_in, 1), 64'sd9) &&
  W_7 == slicer($past(SHA_Input_sig_in, 1), 64'sd8) &&
  W_8 == slicer($past(SHA_Input_sig_in, 1), 64'sd7) &&
  W_9 == slicer($past(SHA_Input_sig_in, 1), 64'sd6) &&
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
  SHA_Input_sync &&
  SHA_Input_sig_init &&
  (SHA_Input_sig_SHA_Mode != 'sd224) &&
  (SHA_Input_sig_SHA_Mode != 'sd256) &&
  (SHA_Input_sig_SHA_Mode != 'sd512)
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
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
  W_0 == slicer($past(SHA_Input_sig_in, 1), 64'sd15) &&
  W_10 == slicer($past(SHA_Input_sig_in, 1), 64'sd5) &&
  W_11 == slicer($past(SHA_Input_sig_in, 1), 64'sd4) &&
  W_12 == slicer($past(SHA_Input_sig_in, 1), 64'sd3) &&
  W_13 == slicer($past(SHA_Input_sig_in, 1), 64'sd2) &&
  W_14 == slicer($past(SHA_Input_sig_in, 1), 64'sd1) &&
  W_15 == slicer($past(SHA_Input_sig_in, 1), 64'sd0) &&
  W_1 == slicer($past(SHA_Input_sig_in, 1), 64'sd14) &&
  W_2 == slicer($past(SHA_Input_sig_in, 1), 64'sd13) &&
  W_3 == slicer($past(SHA_Input_sig_in, 1), 64'sd12) &&
  W_4 == slicer($past(SHA_Input_sig_in, 1), 64'sd11) &&
  W_5 == slicer($past(SHA_Input_sig_in, 1), 64'sd10) &&
  W_6 == slicer($past(SHA_Input_sig_in, 1), 64'sd9) &&
  W_7 == slicer($past(SHA_Input_sig_in, 1), 64'sd8) &&
  W_8 == slicer($past(SHA_Input_sig_in, 1), 64'sd7) &&
  W_9 == slicer($past(SHA_Input_sig_in, 1), 64'sd6) &&
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
  SHA_Input_sync &&
  !SHA_Input_sig_init
|->
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
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
  W_0 == slicer($past(SHA_Input_sig_in, 1), 64'sd15) &&
  W_10 == slicer($past(SHA_Input_sig_in, 1), 64'sd5) &&
  W_11 == slicer($past(SHA_Input_sig_in, 1), 64'sd4) &&
  W_12 == slicer($past(SHA_Input_sig_in, 1), 64'sd3) &&
  W_13 == slicer($past(SHA_Input_sig_in, 1), 64'sd2) &&
  W_14 == slicer($past(SHA_Input_sig_in, 1), 64'sd1) &&
  W_15 == slicer($past(SHA_Input_sig_in, 1), 64'sd0) &&
  W_1 == slicer($past(SHA_Input_sig_in, 1), 64'sd14) &&
  W_2 == slicer($past(SHA_Input_sig_in, 1), 64'sd13) &&
  W_3 == slicer($past(SHA_Input_sig_in, 1), 64'sd12) &&
  W_4 == slicer($past(SHA_Input_sig_in, 1), 64'sd11) &&
  W_5 == slicer($past(SHA_Input_sig_in, 1), 64'sd10) &&
  W_6 == slicer($past(SHA_Input_sig_in, 1), 64'sd9) &&
  W_7 == slicer($past(SHA_Input_sig_in, 1), 64'sd8) &&
  W_8 == slicer($past(SHA_Input_sig_in, 1), 64'sd7) &&
  W_9 == slicer($past(SHA_Input_sig_in, 1), 64'sd6) &&
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
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
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
  W_15 == compute_w($past(W_14, 1), $past(W_9, 1), $past(W_1, 1), $past(W_0, 1)) &&
  W_1 == $past(W_2, 1) &&
  W_2 == $past(W_3, 1) &&
  W_3 == $past(W_4, 1) &&
  W_4 == $past(W_5, 1) &&
  W_5 == $past(W_6, 1) &&
  W_6 == $past(W_7, 1) &&
  W_7 == $past(W_8, 1) &&
  W_8 == $past(W_9, 1) &&
  W_9 == $past(W_10, 1) &&
  a == 64'((T1($past(e, 1), $past(f, 1), $past(g, 1), $past(h, 1), K[$past(i, 1)], compute_w($past(W_14, 1), $past(W_9, 1), $past(W_1, 1), $past(W_0, 1))) + T2($past(a, 1), $past(b, 1), $past(c, 1)))) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == 64'(($past(d, 1) + T1($past(e, 1), $past(f, 1), $past(g, 1), $past(h, 1), K[$past(i, 1)], compute_w($past(W_14, 1), $past(W_9, 1), $past(W_1, 1), $past(W_0, 1))))) &&
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
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
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
  a == 64'((T1($past(e, 1), $past(f, 1), $past(g, 1), $past(h, 1), K[$past(i, 1)], (($past(i, 1) == 'sd0) ? $past(W_0, 1) : (($past(i, 1) == 'sd1) ? $past(W_1, 1) : (($past(i, 1) == 'sd2) ? $past(W_2, 1) : (($past(i, 1) == 'sd3) ? $past(W_3, 1) : (($past(i, 1) == 'sd4) ? $past(W_4, 1) : (($past(i, 1) == 'sd5) ? $past(W_5, 1) : (($past(i, 1) == 'sd6) ? $past(W_6, 1) : (($past(i, 1) == 'sd7) ? $past(W_7, 1) : (($past(i, 1) == 'sd8) ? $past(W_8, 1) : (($past(i, 1) == 'sd9) ? $past(W_9, 1) : (($past(i, 1) == 'sd10) ? $past(W_10, 1) : (($past(i, 1) == 'sd11) ? $past(W_11, 1) : (($past(i, 1) == 'sd12) ? $past(W_12, 1) : (($past(i, 1) == 'sd13) ? $past(W_13, 1) : (($past(i, 1) == 'sd14) ? $past(W_14, 1) : $past(W_15, 1))))))))))))))))) + T2($past(a, 1), $past(b, 1), $past(c, 1)))) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == 64'(($past(d, 1) + T1($past(e, 1), $past(f, 1), $past(g, 1), $past(h, 1), K[$past(i, 1)], (($past(i, 1) == 'sd0) ? $past(W_0, 1) : (($past(i, 1) == 'sd1) ? $past(W_1, 1) : (($past(i, 1) == 'sd2) ? $past(W_2, 1) : (($past(i, 1) == 'sd3) ? $past(W_3, 1) : (($past(i, 1) == 'sd4) ? $past(W_4, 1) : (($past(i, 1) == 'sd5) ? $past(W_5, 1) : (($past(i, 1) == 'sd6) ? $past(W_6, 1) : (($past(i, 1) == 'sd7) ? $past(W_7, 1) : (($past(i, 1) == 'sd8) ? $past(W_8, 1) : (($past(i, 1) == 'sd9) ? $past(W_9, 1) : (($past(i, 1) == 'sd10) ? $past(W_10, 1) : (($past(i, 1) == 'sd11) ? $past(W_11, 1) : (($past(i, 1) == 'sd12) ? $past(W_12, 1) : (($past(i, 1) == 'sd13) ? $past(W_13, 1) : (($past(i, 1) == 'sd14) ? $past(W_14, 1) : $past(W_15, 1))))))))))))))))))) &&
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
  ##1 (SHA_Input_notify == 0) and
  ##1 (out_notify == 0) and
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
  W_15 == compute_w($past(W_14, 1), $past(W_9, 1), $past(W_1, 1), $past(W_0, 1)) &&
  W_1 == $past(W_2, 1) &&
  W_2 == $past(W_3, 1) &&
  W_3 == $past(W_4, 1) &&
  W_4 == $past(W_5, 1) &&
  W_5 == $past(W_6, 1) &&
  W_6 == $past(W_7, 1) &&
  W_7 == $past(W_8, 1) &&
  W_8 == $past(W_9, 1) &&
  W_9 == $past(W_10, 1) &&
  a == 64'((T1($past(e, 1), $past(f, 1), $past(g, 1), $past(h, 1), K[$past(i, 1)], compute_w($past(W_14, 1), $past(W_9, 1), $past(W_1, 1), $past(W_0, 1))) + T2($past(a, 1), $past(b, 1), $past(c, 1)))) &&
  b == $past(a, 1) &&
  c == $past(b, 1) &&
  d == $past(c, 1) &&
  e == 64'(($past(d, 1) + T1($past(e, 1), $past(f, 1), $past(g, 1), $past(h, 1), K[$past(i, 1)], compute_w($past(W_14, 1), $past(W_9, 1), $past(W_1, 1), $past(W_0, 1))))) &&
  f == $past(e, 1) &&
  g == $past(f, 1) &&
  h == $past(g, 1) &&
  i == ('sd1 + $past(i, 1));
endproperty


IDLE_wait_a: assert property (disable iff(!rst) IDLE_wait_p);
property IDLE_wait_p;
  IDLE &&
  !SHA_Input_sync
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
  SHA_Input_notify == 1 &&
  out_notify == 0;
endproperty


endmodule


module SHA512_bind(
  input bit clk
);


default clocking default_clk @(posedge clk); endclocking


function bit signed [31:0] SHA_Input_sig_SHA_Mode();
if(sha512_core.mode==0)
	return 224;
else if(sha512_core.mode==1)
	return 256;
else if(sha512_core.mode==2)
	return 384;
else
	return 512;
endfunction


SHA512_verification inst(
  .rst((sha512_core.reset_n)  && !(sha512_core.zeroize)),
  .clk(clk),
  .SHA_Input_sig_in(sha512_core.block_msg),
  .SHA_Input_sig_SHA_Mode(SHA_Input_sig_SHA_Mode()),
  .SHA_Input_sig_init(sha512_core.init_cmd),
  .SHA_Input_sig_next(sha512_core.next_cmd),
  .SHA_Input_sig_zeroize(sha512_core.zeroize),
  .out_sig(sha512_core.digest),
  .SHA_Input_sync(((sha512_core.init_cmd) || (sha512_core.next_cmd))),
  .SHA_Input_notify(sha512_core.ready),
  .out_notify((sha512_core.digest_valid) && ((sha512_core.sha512_ctrl_reg==2'h0) && $past(sha512_core.sha512_ctrl_reg==2'h2) )),
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


endmodule


bind sha512_core SHA512_bind inst(
  .clk(clk)
);
