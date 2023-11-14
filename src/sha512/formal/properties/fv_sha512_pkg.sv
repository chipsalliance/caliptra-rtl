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

package fv_sha512_pkg;


typedef bit unsigned [63:0] a_sc_big_unsigned_64_80 [79:0];


// Constants

parameter a_sc_big_unsigned_64_80 K = '{ 0:64'd4794697086780616226, 1:64'd8158064640168781261, 2:64'd13096744586834688815, 3:64'd16840607885511220156, 4:64'd4131703408338449720, 5:64'd6480981068601479193, 6:64'd10538285296894168987, 7:64'd12329834152419229976, 8:64'd15566598209576043074, 9:64'd1334009975649890238, 10:64'd2608012711638119052, 11:64'd6128411473006802146, 12:64'd8268148722764581231, 13:64'd9286055187155687089, 14:64'd11230858885718282805, 15:64'd13951009754708518548, 16:64'd16472876342353939154, 17:64'd17275323862435702243, 18:64'd1135362057144423861, 19:64'd2597628984639134821, 20:64'd3308224258029322869, 21:64'd5365058923640841347, 22:64'd6679025012923562964, 23:64'd8573033837759648693, 24:64'd10970295158949994411, 25:64'd12119686244451234320, 26:64'd12683024718118986047, 27:64'd13788192230050041572, 28:64'd14330467153632333762, 29:64'd15395433587784984357, 30:64'd489312712824947311, 31:64'd1452737877330783856, 32:64'd2861767655752347644, 33:64'd3322285676063803686, 34:64'd5560940570517711597, 35:64'd5996557281743188959, 36:64'd7280758554555802590, 37:64'd8532644243296465576, 38:64'd9350256976987008742, 39:64'd10552545826968843579, 40:64'd11727347734174303076, 41:64'd12113106623233404929, 42:64'd14000437183269869457, 43:64'd14369950271660146224, 44:64'd15101387698204529176, 45:64'd15463397548674623760, 46:64'd17586052441742319658, 47:64'd1182934255886127544, 48:64'd1847814050463011016, 49:64'd2177327727835720531, 50:64'd2830643537854262169, 51:64'd3796741975233480872, 52:64'd4115178125766777443, 53:64'd5681478168544905931, 54:64'd6601373596472566643, 55:64'd7507060721942968483, 56:64'd8399075790359081724, 57:64'd8693463985226723168, 58:64'd9568029438360202098, 59:64'd10144078919501101548, 60:64'd10430055236837252648, 61:64'd11840083180663258601, 62:64'd13761210420658862357, 63:64'd14299343276471374635, 64:64'd14566680578165727644, 65:64'd15097957966210449927, 66:64'd16922976911328602910, 67:64'd17689382322260857208, 68:64'd500013540394364858, 69:64'd748580250866718886, 70:64'd1242879168328830382, 71:64'd1977374033974150939, 72:64'd2944078676154940804, 73:64'd3659926193048069267, 74:64'd4368137639120453308, 75:64'd4836135668995329356, 76:64'd5532061633213252278, 77:64'd6448918945643986474, 78:64'd6902733635092675308, 79:64'd7801388544844847127 };


// Functions

function bit unsigned [63:0] Ch(bit unsigned [63:0] a, bit unsigned [63:0] b, bit unsigned [63:0] c);
  return ((a & b) ^ (~a & c));
endfunction

function bit unsigned [63:0] Maj(bit unsigned [63:0] x, bit unsigned [63:0] y, bit unsigned [63:0] z);
  return (((x & y) ^ (x & z)) ^ (y & z));
endfunction


function bit unsigned [63:0] T1(bit unsigned [63:0] e, bit unsigned [63:0] f, bit unsigned [63:0] g, bit unsigned [63:0] h, bit unsigned [63:0] k, bit unsigned [63:0] w);
  return 64'(((((h + sigma1(e)) + Ch(e, f, g)) + k) + w));
endfunction

function bit unsigned [63:0] T2(bit unsigned [63:0] a, bit unsigned [63:0] b, bit unsigned [63:0] c);
  return 64'((sigma0(a) + Maj(a, b, c)));
endfunction

function bit unsigned [63:0] compute_w(bit unsigned [63:0] w14, bit unsigned [63:0] w9, bit unsigned [63:0] w1, bit unsigned [63:0] w0);
  return 64'((((delta1(w14) + w9) + delta0(w1)) + w0));
endfunction

function bit unsigned [511:0] compute_digest(bit unsigned [63:0] H_7,bit unsigned [63:0] h,bit unsigned [63:0] H_6,bit unsigned [63:0] g,bit unsigned [63:0] H_5,bit unsigned [63:0] f,bit unsigned [63:0] H_4,bit unsigned [63:0] e,bit unsigned [63:0] H_3,bit unsigned [63:0] d,bit unsigned [63:0] H_2,bit unsigned [63:0] c,bit unsigned [63:0] H_1,bit unsigned [63:0] b,bit unsigned [63:0] H_0,bit unsigned [63:0] a);
  bit unsigned [511:0] temp;
    temp[63:0] = 64'(H_7+h);
    temp[127:64] = 64'(H_6+g);
    temp[191:128] = 64'(H_5+f);
    temp[255:192] = 64'(H_4+e);
    temp[319:256] = 64'(H_3+d);
    temp[383:320] = 64'(H_2+c);
    temp[447:384] = 64'(H_1+b);
    temp[511:448] = 64'(H_0+a);
  return temp;
 endfunction

function bit unsigned [63:0] delta0(bit unsigned [63:0] x);
  return ((rotr1(x) ^ rotr8(x)) ^ shr7(x));
endfunction

function bit unsigned [63:0] delta1(bit unsigned [63:0] x);
  return ((rotr19(x) ^ rotr61(x)) ^ shr6(x));
endfunction

function bit unsigned [31:0] get_block_sha_mode(input logic[1:0] mode );
if(mode==0)
	return 224;
else if(mode==1)
	return 256;
else if(mode==2)
	return 384;
else
	return 512;
endfunction

function bit unsigned [63:0] past_w(bit unsigned [6:0]i,bit unsigned [63:0]W_0,bit unsigned [63:0]W_1,bit unsigned [63:0]W_2,bit unsigned [63:0]W_3,bit unsigned [63:0]W_4,bit unsigned [63:0]W_5,bit unsigned [63:0]W_6,bit unsigned [63:0]W_7,bit unsigned [63:0]W_8,bit unsigned [63:0]W_9,bit unsigned [63:0]W_10,bit unsigned [63:0]W_11,bit unsigned [63:0]W_12,bit unsigned [63:0]W_13,bit unsigned [63:0]W_14,bit unsigned [63:0]W_15);
  return ((i == 'sd0) ? W_0 : ((i == 'sd1) ? W_1 : ((i == 'sd2) ? W_2 : ((i == 'sd3) ? W_3 : ((i == 'sd4) ? W_4 : ((i == 'sd5) ? W_5 : ((i == 'sd6) ? W_6 : ((i == 'sd7) ? W_7 : ((i == 'sd8) ? W_8 : ((i == 'sd9) ? W_9 : ((i == 'sd10) ? W_10 : ((i == 'sd11) ? W_11 : ((i == 'sd12) ? W_12 : ((i == 'sd13) ? W_13 : ((i == 'sd14) ? W_14 : W_15)))))))))))))));
endfunction

function bit unsigned [63:0] rotr1(bit unsigned [63:0] n);
  return 64'(((n >> 64'd1) | (n << 64'd63)));
endfunction

function bit unsigned [63:0] rotr14(bit unsigned [63:0] n);
  return 64'(((n >> 64'd14) | (n << 64'd50)));
endfunction

function bit unsigned [63:0] rotr18(bit unsigned [63:0] n);
  return 64'(((n >> 64'd18) | (n << 64'd46)));
endfunction

function bit unsigned [63:0] rotr19(bit unsigned [63:0] n);
  return 64'(((n >> 64'd19) | (n << 64'd45)));
endfunction

function bit unsigned [63:0] rotr28(bit unsigned [63:0] n);
  return 64'(((n >> 64'd28) | (n << 64'd36)));
endfunction

function bit unsigned [63:0] rotr34(bit unsigned [63:0] n);
  return 64'(((n >> 64'd34) | (n << 64'd30)));
endfunction

function bit unsigned [63:0] rotr39(bit unsigned [63:0] n);
  return 64'(((n >> 64'd39) | (n << 64'd25)));
endfunction

function bit unsigned [63:0] rotr41(bit unsigned [63:0] n);
  return 64'(((n >> 64'd41) | (n << 64'd23)));
endfunction

function bit unsigned [63:0] rotr61(bit unsigned [63:0] n);
  return 64'(((n >> 64'd61) | (n << 64'd3)));
endfunction

function bit unsigned [63:0] rotr8(bit unsigned [63:0] n);
  return 64'(((n >> 64'd8) | (n << 64'd56)));
endfunction

function bit unsigned [63:0] shr6(bit unsigned [63:0] n);
  return (n >> 64'd6);
endfunction

function bit unsigned [63:0] shr7(bit unsigned [63:0] n);
  return (n >> 64'd7);
endfunction

function bit unsigned [63:0] sigma0(bit unsigned [63:0] x);
  return ((rotr28(x) ^ rotr34(x)) ^ rotr39(x));
endfunction

function bit unsigned [63:0] sigma1(bit unsigned [63:0] x);
  return ((rotr14(x) ^ rotr18(x)) ^ rotr41(x));
endfunction

function bit unsigned [63:0] slicer(bit unsigned [1023:0] block, bit signed [31:0] index);
 return(block[(64*index)+:64]);
endfunction

endpackage
