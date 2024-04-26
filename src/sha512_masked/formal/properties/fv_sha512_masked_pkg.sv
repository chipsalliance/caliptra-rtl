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

package SHA512_masked_pkg;


typedef struct {
  logic unsigned [1023:0] in;
  logic unsigned [191:0] entropy;
  logic signed [31:0] SHA_Mode;
  logic init_cmd;
  logic next_cmd;
  logic zeroize;
} st_SHA_Args;

typedef struct {
  logic unsigned [63:0] masked;
  logic unsigned [63:0] random;
} st_masked_reg_t;

typedef logic a_bool_10 [9:0];

typedef logic unsigned [63:0] a_sc_big_unsigned_64_16 [15:0];

typedef logic unsigned [63:0] a_sc_big_unsigned_64_23 [22:0];
typedef logic unsigned [63:0] a_sc_big_unsigned_64_24 [23:0];

typedef logic unsigned [63:0] a_sc_big_unsigned_64_8 [7:0];

typedef logic unsigned [63:0] a_sc_big_unsigned_64_80 [79:0];

typedef st_masked_reg_t a_st_masked_reg_t_16 [15:0];


// Constants

parameter a_sc_big_unsigned_64_80 K = '{ 0: 64'h428A2F98D728AE22, 1: 64'h7137449123EF65CD, 2: 64'hB5C0FBCFEC4D3B2F, 3: 64'hE9B5DBA58189DBBC, 4: 64'h3956C25BF348B538, 5: 64'h59F111F1B605D019, 6: 64'h923F82A4AF194F9B, 7: 64'hAB1C5ED5DA6D8118, 8: 64'hD807AA98A3030242, 9: 64'h12835B0145706FBE, 10: 64'h243185BE4EE4B28C, 11: 64'h550C7DC3D5FFB4E2, 12: 64'h72BE5D74F27B896F, 13: 64'h80DEB1FE3B1696B1, 14: 64'h9BDC06A725C71235, 15: 64'hC19BF174CF692694, 16: 64'hE49B69C19EF14AD2, 17: 64'hEFBE4786384F25E3, 18: 64'hFC19DC68B8CD5B5, 19: 64'h240CA1CC77AC9C65, 20: 64'h2DE92C6F592B0275, 21: 64'h4A7484AA6EA6E483, 22: 64'h5CB0A9DCBD41FBD4, 23: 64'h76F988DA831153B5, 24: 64'h983E5152EE66DFAB, 25: 64'hA831C66D2DB43210, 26: 64'hB00327C898FB213F, 27: 64'hBF597FC7BEEF0EE4, 28: 64'hC6E00BF33DA88FC2, 29: 64'hD5A79147930AA725, 30: 64'h6CA6351E003826F, 31: 64'h142929670A0E6E70, 32: 64'h27B70A8546D22FFC, 33: 64'h2E1B21385C26C926, 34: 64'h4D2C6DFC5AC42AED, 35: 64'h53380D139D95B3DF, 36: 64'h650A73548BAF63DE, 37: 64'h766A0ABB3C77B2A8, 38: 64'h81C2C92E47EDAEE6, 39: 64'h92722C851482353B, 40: 64'hA2BFE8A14CF10364, 41: 64'hA81A664BBC423001, 42: 64'hC24B8B70D0F89791, 43: 64'hC76C51A30654BE30, 44: 64'hD192E819D6EF5218, 45: 64'hD69906245565A910, 46: 64'hF40E35855771202A, 47: 64'h106AA07032BBD1B8, 48: 64'h19A4C116B8D2D0C8, 49: 64'h1E376C085141AB53, 50: 64'h2748774CDF8EEB99, 51: 64'h34B0BCB5E19B48A8, 52: 64'h391C0CB3C5C95A63, 53: 64'h4ED8AA4AE3418ACB, 54: 64'h5B9CCA4F7763E373, 55: 64'h682E6FF3D6B2B8A3, 56: 64'h748F82EE5DEFB2FC, 57: 64'h78A5636F43172F60, 58: 64'h84C87814A1F0AB72, 59: 64'h8CC702081A6439EC, 60: 64'h90BEFFFA23631E28, 61: 64'hA4506CEBDE82BDE9, 62: 64'hBEF9A3F7B2C67915, 63: 64'hC67178F2E372532B, 64: 64'hCA273ECEEA26619C, 65: 64'hD186B8C721C0C207, 66: 64'hEADA7DD6CDE0EB1E, 67: 64'hF57D4F7FEE6ED178, 68: 64'h6F067AA72176FBA, 69: 64'hA637DC5A2C898A6, 70: 64'h113F9804BEF90DAE, 71: 64'h1B710B35131C471B, 72: 64'h28DB77F523047D84, 73: 64'h32CAAB7B40C72493, 74: 64'h3C9EBE0A15C9BEBC, 75: 64'h431D67C49C100D4C, 76: 64'h4CC5D4BECB3E42B6, 77: 64'h597F299CFC657E2A, 78: 64'h5FCB6FAB3AD6FAEC, 79: 64'h6C44198C4A475817 };


// Functions

/* function logic unsigned [63:0] A2B_conv(logic unsigned [63:0] x_masked, logic unsigned [63:0] x_random, logic q, logic masked_carry, logic unsigned [127:0] x_m, logic unsigned [63:0] mask, logic signed [31:0] j);
  return 64'((((x_masked & 64'h1) << 128'd64) >> 128'd1));
endfunction

function logic unsigned [63:0] B2A_conv(logic unsigned [63:0] x_masked, logic unsigned [63:0] x_random, logic q, logic masked_carry, logic unsigned [127:0] x_prime, logic unsigned [63:0] mask, logic signed [31:0] j);
  return 64'd0;
endfunction */


function bit unsigned [63:0] A2B_conv(bit unsigned [63:0] x_masked, bit unsigned [63:0] x_random, bit q, bit masked_carr, bit unsigned [127:0] x_m, bit unsigned [63:0] mask, bit signed [31:0] j);

 reg [63 : 0] masked_carry;
    for (int j = 0; j < 64 ; j++) begin
      if (j == 0) begin
        masked_carry[j] = (~x_masked[0] & x_random[0]) ^ q;
        x_masked[j] = x_masked[j];
      end
      else begin
        masked_carry[j] = (x_masked[j] ^ x_random[j]) & (x_random[j] ^ q) | (~x_masked[j] ^ x_random[j]) & masked_carry[j-1];
        x_masked[j] = (x_masked[j] ^ masked_carry[j-1]) ^ q;
       
      end
    end
    return x_masked;
endfunction

function bit unsigned [63:0] B2A_conv(bit unsigned [63:0] x_masked, bit unsigned [63:0] x_random, bit q, bit masked_carr, bit unsigned [127:0] x_prime, bit unsigned [63:0] mask, bit signed [31:0] j);
reg [63 : 0] masked_carry;
    for (int j = 0; j < 64 ; j++) begin
        if (j == 0) begin
          masked_carry[j] = ~x_masked[j] & (x_random[j] ^ q) | (x_masked[j] & q);
          x_prime[j] = x_masked[j];
        end
        else begin
          x_prime[j] = (x_masked[j] ^ masked_carry[j-1]) ^ q;
          masked_carry[j] = ~x_masked[j] & (x_random[j] ^ q) | x_masked[j] & masked_carry[j-1];
        end
    end
    return x_prime;
endfunction


function logic unsigned [63:0] T1_m(logic unsigned [63:0] e_masked, logic unsigned [63:0] e_random, logic unsigned [63:0] f_masked, logic unsigned [63:0] f_random, logic unsigned [63:0] g_masked, logic unsigned [63:0] g_random, logic unsigned [63:0] h_masked, logic unsigned [63:0] h_random, logic unsigned [63:0] k, logic unsigned [63:0] w_masked, logic unsigned [63:0] w_random, logic masked_carry, logic unsigned [127:0] x_prime, logic unsigned [63:0] mask, logic q_masking_rnd_0, logic q_masking_rnd_1, logic q_masking_rnd_2, logic q_masking_rnd_3, logic q_masking_rnd_4, logic signed [31:0] j);
  logic unsigned [63:0] B2A_conv_0_i;
  logic unsigned [63:0] sigma1_0_i;
  logic unsigned [63:0] sigma1_1_i;
  logic unsigned [63:0] B2A_conv_1_i;
  logic unsigned [63:0] masked_Ch_m_0_i;
  logic unsigned [63:0] B2A_conv_2_i;
  logic unsigned [63:0] B2A_conv_3_i;
  logic unsigned [63:0] B2A_conv_4_i;
  B2A_conv_0_i = B2A_conv(h_masked, h_random, q_masking_rnd_0, masked_carry, x_prime, mask, j);
  
  sigma1_0_i = sigma1(e_masked);
  
  sigma1_1_i = sigma1(e_random);
 
  B2A_conv_1_i = B2A_conv(sigma1_0_i, sigma1_1_i, q_masking_rnd_1, masked_carry, x_prime, mask, j);
  
  masked_Ch_m_0_i = masked_Ch_m(e_masked, e_random, f_masked, f_random, g_masked, g_random);
  
  B2A_conv_2_i = B2A_conv(masked_Ch_m_0_i, (e_random ^ g_random), q_masking_rnd_2, masked_carry, x_prime, mask, j);
  
  B2A_conv_3_i = B2A_conv(k, 64'h0, q_masking_rnd_3, masked_carry, x_prime, mask, j);
  
  B2A_conv_4_i = B2A_conv(w_masked, w_random, q_masking_rnd_4, masked_carry, x_prime, mask, j);

  return 64'(((((B2A_conv_0_i + B2A_conv_1_i) + B2A_conv_2_i) + B2A_conv_3_i) + B2A_conv_4_i));
endfunction

function logic unsigned [63:0] T1_r(logic unsigned [63:0] e_random, logic unsigned [63:0] g_random, logic unsigned [63:0] h_random, logic unsigned [63:0] w_random);
  logic unsigned [63:0] sigma1_0_i;
  sigma1_0_i = sigma1(e_random);

  return 64'((((h_random + sigma1_0_i) + (e_random ^ g_random)) + w_random));
endfunction

function logic unsigned [63:0] T2_m(logic unsigned [63:0] a_masked, logic unsigned [63:0] a_random, logic unsigned [63:0] b_masked, logic unsigned [63:0] b_random, logic unsigned [63:0] c_masked, logic unsigned [63:0] c_random, logic masked_carry, logic unsigned [127:0] x_prime, logic unsigned [63:0] mask, logic q_masking_rnd_5, logic q_masking_rnd_6, logic signed [31:0] j);
  logic unsigned [63:0] sigma0_0_i;
  logic unsigned [63:0] sigma0_1_i;
  logic unsigned [63:0] B2A_conv_0_i;
  logic unsigned [63:0] masked_Maj_0_i;
  logic unsigned [63:0] B2A_conv_1_i;
  sigma0_0_i = sigma0(a_masked);
  
  sigma0_1_i = sigma0(a_random);
  
  B2A_conv_0_i = B2A_conv(sigma0_0_i, sigma0_1_i, q_masking_rnd_5, masked_carry, x_prime, mask, j);
  
  masked_Maj_0_i = masked_Maj(a_masked, a_random, b_masked, b_random, c_masked, c_random);
  
  B2A_conv_1_i = B2A_conv(masked_Maj_0_i, b_random, q_masking_rnd_6, masked_carry, x_prime, mask, j);

  return 64'((B2A_conv_0_i + B2A_conv_1_i));
endfunction

function logic unsigned [63:0] T2_r(logic unsigned [63:0] a_random, logic unsigned [63:0] b_random);
  logic unsigned [63:0] sigma0_0_i;
  sigma0_0_i = sigma0(a_random);

  return 64'((sigma0_0_i + b_random));
endfunction

function logic unsigned [63:0] compute_w_masked(st_masked_reg_t w14, st_masked_reg_t w9, st_masked_reg_t w1, st_masked_reg_t w0, logic unsigned [191:0] ent, logic masked_carry, logic unsigned [127:0] x_prime, logic unsigned [63:0] mask, logic signed [31:0] j, logic unsigned [63:0] m_rand);
  logic ent_shift_0_i;
  logic unsigned [63:0] B2A_conv_0_i;
  logic unsigned [63:0] delta0_0_i;
  logic unsigned [63:0] delta0_1_i;
  logic ent_shift_1_i;
  logic unsigned [63:0] B2A_conv_1_i;
  logic ent_shift_2_i;
  logic unsigned [63:0] B2A_conv_2_i;
  logic unsigned [63:0] delta1_0_i;
  logic unsigned [63:0] delta1_1_i;
  logic ent_shift_3_i;
  logic unsigned [63:0] B2A_conv_3_i;
  logic unsigned [63:0] masked_sum_0_i;
  logic unsigned [63:0] masked_sum_1_i;
  logic unsigned [63:0] masked_sum_2_i;
  logic ent_shift_4_i;
  logic unsigned [63:0] A2B_conv_0_i;

  ent_shift_0_i = ent_shift(ent, 192'd1);
  
  B2A_conv_0_i = B2A_conv(w0.masked, w0.random, ent_shift_0_i, masked_carry, x_prime, mask, j);
  
  delta0_0_i = delta0(w1.masked);
  
  delta0_1_i = delta0(w1.random);
  
  ent_shift_1_i = ent_shift(ent, 192'd2);
  
  B2A_conv_1_i = B2A_conv(delta0_0_i, delta0_1_i, ent_shift_1_i, masked_carry, x_prime, mask, j);
  
  ent_shift_2_i = ent_shift(ent, 192'd4);
  
  B2A_conv_2_i = B2A_conv(w9.masked, w9.random, ent_shift_2_i, masked_carry, x_prime, mask, j);
  
  delta1_0_i = delta1(w14.masked);
  
  delta1_1_i = delta1(w14.random);
  
  ent_shift_3_i = ent_shift(ent, 192'd8);
  
  B2A_conv_3_i = B2A_conv(delta1_0_i, delta1_1_i, ent_shift_3_i, masked_carry, x_prime, mask, j);
  
  masked_sum_0_i = masked_sum(B2A_conv_2_i, B2A_conv_3_i);
  
  masked_sum_1_i = masked_sum(B2A_conv_1_i, masked_sum_0_i);
  
  masked_sum_2_i = masked_sum(B2A_conv_0_i, masked_sum_1_i);
  
  ent_shift_4_i = ent_shift(ent, 192'd16);
  
  A2B_conv_0_i = A2B_conv(masked_sum_2_i, m_rand, ent_shift_4_i, masked_carry, x_prime, mask, j);

  return A2B_conv_0_i;
endfunction

function logic unsigned [63:0] compute_w_random(logic unsigned [63:0] w14, logic unsigned [63:0] w9, logic unsigned [63:0] w1, logic unsigned [63:0] w0);
  logic unsigned [63:0] delta0_0_i;
  logic unsigned [63:0] delta1_0_i;
  logic unsigned [63:0] masked_sum_0_i;
  logic unsigned [63:0] masked_sum_1_i;
  logic unsigned [63:0] masked_sum_2_i;

  delta0_0_i = delta0(w1);
  
  delta1_0_i = delta1(w14);
  
  masked_sum_0_i = masked_sum(w9, delta1_0_i);
  
  masked_sum_1_i = masked_sum(delta0_0_i, masked_sum_0_i);
  
  masked_sum_2_i = masked_sum(w0, masked_sum_1_i);

  return masked_sum_2_i;
endfunction

function logic unsigned [63:0] delta0(logic unsigned [63:0] x);
  logic unsigned [63:0] rotr1_0_i;
  logic unsigned [63:0] rotr8_0_i;
  logic unsigned [63:0] shr7_0_i;
  rotr1_0_i = rotr1(x);
  
  rotr8_0_i = rotr8(x);
  
  shr7_0_i = shr7(x);

  return ((rotr1_0_i ^ rotr8_0_i) ^ shr7_0_i);
endfunction

function logic unsigned [63:0] delta1(logic unsigned [63:0] x);
  logic unsigned [63:0] rotr19_0_i;
  logic unsigned [63:0] rotr61_0_i;
  logic unsigned [63:0] shr6_0_i;
  rotr19_0_i = rotr19(x);
  
  rotr61_0_i = rotr61(x);
  
  shr6_0_i = shr6(x);

  return ((rotr19_0_i ^ rotr61_0_i) ^ shr6_0_i);
endfunction

function logic ent_shift(logic unsigned [191:0] ent, logic unsigned [191:0] i);
  return ((ent & i) == i);
endfunction

function logic unsigned [63:0] masked_Ch_m(logic unsigned [63:0] e_masked, logic unsigned [63:0] e_random, logic unsigned [63:0] f_masked, logic unsigned [63:0] f_random, logic unsigned [63:0] g_masked, logic unsigned [63:0] g_random);
  logic unsigned [63:0] masked_and_0_i;
  logic unsigned [63:0] masked_and_1_i;
  masked_and_0_i = masked_and(e_masked, e_random, f_masked, f_random);
  
  masked_and_1_i = masked_and(g_masked, g_random, ~e_masked, e_random);

  return (masked_and_0_i ^ masked_and_1_i);
endfunction

function logic unsigned [63:0] masked_Maj(logic unsigned [63:0] a_masked, logic unsigned [63:0] a_random, logic unsigned [63:0] b_masked, logic unsigned [63:0] b_random, logic unsigned [63:0] c_masked, logic unsigned [63:0] c_random);
  logic unsigned [63:0] masked_and_0_i;
  logic unsigned [63:0] masked_and_1_i;
  logic unsigned [63:0] masked_and_2_i;
  masked_and_0_i = masked_and(a_masked, a_random, b_masked, b_random);
  
  masked_and_1_i = masked_and(a_masked, a_random, c_masked, c_random);
  
  masked_and_2_i = masked_and(b_masked, b_random, c_masked, c_random);

  return ((masked_and_0_i ^ masked_and_1_i) ^ masked_and_2_i);
endfunction

function logic unsigned [63:0] masked_and(logic unsigned [63:0] x_masked, logic unsigned [63:0] x_random, logic unsigned [63:0] y_masked, logic unsigned [63:0] y_random);
  return ((~y_masked & ((~y_random & x_random) | (y_random & x_masked))) | (y_masked & ((y_random & x_random) | (~y_random & x_masked))));
endfunction

function logic unsigned [63:0] masked_sum(logic unsigned [63:0] x, logic unsigned [63:0] y);
  return 64'((x + y));
endfunction

function logic unsigned [63:0] rotr1(logic unsigned [63:0] n);
  return 64'(((n >> 64'd1) | (n << 64'd63)));
endfunction

function logic unsigned [63:0] rotr14(logic unsigned [63:0] n);
  return 64'(((n >> 64'd14) | (n << 64'd50)));
endfunction

function logic unsigned [63:0] rotr18(logic unsigned [63:0] n);
  return 64'(((n >> 64'd18) | (n << 64'd46)));
endfunction

function logic unsigned [63:0] rotr19(logic unsigned [63:0] n);
  return 64'(((n >> 64'd19) | (n << 64'd45)));
endfunction

function logic unsigned [63:0] rotr28(logic unsigned [63:0] n);
  return 64'(((n >> 64'd28) | (n << 64'd36)));
endfunction

function logic unsigned [63:0] rotr34(logic unsigned [63:0] n);
  return 64'(((n >> 64'd34) | (n << 64'd30)));
endfunction

function logic unsigned [63:0] rotr39(logic unsigned [63:0] n);
  return 64'(((n >> 64'd39) | (n << 64'd25)));
endfunction

function logic unsigned [63:0] rotr41(logic unsigned [63:0] n);
  return 64'(((n >> 64'd41) | (n << 64'd23)));
endfunction

function logic unsigned [63:0] rotr61(logic unsigned [63:0] n);
  return 64'(((n >> 64'd61) | (n << 64'd3)));
endfunction

function logic unsigned [63:0] rotr8(logic unsigned [63:0] n);
  return 64'(((n >> 64'd8) | (n << 64'd56)));
endfunction

function logic unsigned [63:0] shr6(logic unsigned [63:0] n);
  return (n >> 64'd6);
endfunction

function logic unsigned [63:0] shr7(logic unsigned [63:0] n);
  return (n >> 64'd7);
endfunction

function logic unsigned [63:0] sigma0(logic unsigned [63:0] x);
  logic unsigned [63:0] rotr28_0_i;
   logic unsigned [63:0] rotr34_0_i;
   logic unsigned [63:0] rotr39_0_i;
  rotr28_0_i = rotr28(x);
 
  rotr34_0_i = rotr34(x);
  
  rotr39_0_i = rotr39(x);

  return ((rotr28_0_i ^ rotr34_0_i) ^ rotr39_0_i);
endfunction

function logic unsigned [63:0] sigma1(logic unsigned [63:0] x);
  logic unsigned [63:0] rotr14_0_i;
  logic unsigned [63:0] rotr18_0_i;
  logic unsigned [63:0] rotr41_0_i;
  rotr14_0_i = rotr14(x);
  
  rotr18_0_i = rotr18(x);
  
  rotr41_0_i = rotr41(x);

  return ((rotr14_0_i ^ rotr18_0_i) ^ rotr41_0_i);
endfunction

function logic unsigned [63:0] slicer(logic unsigned [1023:0] block, logic signed [31:0] index);
  if ((index == 'sd0))
    return 64'((block >> 1024'd0));
  else if ((index == 'sd1))
    return 64'((block >> 1024'd64));
  else if ((index == 'sd2))
    return 64'((block >> 1024'd128));
  else if ((index == 'sd3))
    return 64'((block >> 1024'd192));
  else if ((index == 'sd4))
    return 64'((block >> 1024'd256));
  else if ((index == 'sd5))
    return 64'((block >> 1024'd320));
  else if ((index == 'sd6))
    return 64'((block >> 1024'd384));
  else if ((index == 'sd7))
    return 64'((block >> 1024'd448));
  else if ((index == 'sd8))
    return 64'((block >> 1024'd512));
  else if ((index == 'sd9))
    return 64'((block >> 1024'd576));
  else if ((index == 'sd10))
    return 64'((block >> 1024'd640));
  else if ((index == 'sd11))
    return 64'((block >> 1024'd704));
  else if ((index == 'sd12))
    return 64'((block >> 1024'd768));
  else if ((index == 'sd13))
    return 64'((block >> 1024'd832));
  else if ((index == 'sd14))
    return 64'((block >> 1024'd896));
  else if ((index == 'sd15))
    return 64'((block >> 1024'd960));
  else
    return 64'((block >> 1024'd960));
endfunction


endpackage
