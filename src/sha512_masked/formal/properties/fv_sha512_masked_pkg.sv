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
 
package sha512_masked_pkg;


typedef struct {
  bit unsigned [1023:0] in;
  bit signed [31:0] SHA_Mode;
  bit init_cmd;
  bit next_cmd;
  bit zeroize;
} st_SHA_Args;

typedef struct {
  bit unsigned [63:0] masked;
  bit unsigned [63:0] random;
} st_masked_reg_t;

typedef bit a_bool_10 [9:0];

typedef bit unsigned [63:0] a_sc_big_unsigned_64_16 [15:0];

typedef bit unsigned [63:0] a_sc_big_unsigned_64_8 [7:0];

typedef bit unsigned [63:0] a_sc_big_unsigned_64_80 [79:0];


// Constants

parameter a_sc_big_unsigned_64_80 K = '{ 0: 64'h428A2F98D728AE22, 1: 64'h7137449123EF65CD, 2: 64'hB5C0FBCFEC4D3B2F, 3: 64'hE9B5DBA58189DBBC, 4: 64'h3956C25BF348B538, 5: 64'h59F111F1B605D019, 6: 64'h923F82A4AF194F9B, 7: 64'hAB1C5ED5DA6D8118, 8: 64'hD807AA98A3030242, 9: 64'h12835B0145706FBE, 10: 64'h243185BE4EE4B28C, 11: 64'h550C7DC3D5FFB4E2, 12: 64'h72BE5D74F27B896F, 13: 64'h80DEB1FE3B1696B1, 14: 64'h9BDC06A725C71235, 15: 64'hC19BF174CF692694, 16: 64'hE49B69C19EF14AD2, 17: 64'hEFBE4786384F25E3, 18: 64'hFC19DC68B8CD5B5, 19: 64'h240CA1CC77AC9C65, 20: 64'h2DE92C6F592B0275, 21: 64'h4A7484AA6EA6E483, 22: 64'h5CB0A9DCBD41FBD4, 23: 64'h76F988DA831153B5, 24: 64'h983E5152EE66DFAB, 25: 64'hA831C66D2DB43210, 26: 64'hB00327C898FB213F, 27: 64'hBF597FC7BEEF0EE4, 28: 64'hC6E00BF33DA88FC2, 29: 64'hD5A79147930AA725, 30: 64'h6CA6351E003826F, 31: 64'h142929670A0E6E70, 32: 64'h27B70A8546D22FFC, 33: 64'h2E1B21385C26C926, 34: 64'h4D2C6DFC5AC42AED, 35: 64'h53380D139D95B3DF, 36: 64'h650A73548BAF63DE, 37: 64'h766A0ABB3C77B2A8, 38: 64'h81C2C92E47EDAEE6, 39: 64'h92722C851482353B, 40: 64'hA2BFE8A14CF10364, 41: 64'hA81A664BBC423001, 42: 64'hC24B8B70D0F89791, 43: 64'hC76C51A30654BE30, 44: 64'hD192E819D6EF5218, 45: 64'hD69906245565A910, 46: 64'hF40E35855771202A, 47: 64'h106AA07032BBD1B8, 48: 64'h19A4C116B8D2D0C8, 49: 64'h1E376C085141AB53, 50: 64'h2748774CDF8EEB99, 51: 64'h34B0BCB5E19B48A8, 52: 64'h391C0CB3C5C95A63, 53: 64'h4ED8AA4AE3418ACB, 54: 64'h5B9CCA4F7763E373, 55: 64'h682E6FF3D6B2B8A3, 56: 64'h748F82EE5DEFB2FC, 57: 64'h78A5636F43172F60, 58: 64'h84C87814A1F0AB72, 59: 64'h8CC702081A6439EC, 60: 64'h90BEFFFA23631E28, 61: 64'hA4506CEBDE82BDE9, 62: 64'hBEF9A3F7B2C67915, 63: 64'hC67178F2E372532B, 64: 64'hCA273ECEEA26619C, 65: 64'hD186B8C721C0C207, 66: 64'hEADA7DD6CDE0EB1E, 67: 64'hF57D4F7FEE6ED178, 68: 64'h6F067AA72176FBA, 69: 64'hA637DC5A2C898A6, 70: 64'h113F9804BEF90DAE, 71: 64'h1B710B35131C471B, 72: 64'h28DB77F523047D84, 73: 64'h32CAAB7B40C72493, 74: 64'h3C9EBE0A15C9BEBC, 75: 64'h431D67C49C100D4C, 76: 64'h4CC5D4BECB3E42B6, 77: 64'h597F299CFC657E2A, 78: 64'h5FCB6FAB3AD6FAEC, 79: 64'h6C44198C4A475817 };


// Functions

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

function bit unsigned [63:0] T1_m(bit unsigned [63:0] e_masked, bit unsigned [63:0] e_random, bit unsigned [63:0] f_masked, bit unsigned [63:0] f_random, bit unsigned [63:0] g_masked, bit unsigned [63:0] g_random, bit unsigned [63:0] h_masked, bit unsigned [63:0] h_random, bit unsigned [63:0] k, bit unsigned [63:0] w_masked, bit unsigned [63:0] w_random, bit masked_carry, bit unsigned [127:0] x_prime, bit unsigned [63:0] mask, bit q_masking_rnd_0, bit q_masking_rnd_1, bit q_masking_rnd_2, bit q_masking_rnd_3, bit q_masking_rnd_4, bit signed [31:0] j);
  return 64'(((((B2A_conv(h_masked, h_random, q_masking_rnd_0, masked_carry, x_prime, mask, j) + B2A_conv(sigma1(e_masked), sigma1(e_random), q_masking_rnd_1, masked_carry, x_prime, mask, j)) + B2A_conv(masked_Ch_m(e_masked, e_random, f_masked, f_random, g_masked, g_random), (e_random ^ g_random), q_masking_rnd_2, masked_carry, x_prime, mask, j)) + B2A_conv(k, 64'h0, q_masking_rnd_3, masked_carry, x_prime, mask, j)) + B2A_conv(w_masked, w_random, q_masking_rnd_4, masked_carry, x_prime, mask, j)));
endfunction

function bit unsigned [63:0] T1_r(bit unsigned [63:0] e_random, bit unsigned [63:0] g_random, bit unsigned [63:0] h_random, bit unsigned [63:0] w_random);
  return 64'((((h_random + sigma1(e_random)) + (e_random ^ g_random)) + w_random));
endfunction

function bit unsigned [63:0] T2_m(bit unsigned [63:0] a_masked, bit unsigned [63:0] a_random, bit unsigned [63:0] b_masked, bit unsigned [63:0] b_random, bit unsigned [63:0] c_masked, bit unsigned [63:0] c_random, bit masked_carry, bit unsigned [127:0] x_prime, bit unsigned [63:0] mask, bit q_masking_rnd_5, bit q_masking_rnd_6, bit signed [31:0] j);
  return 64'((B2A_conv(sigma0(a_masked), sigma0(a_random), q_masking_rnd_5, masked_carry, x_prime, mask, j) + B2A_conv(masked_Maj(a_masked, a_random, b_masked, b_random, c_masked, c_random), b_random, q_masking_rnd_6, masked_carry, x_prime, mask, j)));
endfunction

function bit unsigned [63:0] T2_r(bit unsigned [63:0] a_random, bit unsigned [63:0] b_random);
  return 64'((sigma0(a_random) + b_random));
endfunction

function bit unsigned [63:0] compute_w(bit unsigned [63:0] w14, bit unsigned [63:0] w9, bit unsigned [63:0] w1, bit unsigned [63:0] w0);
  return 64'((((delta1(w14) + w9) + delta0(w1)) + w0));
endfunction

function bit unsigned [63:0] delta0(bit unsigned [63:0] x);
  return ((rotr1(x) ^ rotr8(x)) ^ shr7(x));
endfunction

function bit unsigned [63:0] delta1(bit unsigned [63:0] x);
  return ((rotr19(x) ^ rotr61(x)) ^ shr6(x));
endfunction

function bit unsigned [63:0] masked_Ch_m(bit unsigned [63:0] e_masked, bit unsigned [63:0] e_random, bit unsigned [63:0] f_masked, bit unsigned [63:0] f_random, bit unsigned [63:0] g_masked, bit unsigned [63:0] g_random);
  return (masked_and(e_masked, e_random, f_masked, f_random) ^ masked_and(g_masked, g_random, ~e_masked, e_random));
endfunction

function bit unsigned [63:0] masked_Maj(bit unsigned [63:0] a_masked, bit unsigned [63:0] a_random, bit unsigned [63:0] b_masked, bit unsigned [63:0] b_random, bit unsigned [63:0] c_masked, bit unsigned [63:0] c_random);
  return ((masked_and(a_masked, a_random, b_masked, b_random) ^ masked_and(a_masked, a_random, c_masked, c_random)) ^ masked_and(b_masked, b_random, c_masked, c_random));
endfunction

function bit unsigned [63:0] masked_and(bit unsigned [63:0] x_masked, bit unsigned [63:0] x_random, bit unsigned [63:0] y_masked, bit unsigned [63:0] y_random);
  return ((~y_masked & ((~y_random & x_random) | (y_random & x_masked))) | (y_masked & ((y_random & x_random) | (~y_random & x_masked))));
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

function bit unsigned [511:0] compute_digest(bit unsigned [63:0] H_7, bit unsigned [63:0] h_random , bit unsigned [63:0] h_masked, bit unsigned [63:0] H_6, bit unsigned [63:0] g_random , bit unsigned [63:0] g_masked, bit unsigned [63:0] H_5,  bit unsigned [63:0] f_random , bit unsigned [63:0] f_masked, bit unsigned [63:0] H_4, bit unsigned [63:0] e_random , bit unsigned [63:0] e_masked, bit unsigned [63:0] H_3, bit unsigned [63:0] d_random , bit unsigned [63:0] d_masked, bit unsigned [63:0] H_2, bit unsigned [63:0] c_random , bit unsigned [63:0] c_masked, bit unsigned [63:0] H_1, bit unsigned [63:0] b_random , bit unsigned [63:0] b_masked, bit unsigned [63:0] H_0, bit unsigned [63:0] a_random , bit unsigned [63:0] a_masked);
  bit unsigned [511:0] temp;
    temp[63:0]    = 64'(H_7 + (h_masked ^ h_random));
    temp[127:64]  = 64'(H_6 + (g_masked ^ g_random));
    temp[191:128] = 64'(H_5 + (f_masked ^ f_random));
    temp[255:192] = 64'(H_4 + (e_masked ^ e_random));
    temp[319:256] = 64'(H_3 + (d_masked ^ d_random));
    temp[383:320] = 64'(H_2 + (c_masked ^ c_random));
    temp[447:384] = 64'(H_1 + (b_masked ^ b_random));
    temp[511:448] = 64'(H_0 + (a_masked ^ a_random));
  return temp;
 endfunction

endpackage
