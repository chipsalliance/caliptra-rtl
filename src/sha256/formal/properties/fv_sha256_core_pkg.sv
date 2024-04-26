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

package fv_sha256_core_pkg;

typedef bit unsigned [31:0] a_unsigned_32_64 [63:0];

// Constants

parameter a_unsigned_32_64 K = '{ 0:'h428A2F98, 1:'h71374491, 2:'hB5C0FBCF, 3:'hE9B5DBA5, 4:'h3956C25B, 5:'h59F111F1, 6:'h923F82A4, 7:'hAB1C5ED5, 8:'hD807AA98, 9:'h12835B01, 10:'h243185BE, 11:'h550C7DC3, 12:'h72BE5D74, 13:'h80DEB1FE, 14:'h9BDC06A7, 15:'hC19BF174, 16:'hE49B69C1, 17:'hEFBE4786, 18:'hFC19DC6, 19:'h240CA1CC, 20:'h2DE92C6F, 21:'h4A7484AA, 22:'h5CB0A9DC, 23:'h76F988DA, 24:'h983E5152, 25:'hA831C66D, 26:'hB00327C8, 27:'hBF597FC7, 28:'hC6E00BF3, 29:'hD5A79147, 30:'h6CA6351, 31:'h14292967, 32:'h27B70A85, 33:'h2E1B2138, 34:'h4D2C6DFC, 35:'h53380D13, 36:'h650A7354, 37:'h766A0ABB, 38:'h81C2C92E, 39:'h92722C85, 40:'hA2BFE8A1, 41:'hA81A664B, 42:'hC24B8B70, 43:'hC76C51A3, 44:'hD192E819, 45:'hD6990624, 46:'hF40E3585, 47:'h106AA070, 48:'h19A4C116, 49:'h1E376C08, 50:'h2748774C, 51:'h34B0BCB5, 52:'h391C0CB3, 53:'h4ED8AA4A, 54:'h5B9CCA4F, 55:'h682E6FF3, 56:'h748F82EE, 57:'h78A5636F, 58:'h84C87814, 59:'h8CC70208, 60:'h90BEFFFA, 61:'hA4506CEB, 62:'hBEF9A3F7, 63:'hC67178F2 };


// Functions

function bit unsigned [31:0] Summ(bit unsigned [31:0] x, bit unsigned [31:0] y, bit unsigned [31:0] z, bit unsigned [31:0] m, bit unsigned [31:0] e);
  return ((((x + y) + z) + m) + e);
endfunction

function bit unsigned [31:0] choose(bit unsigned [31:0] e, bit unsigned [31:0] f, bit unsigned [31:0] g);
  return ((e & f) ^ (~e & g));
endfunction

function bit unsigned [31:0] compute_w(bit unsigned [31:0] m14, bit unsigned [31:0] m9, bit unsigned [31:0] m1, bit unsigned [31:0] m0);
  return (((sig1(m14) + m9) + sig0(m1)) + m0);
endfunction

function bit unsigned [31:0] majority(bit unsigned [31:0] a, bit unsigned [31:0] b, bit unsigned [31:0] c);
  return ((a & (b | c)) | (b & c));
endfunction

function bit unsigned [31:0] mult_xor(bit unsigned [31:0] x, bit unsigned [31:0] a, bit unsigned [31:0] b, bit unsigned [31:0] c);
  return ((rotr(x, a) ^ rotr(x, b)) ^ rotr(x, c));
endfunction

function bit unsigned [31:0] newa(bit unsigned [31:0] x, bit unsigned [31:0] y, bit unsigned [31:0] z);
  return ((x + y) + z);
endfunction

function bit unsigned [31:0] newe(bit unsigned [31:0] x, bit unsigned [31:0] y);
  return (x + y);
endfunction

function bit unsigned [31:0] past_m(bit unsigned [5:0]i,bit unsigned [31:0] m_0,bit unsigned [31:0] m_1,bit unsigned [31:0] m_2,bit unsigned [31:0] m_3,bit unsigned [31:0] m_4,bit unsigned [31:0] m_5,bit unsigned [31:0] m_6,bit unsigned [31:0] m_7,bit unsigned [31:0] m_8,bit unsigned [31:0] m_9,bit unsigned [31:0] m_10,bit unsigned [31:0] m_11,bit unsigned [31:0] m_12,bit unsigned [31:0] m_13,bit unsigned [31:0] m_14,bit unsigned [31:0] m_15);
  return ((i == 'sd0 ? m_0 : (i == 'sd1) ? m_1 : (i == 'sd2) ? m_2 : (i == 'sd3) ? m_3 : (i == 'sd4) ? m_4 : (i == 'sd5) ? m_5 : (i == 'sd6) ? m_6 : (i == 'sd7) ? m_7 : (i == 'sd8) ? m_8 : (i == 'sd9) ? m_9 : (i == 'sd10) ? m_10 : (i == 'sd11) ? m_11 : (i == 'sd12) ? m_12 : (i == 'sd13) ? m_13 : (i == 'sd14) ? m_14 : m_15));
endfunction

function bit unsigned [31:0] rotr(bit unsigned [31:0] x, bit unsigned [31:0] n);
  return ((x >> n) | (x << (32 - n)));
endfunction

function bit unsigned [31:0] sig0(bit unsigned [31:0] x);
  return ((rotr(x, 7) ^ rotr(x, 18)) ^ (x >> 3));
endfunction

function bit unsigned [31:0] sig1(bit unsigned [31:0] x);
  return ((rotr(x, 17) ^ rotr(x, 19)) ^ (x >> 10));
endfunction


endpackage
