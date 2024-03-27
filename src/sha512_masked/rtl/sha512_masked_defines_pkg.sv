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
`ifndef CALIPTRA_SHA512_MASKED_DEFINES_PKG
`define CALIPTRA_SHA512_MASKED_DEFINES_PKG

package sha512_masked_defines_pkg;

  typedef struct packed {
    reg   [63:0]  masked;
    reg   [63:0]  random;
  } masked_reg_t;

  //----------------------------------------------------------------
  // Function definition.
  //----------------------------------------------------------------
  function automatic masked_reg_t masked_not (input masked_reg_t x);
    return {~x.masked, x.random};
  endfunction

  function automatic reg [63:0] masked_and (input masked_reg_t x, y);
    return ~y.masked & (~y.random & x.random | y.random & x.masked) | y.masked & (y.random & x.random | ~y.random & x.masked); //x & y;
  endfunction

  function automatic masked_reg_t masked_maj (input masked_reg_t a, b, c);
    return {masked_and(a, b) ^ masked_and(a, c) ^ masked_and(b, c), b.random};
  endfunction

  function automatic masked_reg_t masked_ch (input masked_reg_t e, f, g);
    return {masked_and(e, f) ^ masked_and(g, masked_not(e)), e.random ^ g.random};
  endfunction

  function automatic reg [63:0] sigma0 (input reg [63:0] x);
    return {x[27 : 0], x[63 : 28]} ^
           {x[33 : 0], x[63 : 34]} ^
           {x[38 : 0], x[63 : 39]};
  endfunction

  function automatic reg [63:0] sigma1 (input reg [63:0] x);
    return {x[13 : 0], x[63 : 14]} ^
           {x[17 : 0], x[63 : 18]} ^
           {x[40 : 0], x[63 : 41]};
  endfunction

  function automatic reg [63:0] ROT1 (input reg [63:0] x);
    return {x[0],       x[63 : 1]} ^ // ROTR1
           {x[7 : 0],   x[63 : 8]} ^ // ROTR8
           {7'b0000000, x[63 : 7]};  // SHR7           
  endfunction
  
  function automatic reg [63:0] ROT14 (input reg [63:0] x);
    return {x[18 : 0], x[63 : 19]} ^ // ROTR19
           {x[60 : 0], x[63 : 61]} ^ // ROTR61
           {6'b000000, x[63 : 6]};   // SHR6          
  endfunction
  
  function automatic masked_reg_t masked_sum (input masked_reg_t x, y);
    return {(x.masked + y.masked), (x.random + y.random)};
  endfunction

  function automatic masked_reg_t B2A_conv (input masked_reg_t x, logic q); // convert x_masked = x ^ rnd to x_prime = x + rand
    reg [63 : 0] masked_carry;  // masked_carry[j] = c[j] ^ q
    reg [63 : 0] x_prime;
    for (int j = 0; j < 64 ; j++) begin
        if (j == 0) begin
          masked_carry[j] = ~x.masked[j] & (x.random[j] ^ q) | (x.masked[j] & q);
          x_prime[j] = x.masked[j];
        end
        else begin
          masked_carry[j] = ~x.masked[j] & (x.random[j] ^ q) | x.masked[j] & masked_carry[j-1];
          x_prime[j] = (x.masked[j] ^ masked_carry[j-1]) ^ q;
        end
    end
    return {x_prime, x.random};
  endfunction

  function automatic masked_reg_t A2B_conv (input masked_reg_t x, logic q); // convert x_prime = x + rand to x_masked = x ^ rnd
    reg [63 : 0] masked_carry;  // masked_carry[j] = c[j] ^ q
    reg [63 : 0] x_masked;
 
    for (int j = 0; j < 64 ; j++) begin
      if (j == 0) begin
        masked_carry[j] = (~x.masked[0] & x.random[0]) ^ q;
        x_masked[j] = x.masked[j];
      end
      else begin
        masked_carry[j] = (x.masked[j] ^ x.random[j]) & (x.random[j] ^ q) | (~x.masked[j] ^ x.random[j]) & masked_carry[j-1];
        x_masked[j] = (x.masked[j] ^ masked_carry[j-1]) ^ q;
      end
    end
    return {x_masked, x.random};
  endfunction

endpackage

`endif
