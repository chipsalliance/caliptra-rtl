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

import doe_core_cbc_pkg::*;

module fv_encrypt_checker_m	(
  
  ////////////////////////////
  // Input / Output signals //
  ////////////////////////////
  input            clk,
  input            reset_n,

  input            next_cmd,

  input            keylen,
  input [3 : 0]    round,
  input [127 : 0]  round_key,

  input [31 : 0]   sboxw,
  input  [31 : 0]  new_sboxw,

  input [127 : 0]  block_msg,
  input [127 : 0]  new_block,
  input            ready,

	//////////////////////
 	//       States     //
 	//////////////////////

  input IDLE,
  input Round_Compute,

  //////////////////////
 	// Internal Signals //
 	//////////////////////
  input [127 : 0] block_new,
  input [127 : 0] old_block,

  //Signal for expanded keys
  input [127 : 0]  fv_round_key_array[14:0]

);

//localparams - Respective delays
localparam DLY_128 = 52; //no. of cycles the decryption takes for 128B configuration
localparam DLY_256 = 72; //no. of cycles the decryption takes for 256B configuration
localparam DLY_RND = 5;  //no. of cycles the round computation takes
localparam DLY_SBOX = 4; //no. of cycles the SBOX computation takes

//Compute Intermediate steps in each round
function logic [127 : 0] compute_round_encrypt(input logic [127 : 0] index_msg, input logic [3:0] int_rnd);
  logic [127:0] int_msg;
  logic [31:0] int_word[0:3];

  int_msg = index_msg;
  
      //Round encryption
      for (int i = 0; i < 4; i++)
        int_word[3-i] = int_msg[i*32 +: 32];

      for (int i = 0; i < 4; i++)
        int_word[i] = get_sbox(int_word[i]);

      int_msg = {int_word[0],int_word[1],int_word[2],int_word[3]};

      int_msg = compute_shiftrow(int_msg);

      int_msg = compute_mixcolums_msg(int_msg);

      int_msg = compute_add_round_key(int_msg, fv_round_key_array[int_rnd]);

  return int_msg;
endfunction

//Compute intermediate steps in last round
function logic [127 : 0] compute_lastround(input logic [127 : 0] index_msg, input logic [3:0] int_rnd);
  logic [127:0] int_msg;
  logic [31:0] int_word[0:3];

  int_msg = index_msg;
  
      //Round encryption
      for (int i = 0; i < 4; i++)
        int_word[3-i] = int_msg[i*32 +: 32];

      for (int i = 0; i < 4; i++)
        int_word[i] = get_sbox(int_word[i]);

      int_msg = {int_word[0],int_word[1],int_word[2],int_word[3]};

      int_msg = compute_shiftrow(int_msg);

      int_msg = compute_add_round_key(int_msg, fv_round_key_array[int_rnd]);

  return int_msg;
endfunction

//Compute AES_Encryption 128
function logic [127 : 0] compute_aes_encryption_128(input logic [127 : 0] index_msg);
  logic [127:0] int_msg;
  logic [31:0] int_word[0:3];

  int_msg = index_msg;
  
  //Initial Step
  int_msg = compute_add_round_key(int_msg, fv_round_key_array[0]);
 
  //Round encryption
  for (int rnd = 1; rnd < 10; rnd++) begin
      //Round encryption
      int_msg = compute_round_encrypt(int_msg, rnd);
  end

  //Final Round
  int_msg = compute_lastround(int_msg, 4'ha);

  return int_msg;
endfunction

//Compute AES_Encryption 256
function logic [127 : 0] compute_aes_encryption_256(input logic [127 : 0] index_msg);
  logic [127:0] int_msg;
  logic [31:0] int_word[0:3];

  int_msg = index_msg;
  
  //Initial Step
  int_msg = compute_add_round_key(int_msg, fv_round_key_array[0]);
 
  //Round encryption
  for (int rnd = 1; rnd < 14; rnd++) begin
      //Round encryption
      int_msg = compute_round_encrypt(int_msg, rnd);
  end

  //Final Round 
  int_msg = compute_lastround(int_msg, 4'he);

  return int_msg;
endfunction

////////////////////////
//   Default Clock    //
////////////////////////
default clocking default_clk @(posedge clk); endclocking

//////////////////////////////////////
//  Encryption Checker Properties  //
////////////////////////////////////

// Checks if the design is in IDLE state and ready is low
reset_a: assert property (reset_p);
property reset_p;
  $past(!reset_n)  
|->
  IDLE &&
  ready == 1 
;endproperty

// Checks if block produces correct 128 bit encrypted value
encryption_check_128_a: assert property (disable iff(!reset_n) encryption_check_128_p);
property encryption_check_128_p;
  logic [127:0] result, tracked_blk_msg;

  ##0 next_cmd 
  ##0 !keylen 
  ##0 (1'b1, tracked_blk_msg = block_msg)
  ##DLY_128 (1'b1, result = compute_aes_encryption_128(tracked_blk_msg)) 
|->
  ##0 new_block == result
  ##0 ready 
;endproperty

// Checks if block produces correct sequence of round outputs for 128 bit configuration
round_check_128_a: assert property (disable iff(!reset_n) round_check_128_p);
property round_check_128_p;
  ##0 next_cmd 
  ##0 !keylen 
|->
  ##1 round == 0 && !ready
  ##1 round == 1 && !ready[*DLY_RND]
  ##1 round == 2 && !ready[*DLY_RND]
  ##1 round == 3 && !ready[*DLY_RND]
  ##1 round == 4 && !ready[*DLY_RND]
  ##1 round == 5 && !ready[*DLY_RND]
  ##1 round == 6 && !ready[*DLY_RND]
  ##1 round == 7 && !ready[*DLY_RND]
  ##1 round == 8 && !ready[*DLY_RND]
  ##1 round == 9 && !ready[*DLY_RND]
  ##1 round == 10 && !ready[*DLY_RND]
  ##1 ready
;endproperty

// Checks if block produces correct 256 bit encrypted value
encryption_check_256_a: assert property (disable iff(!reset_n) encryption_check_256_p);
property encryption_check_256_p;
  logic [127:0] result, tracked_blk_msg;

  ##0 next_cmd 
  ##0 keylen 
  ##0 (1'b1, tracked_blk_msg = block_msg)
  ##DLY_256 (1'b1, result = compute_aes_encryption_256(tracked_blk_msg)) 
|->
  ##0 new_block == result
  ##0 ready 
;endproperty

// Checks if block produces correct sequence of round outputs for 256 bit configuration
round_check_256_a: assert property (disable iff(!reset_n) round_check_256_p);
property round_check_256_p;
  ##0 next_cmd 
  ##0 keylen 
|->
  ##1 round == 0
  ##1 round == 1   && !ready[*DLY_RND]
  ##1 round == 2   && !ready[*DLY_RND]
  ##1 round == 3   && !ready[*DLY_RND]
  ##1 round == 4   && !ready[*DLY_RND]
  ##1 round == 5   && !ready[*DLY_RND]
  ##1 round == 6   && !ready[*DLY_RND]
  ##1 round == 7   && !ready[*DLY_RND]
  ##1 round == 8   && !ready[*DLY_RND]
  ##1 round == 9   && !ready[*DLY_RND]
  ##1 round == 10  && !ready[*DLY_RND]
  ##1 round == 11  && !ready[*DLY_RND]
  ##1 round == 12  && !ready[*DLY_RND]
  ##1 round == 13  && !ready[*DLY_RND]
  ##1 round == 14  && !ready[*DLY_RND]
  ##1 ready
;endproperty

// Checks if block produces correct round encrypted value for each round in 128 bit configuration
for (genvar rnd = 1; rnd < 10; rnd++) begin: rndcompute_128
  round_compute_128_a: assert property (disable iff(!reset_n) round_compute_128_p(rnd));
end
property round_compute_128_p(rndcnt);
  logic [127:0] result;
  ##0 Round_Compute && !keylen
  ##1 round == rndcnt
  ##0 (1'b1, result = compute_round_encrypt(old_block,rndcnt))
|->
  ##DLY_SBOX block_new == result
;endproperty

// Checks if block produces correct round encrypted value for each round in 256 bit configuration
for (genvar rnd = 1; rnd < 14; rnd++) begin: rndcompute_256
  round_compute_256_a: assert property (disable iff(!reset_n) round_compute_256_p(rnd));
end
property round_compute_256_p(rndcnt);
  logic [127:0] result;
  ##0 Round_Compute && keylen
  ##1 round == rndcnt
  ##0 (1'b1, result = compute_round_encrypt(old_block,rndcnt))
|->
  ##DLY_SBOX block_new == result
;endproperty

// Checks if block produces correct round encrypted value for last round in 128 bit configuration
lastround_computation_128_a: assert property (disable iff(!reset_n) lastround_computation_128_p);
property lastround_computation_128_p;
  logic [127:0] result;
  ##0 Round_Compute && !keylen
  ##1 round == 4'ha
  ##0 (1'b1, result = compute_lastround(old_block,4'ha))
|->
  ##DLY_SBOX block_new == result
;endproperty

// Checks if block produces correct round encrypted value for last round in 256 bit configuration
lastround_computation_256_a: assert property (disable iff(!reset_n) lastround_computation_256_p);
property lastround_computation_256_p;
  logic [127:0] result;
  ##0 Round_Compute && keylen
  ##1 round == 4'he
  ##0 (1'b1, result = compute_lastround(old_block,4'he))
|->
  ##DLY_SBOX block_new == result
;endproperty

// Checks if block produces correct encrypted value for the first round
firstround_compute_a: assert property (disable iff(!reset_n) firstround_compute_p);
property firstround_compute_p;
  logic [127:0] result, tracked_blk_msg;

  ##0 next_cmd 
  ##0 (1'b1, tracked_blk_msg = block_msg)
  ##0 (1'b1, result = compute_add_round_key(tracked_blk_msg, fv_round_key_array[0]))
|->
  ##1 block_new == result
;endproperty

endmodule

//Inputs driven from doe_core_cbc
`ifdef CBC_BIND

  bind doe_encipher_block fv_encrypt_checker_m 
  fv_encrypt(
    .clk(doe_core_cbc.enc_block.clk),
    .reset_n(doe_core_cbc.enc_block.reset_n && !doe_core_cbc.enc_block.zeroize),
    .next_cmd(doe_core_cbc.enc_block.next_cmd),
    .keylen(doe_core_cbc.enc_block.keylen),
    .round(doe_core_cbc.enc_block.round),
    .round_key(doe_core_cbc.enc_block.round_key),
    .sboxw(doe_core_cbc.enc_block.sboxw),
    .new_sboxw(doe_core_cbc.enc_block.new_sboxw),
    .block_msg(doe_core_cbc.enc_block.block_msg),
    .new_block(doe_core_cbc.enc_block.new_block),
    .ready(doe_core_cbc.enc_block.ready),
    .IDLE(doe_core_cbc.enc_block.enc_ctrl_reg == 0),
    .Round_Compute((doe_core_cbc.enc_block.enc_ctrl_reg == 2'h1) || (doe_core_cbc.enc_block.enc_ctrl_reg == 2'h3)),
    .old_block(doe_core_cbc.enc_block.round_logic.old_block),
    .block_new(doe_core_cbc.enc_block.block_new),
    .fv_round_key_array(doe_core_cbc.keymem.key_mem)
  );

//Inputs driven with constraints on doe_encipher_block
`else

  bind doe_encipher_block fv_encrypt_checker_m 
  fv_encrypt(.*,
    .clk(clk),
    .reset_n(reset_n && !zeroize),
    .IDLE(enc_ctrl_reg == 0),
    .Round_Compute((enc_ctrl_reg == 2'h1) || (enc_ctrl_reg == 2'h3)),
    .old_block(round_logic.old_block),
    .block_new(block_new),
    .fv_round_key_array(fv_enc_constraints.fv_round_key_array)
  );

`endif
