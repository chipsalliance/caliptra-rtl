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

module fv_decrypt_checker_m	(
  
  ////////////////////////////
  // Input / Output signals //
  ////////////////////////////
  input            clk,
  input            reset_n,

  input            next_cmd,

  input            keylen,
  input [3 : 0]    round,
  input [127 : 0]  round_key,

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

//Compute first round intermediate step value for both 128/256 bit configuration
function logic [127 : 0] compute_firstdecrypt(input logic [127 : 0] index_msg, input logic mode);
  logic [127:0] int_msg;
  logic [31:0] int_word[0:3];

  int_msg = index_msg;
  
  //Initial Step
  if(mode) int_msg = compute_add_round_key(int_msg, fv_round_key_array[14]);
  else int_msg = compute_add_round_key(int_msg, fv_round_key_array[10]);

  int_msg = compute_invshiftrow(int_msg);

  return int_msg;
endfunction

//Compute Intermediate steps in each round
function logic [127 : 0] compute_round_decrypt(input logic [127 : 0] index_msg, input logic [3:0] int_rnd);
  logic [127:0] int_msg;
  logic [31:0] int_word[0:3];

  int_msg = index_msg;
  
  //Round encryption
  for (int i = 0; i < 4; i++)
    int_word[3-i] = int_msg[i*32 +: 32];

  for (int i = 0; i < 4; i++)
    int_word[i] = get_invsbox(int_word[i]);

  int_msg = {int_word[0],int_word[1],int_word[2],int_word[3]};

  int_msg = compute_add_round_key(int_msg, fv_round_key_array[int_rnd-1]);

  int_msg = compute_invmixcolums_msg(int_msg);
  
  int_msg = compute_invshiftrow(int_msg);

  return int_msg;
endfunction

//Compute Intermediate step value in last round for both 128/256 bit configuration
function logic [127 : 0] compute_lastround_decrypt(input logic [127 : 0] index_msg);
  logic [127:0] int_msg;
  logic [31:0] int_word[0:3];

  int_msg = index_msg;
  
  //Round encryption
  for (int i = 0; i < 4; i++)
    int_word[3-i] = int_msg[i*32 +: 32];

  for (int i = 0; i < 4; i++)
    int_word[i] = get_invsbox(int_word[i]);

  int_msg = {int_word[0],int_word[1],int_word[2],int_word[3]};

  int_msg = compute_add_round_key(int_msg, fv_round_key_array[0]);

  return int_msg;
endfunction

//Compute AES_Decryption for 128 bit configuration
function logic [127 : 0] compute_aes_decryption_128(input logic [127 : 0] index_msg);
  logic [127:0] int_msg;
  logic [31:0] int_word[0:3];

  int_msg = index_msg;
  
  //Initial Step
  int_msg = compute_add_round_key(int_msg, fv_round_key_array[10]);

  int_msg = compute_invshiftrow(int_msg);

  //Round encryption
  for (int rnd = 9; rnd > 0; rnd--) begin

      //Round decryption
      for (int i = 0; i < 4; i++)
        int_word[3-i] = int_msg[i*32 +: 32];

      for (int i = 0; i < 4; i++)
        int_word[i] = get_invsbox(int_word[i]);

      int_msg = {int_word[0],int_word[1],int_word[2],int_word[3]};

      int_msg = compute_add_round_key(int_msg, fv_round_key_array[rnd]);

      int_msg = compute_invmixcolums_msg(int_msg);
      
      int_msg = compute_invshiftrow(int_msg);
  end

  //Final Round  
  for (int i = 0; i < 4; i++)
    int_word[3-i] = int_msg[i*32 +: 32];

  for (int i = 0; i < 4; i++)
    int_word[i] = get_invsbox(int_word[i]);

  int_msg = {int_word[0],int_word[1],int_word[2],int_word[3]};

  int_msg = compute_add_round_key(int_msg, fv_round_key_array[0]);

  return int_msg;
endfunction

//Compute AES_Decryption for 256 bit configuration
function logic [127 : 0] compute_aes_decryption_256(input logic [127 : 0] index_msg);
  logic [127:0] int_msg;
  logic [31:0] int_word[0:3];

  int_msg = index_msg;
  
  //Initial Step
  int_msg = compute_add_round_key(int_msg, fv_round_key_array[14]);

  int_msg = compute_invshiftrow(int_msg);

  //Round encryption
  for (int rnd = 13; rnd > 0; rnd--) begin

      //Round encryption
      for (int i = 0; i < 4; i++)
        int_word[3-i] = int_msg[i*32 +: 32];

      for (int i = 0; i < 4; i++)
        int_word[i] = get_invsbox(int_word[i]);

      int_msg = {int_word[0],int_word[1],int_word[2],int_word[3]};

      int_msg = compute_add_round_key(int_msg, fv_round_key_array[rnd]);

      int_msg = compute_invmixcolums_msg(int_msg);
      
      int_msg = compute_invshiftrow(int_msg);
  end

  //Final Round  
  for (int i = 0; i < 4; i++)
    int_word[3-i] = int_msg[i*32 +: 32];

  for (int i = 0; i < 4; i++)
    int_word[i] = get_invsbox(int_word[i]);

  int_msg = {int_word[0],int_word[1],int_word[2],int_word[3]};

  int_msg = compute_add_round_key(int_msg, fv_round_key_array[0]);

  return int_msg;
endfunction

////////////////////////
//   Default Clock    //
////////////////////////
default clocking default_clk @(posedge clk); endclocking

////////////////////////////////////
// Decryption Checker Properties  //
///////////////////////////////////

// Checks if the design is in IDLE state and ready is low
reset_a: assert property (reset_p);
property reset_p;
  $past(!reset_n)  
|->
  IDLE &&
  ready == 1 
;endproperty

// Checks if block produces correct 128 bit decrypted value
decryption_check_128_a: assert property (disable iff(!reset_n) decryption_check_128_p);
property decryption_check_128_p;
  logic [127:0] result, tracked_blk_msg;

  ##0 next_cmd 
  ##0 !keylen 
  ##0 (1'b1, tracked_blk_msg = block_msg)
  ##DLY_128 (1'b1, result = compute_aes_decryption_128(tracked_blk_msg)) 
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
  ##1 round == 10 && !ready[*DLY_RND]
  ##1 round == 9 && !ready[*DLY_RND]
  ##1 round == 8 && !ready[*DLY_RND]
  ##1 round == 7 && !ready[*DLY_RND]
  ##1 round == 6 && !ready[*DLY_RND]
  ##1 round == 5 && !ready[*DLY_RND]
  ##1 round == 4 && !ready[*DLY_RND]
  ##1 round == 3 && !ready[*DLY_RND]
  ##1 round == 2 && !ready[*DLY_RND]
  ##1 round == 1 && !ready[*DLY_RND]
  ##1 round == 0 && !ready
  ##1 ready
;endproperty

// Checks if block produces correct 256 bit decrypted value
decryption_check_256_a: assert property (disable iff(!reset_n) decryption_check_256_p);
property decryption_check_256_p;
  logic [127:0] result, tracked_blk_msg;

  ##0 next_cmd 
  ##0 keylen 
  ##0 (1'b1, tracked_blk_msg = block_msg)
  ##DLY_256 (1'b1, result = compute_aes_decryption_256(tracked_blk_msg)) 
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
  ##1 round == 14 && !ready[*DLY_RND]
  ##1 round == 13  && !ready[*DLY_RND]
  ##1 round == 12 && !ready[*DLY_RND]
  ##1 round == 11 && !ready[*DLY_RND]
  ##1 round == 10 && !ready[*DLY_RND]
  ##1 round == 9 && !ready[*DLY_RND]
  ##1 round == 8 && !ready[*DLY_RND]
  ##1 round == 7 && !ready[*DLY_RND]
  ##1 round == 6 && !ready[*DLY_RND]
  ##1 round == 5 && !ready[*DLY_RND]
  ##1 round == 4 && !ready[*DLY_RND]
  ##1 round == 3 && !ready[*DLY_RND]
  ##1 round == 2 && !ready[*DLY_RND]
  ##1 round == 1 && !ready[*DLY_RND]
  ##1 round == 0 && !ready
  ##1 ready
;endproperty

// Checks if block produces correct encrypted value for the first round
firstround_decrypt_a: assert property (disable iff(!reset_n) firstround_decrypt_p);
property firstround_decrypt_p;
  logic [127:0] result, tracked_blk_msg, tracked_mode;

  ##0 next_cmd 
  ##0 (1'b1, tracked_blk_msg = block_msg)
  ##0 (1'b1, tracked_mode = keylen)
  ##0 (1'b1, result = compute_firstdecrypt(tracked_blk_msg,tracked_mode))
|->
  ##1 block_new == result
;endproperty

// Checks if block produces correct round encrypted value for each round in 128 bit configuration
for (genvar rnd = 9; rnd > 0; rnd--) begin: rndcompute_128
  round_compute_128_a: assert property (disable iff(!reset_n) round_compute_128_p(rnd+1));
end
property round_compute_128_p(rndcnt);
  logic [127:0] rnd_rslt, tracked_block;
  ##0 Round_Compute && !keylen
  ##0 round == rndcnt
  ##1 (1'b1, tracked_block = old_block)
  ##0 (1'b1, rnd_rslt = compute_round_decrypt(tracked_block,rndcnt))
|->
  ##DLY_SBOX block_new == rnd_rslt
;endproperty

// Checks if block produces correct round encrypted value for each round in 256 bit configuration
for (genvar rnd = 13; rnd > 0; rnd--) begin: rndcompute_256
  round_compute_256_a: assert property (disable iff(!reset_n) round_compute_256_p(rnd+1));
end
property round_compute_256_p(rndcnt);
  logic [127:0] rnd_rslt, tracked_block;
  ##0 Round_Compute && keylen
  ##0 round == rndcnt
  ##1 (1'b1, tracked_block = old_block)
  ##0 (1'b1, rnd_rslt = compute_round_decrypt(tracked_block,rndcnt))
|->
  ##DLY_SBOX block_new == rnd_rslt
;endproperty

// Checks if block produces correct encrypted value for the first round
lastround_decrypt_a: assert property (disable iff(!reset_n) lastround_decrypt_p);
property lastround_decrypt_p;
  logic [127:0] rnd_rslt, tracked_block;
  ##0 Round_Compute
  ##0 round == 4'h1
  ##1 (1'b1, tracked_block = old_block)
  ##0 (1'b1, rnd_rslt = compute_lastround_decrypt(tracked_block))
|->
  ##DLY_SBOX block_new == rnd_rslt
;endproperty

endmodule

//Inputs driven from doe_core_cbc
`ifdef CBC_BIND

  bind doe_decipher_block fv_decrypt_checker_m 
  fv_decrypt(
    .clk(doe_core_cbc.dec_block.clk),
    .reset_n(doe_core_cbc.dec_block.reset_n && !doe_core_cbc.dec_block.zeroize),
    .next_cmd(doe_core_cbc.dec_block.next_cmd),
    .keylen(doe_core_cbc.dec_block.keylen),
    .round(doe_core_cbc.dec_block.round),
    .round_key(doe_core_cbc.dec_block.round_key),
    .block_msg(doe_core_cbc.dec_block.block_msg),
    .new_block(doe_core_cbc.dec_block.new_block),
    .ready(doe_core_cbc.dec_block.ready),
    .IDLE(doe_core_cbc.dec_block.dec_ctrl_reg == 0),
    .Round_Compute((doe_core_cbc.dec_block.dec_ctrl_reg == 2'h1) || (doe_core_cbc.dec_block.dec_ctrl_reg == 2'h3)),
    .old_block(doe_core_cbc.dec_block.round_logic.old_block),
    .block_new(doe_core_cbc.dec_block.block_new),
    .fv_round_key_array(doe_core_cbc.keymem.key_mem)
  );

//Inputs driven with constraints on doe_decipher_block
`else

  bind doe_decipher_block fv_decrypt_checker_m 
  fv_decrypt(.*,
    .clk(clk),
    .reset_n(reset_n && !zeroize),
    .IDLE(dec_ctrl_reg == 0),
    .Round_Compute((dec_ctrl_reg == 2'h1) || (dec_ctrl_reg == 2'h3)),
    .old_block(round_logic.old_block),
    .block_new(block_new),
    .fv_round_key_array(fv_dec_constraints.fv_round_key_array)
  );

`endif