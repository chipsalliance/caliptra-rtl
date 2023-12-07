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

module fv_enc_constraints_m(
  
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
   input            ready         

);

////////////////////////
//   Default Clock    //
////////////////////////
default clocking default_clk @(posedge clk); endclocking

//Internal Signals
logic [31:0] fv_sbox;
logic [127:0] fv_round_key;
logic [127:0] fv_round_key_array[14:0];

////////////////////////
//   Symbolic Logic   //
///////////////////////

sym_roundkey_a: assume property (disable iff(!reset_n) sym_roundkey_p);
property sym_roundkey_p;
  ##1 $stable(fv_round_key_array)
;endproperty

//Get expanded round keys for input key
function logic[127:0] get_roundkey(input logic [3:0] index_round);
  logic [127:0] int_key;

     int_key = fv_round_key_array[index_round];
  
  return int_key;
endfunction

//Helper Logic
assign fv_sbox = get_sbox(sboxw);
assign fv_round_key = get_roundkey(round);

////////////////////////////////////////
//  Encryption Constraint Properties //
//////////////////////////////////////

//Constraint to drive correct value to new_sboxw input
sbox_constraint_a: assume property (disable iff(!reset_n) sbox_constraint_p);
property sbox_constraint_p;
   new_sboxw == fv_sbox
;endproperty

//Constraint to drive correct value to round_key input
roundkey_constraint_a: assume property (disable iff(!reset_n) roundkey_constraint_p);
property roundkey_constraint_p;
  round_key == fv_round_key
;endproperty

//Constraint to keep keylen input stable
stable_keylen_a: assume property (disable iff(!reset_n) stable_keylen_p);
property stable_keylen_p;
   $stable(keylen) || ready
;endproperty

//Constraint to keep incoming roundkey stable
stable_blk_msg_a: assume property (disable iff(!reset_n) stable_blk_msg_p);
property stable_blk_msg_p;
    $stable(block_msg) || ready
;endproperty

//next_cmd can be only received if the doe_encipher_block is ready
cmd_on_ready_a: assume property (disable iff(!reset_n) cmd_on_ready_p);
property cmd_on_ready_p;
    !ready
|->
    !next_cmd;
endproperty

`ifdef CBC_BIND
  //Constraint to drive correct value to fv_round_key_array signal in fv_encrypt checker
  roundkey_array_cbc_a: assume property (disable iff(!reset_n) roundkey_array_cbc_p);
  property roundkey_array_cbc_p;
    doe_core_cbc.enc_block.fv_encrypt.fv_round_key_array == fv_round_key_array
  ;endproperty
`endif

endmodule

//Connect this constraints module with the DUV
bind doe_encipher_block fv_enc_constraints_m fv_enc_constraints(.*,
  .clk(clk),
  .reset_n(reset_n && !zeroize)
	);

