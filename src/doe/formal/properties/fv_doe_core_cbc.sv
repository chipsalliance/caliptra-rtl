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

module fv_doe_cbc_checker_m(
  
  ////////////////////////////
  // Input / Output signals //
  ////////////////////////////
  // Clock and reset.
  input             clk,
  input             reset_n,
  input             zeroize,

  input             encdec,
  input             init_cmd,
  input             next_cmd,
  input             enc_ready,
  input             dec_ready,
  input             key_ready,
  input [127:0]     enc_new_block,
  input [127:0]     dec_new_block,
  input [127:0]     IV_decry,
  input             ready,
  input [127:0]     result,
  input             result_valid,
  input [31 : 0]    muxed_sboxw,
  input [31 : 0]    new_sboxw
);

////////////////////////
//   Default Clock    //
////////////////////////
default clocking default_clk @(posedge clk); endclocking

//Internal Signals
logic [31:0] fv_sbox;

//Helper Logic
assign fv_sbox = get_sbox(muxed_sboxw);

////////////////////////////////////
//      Core CBC Properties      //
///////////////////////////////////

//Checks if doe_sbox block produces correct values
sbox_check_a: assert property  (disable iff(!reset_n) sbox_check_p);
property sbox_check_p;
   !ready
|->
   new_sboxw == fv_sbox
;endproperty

//Checks if block asserts result_valid upon finishing encryption
result_valid_enc_a: assert property (disable iff(!reset_n) result_valid_enc_p);
property result_valid_enc_p;
   encdec &&
   next_cmd 
   ##1 enc_ready[->1]
|=>
   result_valid
;endproperty

//Checks if block asserts result_valid upon finishing decryption
result_valid_dec_a: assert property (disable iff(!reset_n) result_valid_dec_p);
property result_valid_dec_p;
   !encdec &&
   next_cmd 
   ##1 dec_ready[->1]
|=>
   result_valid
;endproperty

//Checks if block asserts ready upon finishing key expansion
ready_kemem_a: assert property (disable iff(!reset_n) ready_kemem_p);
property ready_kemem_p;
   init_cmd 
   ##1 key_ready[->1]
   |=>
   ready
;endproperty

//Checks if block asserts ready upon finishing encryption
ready_enc_a: assert property (disable iff(!reset_n) ready_enc_p);
property ready_enc_p;
   encdec &&
   next_cmd 
   ##1 enc_ready[->1]
|=>
   ready
;endproperty

//Checks if block asserts ready upon finishing decryption
ready_dec_a: assert property (disable iff(!reset_n) ready_dec_p);
property ready_dec_p;
   !encdec &&
   next_cmd 
   ##1 dec_ready[->1]
|=>
   ready
;endproperty

//Checks if block produces result upon finishing encryption
result_enc_a: assert property (disable iff(!reset_n) result_enc_p);
property result_enc_p;
   encdec &&
   next_cmd 
   ##1 enc_ready[->1]
|->
   result == enc_new_block
;endproperty

//Checks if block produces result upon finishing decryption
result_dec_a: assert property (disable iff(!reset_n) result_dec_p);
property result_dec_p;
   !encdec &&
   next_cmd 
   ##1 dec_ready[->1]
|->
   result == dec_new_block
;endproperty

endmodule

//Connect this checker module with the DUV
bind doe_core_cbc fv_doe_cbc_checker_m fv_doe_cbc_inst(
   .clk(clk),
   .reset_n(reset_n && !zeroize),
   .encdec(encdec),
   .init_cmd(init_cmd),
   .next_cmd(next_cmd),
   .enc_ready(enc_ready),
   .dec_ready(dec_ready),
   .key_ready(key_ready),
   .IV_decry(IV_decry),
   .enc_new_block(enc_new_block),
   .dec_new_block(dec_new_block ^ IV_decry),
   .ready(ready),
   .result(result),
   .result_valid(result_valid),
   .muxed_sboxw(muxed_sboxw),
   .new_sboxw(new_sboxw)
);

