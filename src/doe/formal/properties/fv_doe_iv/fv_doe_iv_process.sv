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

import doe_iv_process_pkg::*;

module fv_doe_iv_process_m(
  input bit rst,
  input bit rst_test,
  input bit clk,

  // Inputs
  input st_InPacket cmd_in,
  input st_InPacket decrypt_in,
  input st_InPacket result_in,

  // Outputs
  input bit unsigned [127:0] ivdecry_out,
  input bit unsigned [127:0] ivencry_out,
  input bit doe_ready,

  // Ready signals
  input bit cmd_in_ready,
  input bit decrypt_in_ready,
  input bit result_in_ready,

  // Registers
  input bit unsigned [127:0] dec_prev_msg,

  // States
  input bit idle,
  input bit enc,
  input bit dec_first,
  input bit dec_next
);


default clocking default_clk @(posedge clk); endclocking

// Checks if the design is in IDLE state and ready is high
reset_a: assert property (reset_p);
property reset_p;
  $past(rst) |->
  idle &&
  doe_ready == 1
;endproperty

// Checks if the block updates IV_encry with the encoded message once encryption is done
enc_to_idle_a: assert property (disable iff(rst_test) enc_to_idle_p);
property enc_to_idle_p;
  enc &&
  result_in_ready
|->
  ##1
  idle &&
  ivencry_out == $past(result_in.encoded_msg, 1);
endproperty

// Checks if the block switches from idle state to enc state upon receiving next_cmd
idle_to_enc_a: assert property (disable iff(rst) idle_to_enc_p);
property idle_to_enc_p;
  idle &&
  cmd_in_ready &&
  cmd_in.next_cmd &&
  cmd_in.encdec
|->
  ##1
  enc;
endproperty

// Checks if the block waits in enc state until encryption is done
enc_wait_a: assert property (disable iff(rst) enc_wait_p);
property enc_wait_p;
  enc &&
  !result_in_ready
|->
  ##1
  enc;
endproperty

// Checks if the block waits iv_encry updated with IV
IV_encry_check_a: assert property (disable iff(rst) IV_encry_check_p);
property IV_encry_check_p;
  doe_core_cbc.encdec &&
  cmd_in.IV_Updated_d
|->
  ##1
  ivencry_out == $past(cmd_in.IV, 1);
endproperty

// Checks if the block switches from idle state to first decrypt state upon receiving next_cmd 
// and updates IV_decry with the IV, IV_decry_next with incoming block message
idle_to_dec_first_a: assert property (disable iff(rst) idle_to_dec_first_p);
property idle_to_dec_first_p;
  doe_core_cbc.IV_dec_state == 0 &&
  doe_core_cbc.next_cmd && doe_core_cbc.dec_ready &&
  !doe_core_cbc.encdec
|->
  ##1
  dec_first &&
  ivdecry_out  == $past(doe_core_cbc.IV) &&
  dec_prev_msg == $past(doe_core_cbc.block_msg);
endproperty

// Checks if the block switches from first decrypt state to next decrypt state upon receiving next_cmd 
// and updates IV_decry with the previous IV_decry_next, IV_decry_next with incoming block message
dec_first_to_dec_next_a: assert property (disable iff(rst) dec_first_to_dec_next_p);
property dec_first_to_dec_next_p;
  dec_first &&
  decrypt_in_ready
|->
  ##1
  dec_next &&
  ivdecry_out  == $past(doe_core_cbc.IV_decry_next) &&
  dec_prev_msg == $past(doe_core_cbc.block_msg)
;endproperty

// Checks if the block switches from next decrypt state to first decrypt state in next cycle
// and holds values of IV_decry, IV_decry_next from previous state
dec_next_to_dec_first_a: assert property (disable iff(rst) dec_next_to_dec_first_p);
property dec_next_to_dec_first_p;
  dec_next
|->
  ##1
  dec_first &&
  ivdecry_out  == $past(ivdecry_out) &&
  dec_prev_msg == $past(dec_prev_msg)
;endproperty

// Checks if the block switches from first decrypt state to idle state upon receiving IV_updated
// and updates IV_decry, IV_decry_next with incoming IV
dec_first_to_idle_a: assert property (disable iff(rst) dec_first_to_idle_p);
property dec_first_to_idle_p;
  dec_first &&
  decrypt_in.dec_ready &&
  !decrypt_in.next_cmd &&
  decrypt_in.IV_Updated_d
|->
  ##1
  idle &&
  ivdecry_out == $past(doe_core_cbc.IV, 1) &&
  dec_prev_msg == $past(doe_core_cbc.IV, 1)
;endproperty

// Checks if the block waits in idle state until encryption/decryption is triggered
idle_wait_a: assert property (disable iff(rst) idle_wait_p);
property idle_wait_p;
  idle &&
  !cmd_in_ready
|->
  ##1
  idle;
endproperty

// Checks if the block waits in first decrypt state until new decryption starts or IV_updated is received
dec_first_wait_a: assert property (disable iff(rst) dec_first_wait_p);
property dec_first_wait_p;
  dec_first &&
  !decrypt_in_ready &&
  !decrypt_in.IV_Updated_d
|->
  ##1
  dec_first 
;endproperty


endmodule


module fv_doe_iv_process_ref_wrapper_m;


default clocking default_clk @(posedge (doe_core_cbc.clk)); endclocking


st_InPacket cmd_in = '{ encoded_msg: (doe_core_cbc.enc_new_block), block_msg: (doe_core_cbc.block_msg), IV: (doe_core_cbc.IV), encdec: (doe_core_cbc.encdec), enc_ready: (doe_core_cbc.enc_ready), dec_ready: (doe_core_cbc.dec_ready), IV_Updated_d: (doe_core_cbc.IV_updated_delayed), next_cmd: (doe_core_cbc.next_cmd), keylen: (doe_core_cbc.keylen) };
st_InPacket decrypt_in = '{ encoded_msg: (doe_core_cbc.enc_new_block), block_msg: (doe_core_cbc.block_msg), IV: (doe_core_cbc.IV), encdec: (doe_core_cbc.encdec), enc_ready: (doe_core_cbc.enc_ready), dec_ready: (doe_core_cbc.dec_ready), IV_Updated_d: (doe_core_cbc.IV_updated_delayed), next_cmd: (doe_core_cbc.next_cmd), keylen: (doe_core_cbc.keylen) };
st_InPacket result_in = '{ encoded_msg: (doe_core_cbc.enc_new_block), block_msg: (doe_core_cbc.block_msg), IV: (doe_core_cbc.IV), encdec: (doe_core_cbc.encdec), enc_ready: (doe_core_cbc.enc_ready), dec_ready: (doe_core_cbc.dec_ready), IV_Updated_d: (doe_core_cbc.IV_updated_delayed), next_cmd: (doe_core_cbc.next_cmd), keylen: (doe_core_cbc.keylen) };


fv_doe_iv_process_m fv_doe_iv_process(
  .rst(!(doe_core_cbc.reset_n && !doe_core_cbc.zeroize)),
  .rst_test(!(doe_core_cbc.reset_n && !doe_core_cbc.zeroize) || $past(!(doe_core_cbc.reset_n && !doe_core_cbc.zeroize))),
  .clk(doe_core_cbc.clk),

  // Inputs
  .cmd_in(cmd_in),
  .decrypt_in(decrypt_in),
  .result_in(result_in),

  // Outputs
  .ivdecry_out(doe_core_cbc.IV_decry),
  .ivencry_out(doe_core_cbc.IV_encry),
  .doe_ready(doe_core_cbc.ready),

  // Ready signals
  .cmd_in_ready((doe_core_cbc.enc_ready && doe_core_cbc.enc_next) || (doe_core_cbc.dec_ready && doe_core_cbc.dec_next)),
  .decrypt_in_ready(doe_core_cbc.dec_next && doe_core_cbc.dec_ready),
  .result_in_ready((!$past(doe_core_cbc.enc_ready) && doe_core_cbc.enc_ready) ),

  // Registers
  .dec_prev_msg(doe_core_cbc.IV_decry_next),

  // States
  .idle(doe_core_cbc.IV_enc_state == 0 || doe_core_cbc.IV_dec_state == 0),
  .enc(doe_core_cbc.IV_enc_state == 1),
  .dec_first(doe_core_cbc.IV_dec_state == 2),
  .dec_next(doe_core_cbc.IV_dec_state == 1)
);


endmodule


bind doe_core_cbc fv_doe_iv_process_ref_wrapper_m fv_doe_iv_process_ref_wrapper();
