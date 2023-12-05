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
import global_package::*;

module fv_hmac_core_m(
  input bit rst,
  input bit clk,
  input bit unsigned [511:0] H1_digest,
  input bit unsigned [511:0] H1_setup_digest,
  input bit unsigned [511:0] H2_digest,
  input bit unsigned [383:0] hmac_msg_key,
  input bit unsigned [1023:0] hmac_msg_block_msg,
  input bit hmac_msg_init,
  input bit hmac_msg_next,
  input bit unsigned [1023:0] sha1_block_msg,
  input bit sha1_init,
  input bit sha1_next,
  input bit unsigned [1023:0] sha2_block_msg,
  input bit sha2_init,
  input bit sha2_next,
  input bit unsigned [383:0] tag,
  input bit H1_digest_ready,
  input bit H1_setup_digest_ready,
  input bit H2_digest_ready,
  input bit hmac_msg_valid,
  input bit H1_digest_valid,
  input bit H1_setup_digest_valid,
  input bit H2_digest_valid,
  input bit hmac_msg_ready,
  input bit tag_valid,
  input bit unsigned [383:0] hmac_key,
  input bit unsigned [1023:0] hmac_block_msg,
  input bit unsigned [511:0] sha_digest_out_opad,
  input bit idle,
  input bit ctrl_ipad,
  input bit ctrl_opad,
  input bit ctrl_hmac,
  input bit done_tag
);


default clocking default_clk @(posedge clk); endclocking

sequence reset_sequence;
  rst ##1 !rst;
endsequence

reset_a: assert property (reset_p);
property reset_p;
  reset_sequence |->
  idle &&
  hmac_msg_ready == 1 &&
  tag_valid == 0;
endproperty


ctrl_hmac_to_done_tag_a: assert property (disable iff(rst) ctrl_hmac_to_done_tag_p);
property ctrl_hmac_to_done_tag_p;
  ctrl_hmac &&
  H2_digest_ready
|->
  ##1 (hmac_msg_ready == 0) and
  ##1 (tag_valid == 0) and
  ##1 done_tag;
endproperty


done_tag_to_idle_a: assert property (disable iff(rst) done_tag_to_idle_p);
property done_tag_to_idle_p;
  done_tag
|->
  ##1
  idle &&
  tag == 384'(((sha_digest_out_opad) >> 512'd128)) &&
  hmac_msg_ready == 1 &&
  tag_valid == 1;
endproperty


idle_to_ctrl_ipad_a: assert property (disable iff(rst) idle_to_ctrl_ipad_p);
property idle_to_ctrl_ipad_p;
  idle &&
  hmac_msg_valid &&
  hmac_msg_init
|->
  ##1 (hmac_msg_ready == 0) and
  ##1 (tag_valid == 0) and
  ##1
  ctrl_ipad &&
  sha1_block_msg == key_ipadded($past(hmac_msg_key, 1)) &&
  sha1_init == 1 &&
  sha1_next == 0 &&
  sha2_block_msg == key_opadded($past(hmac_msg_key, 1)) &&
  sha2_init == 0 &&
  sha2_next == 0;
endproperty


idle_to_ctrl_opad_a: assert property (disable iff(rst) idle_to_ctrl_opad_p);
property idle_to_ctrl_opad_p;
  idle &&
  hmac_msg_valid &&
  !hmac_msg_init
|->
  ##1 (hmac_msg_ready == 0) and
  ##1 (tag_valid == 0) and
  ##1
  ctrl_opad &&
  sha1_block_msg == (hmac_block_msg) &&
  sha1_init == 0 &&
  sha1_next == 1 &&
  sha2_block_msg == key_opadded($past(hmac_msg_key, 1)) &&
  sha2_init == 1 &&
  sha2_next == 0;
endproperty


ctrl_ipad_to_ctrl_opad_a: assert property (disable iff(rst) ctrl_ipad_to_ctrl_opad_p);
property ctrl_ipad_to_ctrl_opad_p;
  ctrl_ipad &&
  H1_setup_digest_ready
|->
  ##1 (hmac_msg_ready == 0) and
  ##1 (tag_valid == 0) and
  ##1
  ctrl_opad &&
  sha1_block_msg == (hmac_block_msg) &&
  sha1_init == 0 &&
  sha1_next == 1 &&
  sha2_block_msg == key_opadded($past(hmac_key, 1)) &&
  sha2_init == 1 &&
  sha2_next == 0;
endproperty


ctrl_opad_to_ctrl_hmac_a: assert property (disable iff(rst) ctrl_opad_to_ctrl_hmac_p);
property ctrl_opad_to_ctrl_hmac_p;
  ctrl_opad &&
  H1_digest_ready
|->
  ##1 (hmac_msg_ready == 0) and
  ##1 (tag_valid == 0) and
  ##1
  ctrl_hmac &&
  sha1_block_msg == key_ipadded($past(hmac_key, 1)) &&
  sha1_init == 0 &&
  sha1_next == 0 &&
  sha2_block_msg == hmac_padded(384'(((H1_digest) >> 512'd128))) &&
  sha2_init == 0 &&
  sha2_next == 1;
endproperty


ctrl_hmac_wait_a: assert property (disable iff(rst) ctrl_hmac_wait_p);
property ctrl_hmac_wait_p;
  ctrl_hmac &&
  !H2_digest_ready
|->
  ##1
  ctrl_hmac &&
  hmac_msg_ready == 0 &&
  tag_valid == 0;
endproperty


idle_wait_a: assert property (disable iff(rst) idle_wait_p);
property idle_wait_p;
  idle &&
  !hmac_msg_valid
|->
  ##1
  idle &&
  hmac_msg_ready == 1 &&
  tag_valid == $past(tag_valid);
endproperty


ctrl_ipad_wait_a: assert property (disable iff(rst) ctrl_ipad_wait_p);
property ctrl_ipad_wait_p;
  ctrl_ipad &&
  !H1_setup_digest_ready
|->
  ##1
  ctrl_ipad &&
  hmac_msg_ready == 0 &&
  tag_valid == 0;
endproperty


ctrl_opad_wait_a: assert property (disable iff(rst) ctrl_opad_wait_p);
property ctrl_opad_wait_p;
  ctrl_opad &&
  !H1_digest_ready
|->
  ##1
  ctrl_opad &&
  hmac_msg_ready == 0 &&
  tag_valid == 0;
endproperty

endmodule

bind hmac_core fv_hmac_core_m fv_hmac_core(
  .rst((!hmac_core.reset_n || hmac_core.zeroize)),
  .clk(hmac_core.clk),
  .H1_digest({hmac_core.H1_digest,hmac_core.garbage_bit_vector1}),
  .H1_setup_digest({hmac_core.H1_digest,hmac_core.garbage_bit_vector1}),
  .H2_digest({hmac_core.H2_digest,hmac_core.garbage_bit_vector2}),
  .hmac_msg_key(hmac_core.key),
  .hmac_msg_block_msg(hmac_core.block_msg),
  .hmac_msg_init(hmac_core.init_cmd),
  .hmac_msg_next(hmac_core.next_cmd),
  .sha1_block_msg(hmac_core.H1_block),
  .sha1_init(hmac_core.H1_init),
  .sha1_next(hmac_core.H1_next),
  .sha2_block_msg(hmac_core.H2_block),
  .sha2_init(hmac_core.H2_init),
  .sha2_next(hmac_core.H2_next),
  .tag(hmac_core.tag),
  .H1_digest_ready((hmac_core.H1_ready && hmac_core.H2_ready) && !hmac_core.first_round),
  .H1_setup_digest_ready(hmac_core.H1_ready && !hmac_core.first_round),
  .H2_digest_ready(hmac_core.H2_ready && !hmac_core.first_round),
  .hmac_msg_valid(hmac_core.init_cmd || hmac_core.next_cmd),
  .H1_digest_valid(hmac_core.H1_digest_valid && hmac_core.H2_digest_valid),
  .H1_setup_digest_valid(hmac_core.H1_digest_valid),
  .H2_digest_valid(hmac_core.H2_digest_valid),
  .hmac_msg_ready(hmac_core.ready),
  .tag_valid(hmac_core.tag_valid),
  .hmac_key((hmac_core.key)),
  .hmac_block_msg((hmac_core.block_msg)),
  .sha_digest_out_opad({hmac_core.H2_digest,hmac_core.garbage_bit_vector2}),
  .idle(hmac_core.hmac_ctrl_reg==3'h0),
  .ctrl_ipad(hmac_core.hmac_ctrl_reg==3'h1),
  .ctrl_opad(hmac_core.hmac_ctrl_reg==3'h2),
  .ctrl_hmac(hmac_core.hmac_ctrl_reg==3'h3),
  .done_tag(hmac_core.hmac_ctrl_reg==3'h4)
);
