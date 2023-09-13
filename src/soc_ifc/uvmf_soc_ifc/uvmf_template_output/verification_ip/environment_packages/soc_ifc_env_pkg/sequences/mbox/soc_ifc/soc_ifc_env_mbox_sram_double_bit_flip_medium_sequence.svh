//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
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

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: Extended from Mailbox SRAM double bit flip injection
//              sequence for the special 'medium' test case
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_sram_double_bit_flip_medium_sequence extends soc_ifc_env_mbox_sram_double_bit_flip_sequence;

  `uvm_object_utils( soc_ifc_env_mbox_sram_double_bit_flip_medium_sequence )

  // Constrain dlen to be a medium command
  // Max. size: 4096B
  constraint mbox_dlen_max_medium_c { mbox_op_rand.dlen <= 32'h0000_1000; }
  // Minimum 512B
  constraint mbox_dlen_min_medium_c { mbox_op_rand.dlen >= 32'h0000_0200; }
  // Constrain response data size to also be medium
  // Max. size: 4096B
  // Min. size: 512B
  constraint mbox_resp_dlen_max_medium_c { mbox_resp_expected_dlen <= 32'h0000_1000; }
  constraint mbox_resp_dlen_min_medium_c { mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_resp_expected_dlen >= 32'h0000_0200; }
  // Valid solution for the custom delay ruleset, to control random delays while
  // waiting to inject random error accesses
  constraint custom_delay_c { rand_delay > 0;
                              rand_delay dist {[1                   :mbox_op_rand.dlen*2 -1] :/ 250,
                                               [mbox_op_rand.dlen*2 :mbox_op_rand.dlen*5 -1] :/ 100,
                                               [mbox_op_rand.dlen*5 :mbox_op_rand.dlen*15-1] :/ 25}; }

endclass
