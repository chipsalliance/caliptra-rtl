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
// DESCRIPTION: Extended from mbox_base sequence to provide additional
//              functionality in a test that sends large commands.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_reg_axs_invalid_large_sequence extends soc_ifc_env_mbox_reg_axs_invalid_sequence;

  `uvm_object_utils( soc_ifc_env_mbox_reg_axs_invalid_large_sequence )

  // Constrain size to a large command
  // Min. size: 16KiB
  constraint mbox_dlen_min_large_c { mbox_op_rand.dlen > 32'h0000_4000; }
  // Constrain response data size to also be large
  // Min. size: 16KiB
  constraint mbox_resp_dlen_min_large_c { mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_resp_expected_dlen >= 32'h0000_4000; }
  // Valid solution for the custom delay ruleset, to control random delays while
  // waiting to inject random error accesses
  constraint custom_delay_c { rand_delay > 0; rand_delay < (mbox_op_rand.dlen * 5); }

endclass
