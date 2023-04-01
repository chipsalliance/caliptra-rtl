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
// DESCRIPTION: Extended from mbox pauser sequence to exercise PAUSER filtering.
//              Tests small sized mailbox commands with PAUSER randomization.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_rand_pauser_small_sequence extends soc_ifc_env_mbox_rand_pauser_sequence;

  `uvm_object_utils( soc_ifc_env_mbox_rand_pauser_small_sequence )

  // Constrain dlen to be a small command
  // Max. size: 512B
  constraint mbox_dlen_max_small_c { mbox_op_rand.dlen <= 32'h0000_0200; }
  // Constrain response data size to also be small
  // Max. size: 128B
  constraint mbox_resp_dlen_max_small_c { mbox_resp_expected_dlen < 32'h0000_0080; }

endclass
