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
// DESCRIPTION: Mailbox/Reset sequence provides a command flow
//              that executes a mailbox command and injects a reset randomly
//              during the operation.
//              This is facilitated by running the mailbox flow
//              and reset in a fork.
//              This sequence runs a medium sized mailbox command and cold
//              reset.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_rst_cold_rand_medium_sequence extends soc_ifc_env_mbox_rst_sequence;


  `uvm_object_utils( soc_ifc_env_mbox_rst_cold_rand_medium_sequence )

  extern virtual function      create_seqs();

endclass

function soc_ifc_env_mbox_rst_cold_rand_medium_sequence::create_seqs();
    uvm_object obj;
    obj = soc_ifc_env_mbox_rand_medium_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
    if(!$cast(soc_ifc_env_mbox_seq,obj)) `uvm_fatal("SOC_IFC_MBOX_RST", "soc_ifc_env_mbox_rst_cold_rand_medium_sequence::create_seqs() - <seq_type>.create_object() failed")
    obj = soc_ifc_env_reset_cold_sequence_t::get_type().create_object("soc_ifc_env_rst_seq");
    if(!$cast(soc_ifc_env_rst_seq,obj)) `uvm_fatal("SOC_IFC_MBOX_RST", "soc_ifc_env_mbox_rst_cold_rand_medium_sequence::create_seqs() - <seq_type>.create_object() failed")
endfunction
