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
// DESCRIPTION: Sequence to initiate (and respond) to mailbox command
//              "TOP" sequence because it invokes lower level env sequences
//              to facilitate the uC/SoC sides of mailbox command handling
//              and this sequence defines the whole mailbox flow.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_top_mbox_rand_pauser_medium_unlock_sequence extends soc_ifc_env_top_mbox_rand_pauser_sequence;


  `uvm_object_utils( soc_ifc_env_top_mbox_rand_pauser_medium_unlock_sequence )

  extern virtual function create_seqs();
  extern virtual function randomize_seqs();

endclass

function soc_ifc_env_top_mbox_rand_pauser_medium_unlock_sequence::create_seqs();
    uvm_object obj;
    obj = soc_ifc_env_mbox_rand_pauser_medium_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
    if(!$cast(soc_ifc_env_mbox_seq,obj)) `uvm_fatal("SOC_IFC_TOP_MBOX_RAND_PAUSER", "soc_ifc_env_top_mbox_rand_pauser_medium_unlock_sequence::create_seqs() - <seq_type>.create_object() failed")
    soc_ifc_env_cptra_handler_seq = soc_ifc_env_cptra_mbox_handler_sequence_t::type_id::create("soc_ifc_env_cptra_handler_seq");
    soc_ifc_env_pauser_init_seq = soc_ifc_env_pauser_init_sequence_t::type_id::create("soc_ifc_env_pauser_init_seq");
endfunction

function soc_ifc_env_top_mbox_rand_pauser_medium_unlock_sequence::randomize_seqs();
    if(!soc_ifc_env_mbox_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_rand_pauser_medium_unlock_sequence::body() - %s randomization failed", soc_ifc_env_mbox_seq.get_type_name()));
    if(!soc_ifc_env_cptra_handler_seq.randomize() with { inject_force_unlock == 1'b1; })
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_rand_pauser_medium_unlock_sequence::body() - %s randomization failed", soc_ifc_env_cptra_handler_seq.get_type_name()));
    if(!soc_ifc_env_pauser_init_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_rand_pauser_medium_unlock_sequence::body() - %s randomization failed", soc_ifc_env_pauser_init_seq.get_type_name()));
endfunction
