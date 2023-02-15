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
// DESCRIPTION: "TOP" level sequence provides a command and response flow
//              that causes bus contention against the soc_ifc/mailbox
//              internal mapped registers.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_top_mbox_contention_sequence #(
      type CONFIG_T
      ) extends soc_ifc_env_top_mbox_sequence_base #(.CONFIG_T(CONFIG_T));


  `uvm_object_param_utils_begin( soc_ifc_env_top_mbox_contention_sequence #( CONFIG_T) )
  `uvm_object_utils_end
  `m_uvm_get_type_name_func    ( soc_ifc_env_top_mbox_contention_sequence #( CONFIG_T) )

  extern virtual function create_seqs();
  extern virtual function randomize_seqs();

endclass

function soc_ifc_env_top_mbox_contention_sequence::create_seqs();
    uvm_object obj;
    obj = soc_ifc_env_mbox_rand_medium_interference_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
    if(!$cast(soc_ifc_env_mbox_seq,obj)) `uvm_fatal("SOC_IFC_TOP_MBOX_CONTENTION", "soc_ifc_env_top_mbox_contention_sequence::create_seqs() - <seq_type>.create_object() failed")
    soc_ifc_env_cptra_handler_seq = soc_ifc_env_cptra_mbox_interference_handler_sequence_t::type_id::create("soc_ifc_env_cptra_handler_seq");
endfunction

function soc_ifc_env_top_mbox_contention_sequence::randomize_seqs();
    if(!soc_ifc_env_mbox_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_contention_sequence::body() - %s randomization failed", soc_ifc_env_mbox_seq.get_type_name()));
    if(!soc_ifc_env_cptra_handler_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_contention_sequence::body() - %s randomization failed", soc_ifc_env_cptra_handler_seq.get_type_name()));
endfunction
