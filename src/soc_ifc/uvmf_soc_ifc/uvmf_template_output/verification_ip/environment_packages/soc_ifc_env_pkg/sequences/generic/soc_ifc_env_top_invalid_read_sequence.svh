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
class soc_ifc_env_top_invalid_read_sequence extends soc_ifc_env_top_generic_sequence_base; //soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t)); //uvmf_sequence_base #(uvm_sequence_item);


  `uvm_object_utils( soc_ifc_env_top_invalid_read_sequence )

  extern virtual function create_seqs();

  
endclass

function soc_ifc_env_top_invalid_read_sequence::create_seqs();
  uvm_object obj;
  
  obj = soc_ifc_env_gen_rand_rw_sequence_t::get_type().create_object("soc_ifc_env_gen_rand_rw_seq");
  `uvm_info("KNU_CREATE", "In create seq", UVM_MEDIUM)
  
  if (obj == null)
    `uvm_info("KNU_CREATE", "obj is null", UVM_MEDIUM)
  
  if (!$cast(soc_ifc_env_gen_rand_rw_seq, obj)) `uvm_fatal("KNU_INVALID", "create seq failed")
    
endfunction


