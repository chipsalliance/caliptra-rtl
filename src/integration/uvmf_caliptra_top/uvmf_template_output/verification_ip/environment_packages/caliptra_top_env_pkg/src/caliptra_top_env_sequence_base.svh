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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: This file contains environment level sequences that will
//    be reused from block to top level simulations.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class caliptra_top_env_sequence_base #( 
      type CONFIG_T
      ) extends uvmf_virtual_sequence_base #(.CONFIG_T(CONFIG_T));


  `uvm_object_param_utils( caliptra_top_env_sequence_base #(
                           CONFIG_T
                           ) );

  
// This caliptra_top_env_sequence_base contains a handle to a caliptra_top_env_configuration object 
// named configuration.  This configuration variable contains a handle to each 
// sequencer within each agent within this environment and any sub-environments.
// The configuration object handle is automatically assigned in the pre_body in the
// base class of this sequence.  The configuration handle is retrieved from the
// virtual sequencer that this sequence is started on.
// Available sequencer handles within the environment configuration:

  // Initiator agent sequencers in caliptra_top_environment:

  // Responder agent sequencers in caliptra_top_environment:

  // Virtual sequencers in sub-environments located in sub-environment configuration
    // configuration.soc_ifc_subenv_config.vsqr


typedef soc_ifc_env_sequence_base #(
        .CONFIG_T(soc_ifc_env_configuration)
        ) 
        soc_ifc_subenv_sequence_base_t;
rand soc_ifc_subenv_sequence_base_t soc_ifc_subenv_seq;



  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  function new(string name = "" );
    super.new(name);

    soc_ifc_subenv_seq = soc_ifc_subenv_sequence_base_t::type_id::create("soc_ifc_subenv_seq");

  endfunction

  virtual task body();


    soc_ifc_subenv_seq.start(configuration.soc_ifc_subenv_config.vsqr);

  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

