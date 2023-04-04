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
class soc_ifc_env_sequence_base #( 
      type CONFIG_T
      ) extends uvmf_virtual_sequence_base #(.CONFIG_T(CONFIG_T));


  `uvm_object_param_utils( soc_ifc_env_sequence_base #(
                           CONFIG_T
                           ) );
  `m_uvm_get_type_name_func(soc_ifc_env_sequence_base)

  // Handle to the environments register model
// This handle needs to be set before use.
  soc_ifc_reg_model_top  reg_model;

// This soc_ifc_env_sequence_base contains a handle to a soc_ifc_env_configuration object 
// named configuration.  This configuration variable contains a handle to each 
// sequencer within each agent within this environment and any sub-environments.
// The configuration object handle is automatically assigned in the pre_body in the
// base class of this sequence.  The configuration handle is retrieved from the
// virtual sequencer that this sequence is started on.
// Available sequencer handles within the environment configuration:

  // Initiator agent sequencers in soc_ifc_environment:
    // configuration.soc_ifc_ctrl_agent_config.sequencer
    // configuration.cptra_ctrl_agent_config.sequencer

  // Responder agent sequencers in soc_ifc_environment:
    // configuration.soc_ifc_status_agent_config.sequencer
    // configuration.cptra_status_agent_config.sequencer


    typedef soc_ifc_ctrl_random_sequence soc_ifc_ctrl_agent_random_sequence_t;
    soc_ifc_ctrl_agent_random_sequence_t soc_ifc_ctrl_agent_rand_seq;

    typedef cptra_ctrl_random_sequence cptra_ctrl_agent_random_sequence_t;
    cptra_ctrl_agent_random_sequence_t cptra_ctrl_agent_rand_seq;






  // pragma uvmf custom class_item_additional begin
    soc_ifc_status_agent_responder_seq_t soc_ifc_status_agent_rsp_seq;
    cptra_status_agent_responder_seq_t cptra_status_agent_rsp_seq;

  virtual task pre_start();
    `uvm_info(this.get_type_name(), "In: pre_start() for sequence", UVM_NONE)
  endtask

  // pragma uvmf custom class_item_additional end
  
  function new(string name = "" );
    super.new(name);
    soc_ifc_ctrl_agent_rand_seq = soc_ifc_ctrl_agent_random_sequence_t::type_id::create("soc_ifc_ctrl_agent_rand_seq");
    cptra_ctrl_agent_rand_seq = cptra_ctrl_agent_random_sequence_t::type_id::create("cptra_ctrl_agent_rand_seq");


  endfunction

  virtual task body();

    if ( configuration.soc_ifc_ctrl_agent_config.sequencer != null )
       repeat (25) soc_ifc_ctrl_agent_rand_seq.start(configuration.soc_ifc_ctrl_agent_config.sequencer);
    if ( configuration.cptra_ctrl_agent_config.sequencer != null )
       repeat (25) cptra_ctrl_agent_rand_seq.start(configuration.cptra_ctrl_agent_config.sequencer);


  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

