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
class pv_env_sequence_base #( 
      type CONFIG_T
      ) extends uvmf_virtual_sequence_base #(.CONFIG_T(CONFIG_T));


  `uvm_object_param_utils( pv_env_sequence_base #(
                           CONFIG_T
                           ) );

  // Handle to the environments register model
// This handle needs to be set before use.
  pv_reg_model_top  reg_model;

// This pv_env_sequence_base contains a handle to a pv_env_configuration object 
// named configuration.  This configuration variable contains a handle to each 
// sequencer within each agent within this environment and any sub-environments.
// The configuration object handle is automatically assigned in the pre_body in the
// base class of this sequence.  The configuration handle is retrieved from the
// virtual sequencer that this sequence is started on.
// Available sequencer handles within the environment configuration:

  // Initiator agent sequencers in pv_environment:
    // configuration.pv_rst_agent_config.sequencer
    // configuration.pv_sha512_write_agent_config.sequencer
    // configuration.pv_sha512_block_read_agent_config.sequencer

  // Responder agent sequencers in pv_environment:


    typedef pv_rst_random_sequence pv_rst_agent_random_sequence_t;
    pv_rst_agent_random_sequence_t pv_rst_agent_rand_seq;

    typedef pv_write_random_sequence pv_sha512_write_agent_random_sequence_t;
    pv_sha512_write_agent_random_sequence_t pv_sha512_write_agent_rand_seq;

    typedef pv_read_random_sequence pv_sha512_block_read_agent_random_sequence_t;
    pv_sha512_block_read_agent_random_sequence_t pv_sha512_block_read_agent_rand_seq;




  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  function new(string name = "" );
    super.new(name);
    pv_rst_agent_rand_seq = pv_rst_agent_random_sequence_t::type_id::create("pv_rst_agent_rand_seq");
    pv_sha512_write_agent_rand_seq = pv_sha512_write_agent_random_sequence_t::type_id::create("pv_sha512_write_agent_rand_seq");
    pv_sha512_block_read_agent_rand_seq = pv_sha512_block_read_agent_random_sequence_t::type_id::create("pv_sha512_block_read_agent_rand_seq");


  endfunction

  virtual task body();

    if ( configuration.pv_rst_agent_config.sequencer != null )
       repeat (25) pv_rst_agent_rand_seq.start(configuration.pv_rst_agent_config.sequencer);
    if ( configuration.pv_sha512_write_agent_config.sequencer != null )
       repeat (25) pv_sha512_write_agent_rand_seq.start(configuration.pv_sha512_write_agent_config.sequencer);
    if ( configuration.pv_sha512_block_read_agent_config.sequencer != null )
       repeat (25) pv_sha512_block_read_agent_rand_seq.start(configuration.pv_sha512_block_read_agent_config.sequencer);


  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

