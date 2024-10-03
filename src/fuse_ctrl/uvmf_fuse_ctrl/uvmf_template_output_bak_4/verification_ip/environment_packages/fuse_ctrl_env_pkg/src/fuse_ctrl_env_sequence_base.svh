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
class fuse_ctrl_env_sequence_base #( 
      type CONFIG_T
      ) extends uvmf_virtual_sequence_base #(.CONFIG_T(CONFIG_T));


  `uvm_object_param_utils( fuse_ctrl_env_sequence_base #(
                           CONFIG_T
                           ) );

  
// This fuse_ctrl_env_sequence_base contains a handle to a fuse_ctrl_env_configuration object 
// named configuration.  This configuration variable contains a handle to each 
// sequencer within each agent within this environment and any sub-environments.
// The configuration object handle is automatically assigned in the pre_body in the
// base class of this sequence.  The configuration handle is retrieved from the
// virtual sequencer that this sequence is started on.
// Available sequencer handles within the environment configuration:

  // Initiator agent sequencers in fuse_ctrl_environment:
    // configuration.fuse_ctrl_rst_in_agent_config.sequencer
    // configuration.fuse_ctrl_core_axi_write_in_if_agent_config.sequencer
    // configuration.fuse_ctrl_prim_axi_write_in_if_agent_config.sequencer
    // configuration.fuse_ctrl_core_axi_read_in_if_agent_config.sequencer
    // configuration.fuse_ctrl_prim_axi_read_in_if_agent_config.sequencer
    // configuration.fuse_ctrl_secreg_axi_read_in_if_agent_config.sequencer
    // configuration.fuse_ctrl_lc_otp_in_if_agent_config.sequencer
    // configuration.fuse_ctrl_in_if_agent_config.sequencer

  // Responder agent sequencers in fuse_ctrl_environment:
    // configuration.fuse_ctrl_rst_out_agent_config.sequencer
    // configuration.fuse_ctrl_core_axi_write_out_if_agent_config.sequencer
    // configuration.fuse_ctrl_prim_axi_write_out_if_agent_config.sequencer
    // configuration.fuse_ctrl_core_axi_read_out_if_agent_config.sequencer
    // configuration.fuse_ctrl_prim_axi_read_out_if_agent_config.sequencer
    // configuration.fuse_ctrl_secreg_axi_read_out_if_agent_config.sequencer
    // configuration.fuse_ctrl_lc_otp_out_if_agent_config.sequencer
    // configuration.fuse_ctrl_out_if_agent_config.sequencer


    typedef fuse_ctrl_rst_in_random_sequence fuse_ctrl_rst_in_agent_random_sequence_t;
    fuse_ctrl_rst_in_agent_random_sequence_t fuse_ctrl_rst_in_agent_rand_seq;


    typedef fuse_ctrl_core_axi_write_in_random_sequence fuse_ctrl_core_axi_write_in_if_agent_random_sequence_t;
    fuse_ctrl_core_axi_write_in_if_agent_random_sequence_t fuse_ctrl_core_axi_write_in_if_agent_rand_seq;


    typedef fuse_ctrl_prim_axi_write_in_random_sequence fuse_ctrl_prim_axi_write_in_if_agent_random_sequence_t;
    fuse_ctrl_prim_axi_write_in_if_agent_random_sequence_t fuse_ctrl_prim_axi_write_in_if_agent_rand_seq;


    typedef fuse_ctrl_core_axi_read_in_random_sequence fuse_ctrl_core_axi_read_in_if_agent_random_sequence_t;
    fuse_ctrl_core_axi_read_in_if_agent_random_sequence_t fuse_ctrl_core_axi_read_in_if_agent_rand_seq;


    typedef fuse_ctrl_prim_axi_read_in_random_sequence fuse_ctrl_prim_axi_read_in_if_agent_random_sequence_t;
    fuse_ctrl_prim_axi_read_in_if_agent_random_sequence_t fuse_ctrl_prim_axi_read_in_if_agent_rand_seq;


    typedef fuse_ctrl_secreg_axi_read_in_random_sequence fuse_ctrl_secreg_axi_read_in_if_agent_random_sequence_t;
    fuse_ctrl_secreg_axi_read_in_if_agent_random_sequence_t fuse_ctrl_secreg_axi_read_in_if_agent_rand_seq;


    typedef fuse_ctrl_lc_otp_in_random_sequence fuse_ctrl_lc_otp_in_if_agent_random_sequence_t;
    fuse_ctrl_lc_otp_in_if_agent_random_sequence_t fuse_ctrl_lc_otp_in_if_agent_rand_seq;


    typedef fuse_ctrl_in_random_sequence fuse_ctrl_in_if_agent_random_sequence_t;
    fuse_ctrl_in_if_agent_random_sequence_t fuse_ctrl_in_if_agent_rand_seq;





  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  function new(string name = "" );
    super.new(name);
    fuse_ctrl_rst_in_agent_rand_seq = fuse_ctrl_rst_in_agent_random_sequence_t::type_id::create("fuse_ctrl_rst_in_agent_rand_seq");
    fuse_ctrl_core_axi_write_in_if_agent_rand_seq = fuse_ctrl_core_axi_write_in_if_agent_random_sequence_t::type_id::create("fuse_ctrl_core_axi_write_in_if_agent_rand_seq");
    fuse_ctrl_prim_axi_write_in_if_agent_rand_seq = fuse_ctrl_prim_axi_write_in_if_agent_random_sequence_t::type_id::create("fuse_ctrl_prim_axi_write_in_if_agent_rand_seq");
    fuse_ctrl_core_axi_read_in_if_agent_rand_seq = fuse_ctrl_core_axi_read_in_if_agent_random_sequence_t::type_id::create("fuse_ctrl_core_axi_read_in_if_agent_rand_seq");
    fuse_ctrl_prim_axi_read_in_if_agent_rand_seq = fuse_ctrl_prim_axi_read_in_if_agent_random_sequence_t::type_id::create("fuse_ctrl_prim_axi_read_in_if_agent_rand_seq");
    fuse_ctrl_secreg_axi_read_in_if_agent_rand_seq = fuse_ctrl_secreg_axi_read_in_if_agent_random_sequence_t::type_id::create("fuse_ctrl_secreg_axi_read_in_if_agent_rand_seq");
    fuse_ctrl_lc_otp_in_if_agent_rand_seq = fuse_ctrl_lc_otp_in_if_agent_random_sequence_t::type_id::create("fuse_ctrl_lc_otp_in_if_agent_rand_seq");
    fuse_ctrl_in_if_agent_rand_seq = fuse_ctrl_in_if_agent_random_sequence_t::type_id::create("fuse_ctrl_in_if_agent_rand_seq");


  endfunction

  virtual task body();

    if ( configuration.fuse_ctrl_rst_in_agent_config.sequencer != null )
       repeat (25) fuse_ctrl_rst_in_agent_rand_seq.start(configuration.fuse_ctrl_rst_in_agent_config.sequencer);
    if ( configuration.fuse_ctrl_core_axi_write_in_if_agent_config.sequencer != null )
       repeat (25) fuse_ctrl_core_axi_write_in_if_agent_rand_seq.start(configuration.fuse_ctrl_core_axi_write_in_if_agent_config.sequencer);
    if ( configuration.fuse_ctrl_prim_axi_write_in_if_agent_config.sequencer != null )
       repeat (25) fuse_ctrl_prim_axi_write_in_if_agent_rand_seq.start(configuration.fuse_ctrl_prim_axi_write_in_if_agent_config.sequencer);
    if ( configuration.fuse_ctrl_core_axi_read_in_if_agent_config.sequencer != null )
       repeat (25) fuse_ctrl_core_axi_read_in_if_agent_rand_seq.start(configuration.fuse_ctrl_core_axi_read_in_if_agent_config.sequencer);
    if ( configuration.fuse_ctrl_prim_axi_read_in_if_agent_config.sequencer != null )
       repeat (25) fuse_ctrl_prim_axi_read_in_if_agent_rand_seq.start(configuration.fuse_ctrl_prim_axi_read_in_if_agent_config.sequencer);
    if ( configuration.fuse_ctrl_secreg_axi_read_in_if_agent_config.sequencer != null )
       repeat (25) fuse_ctrl_secreg_axi_read_in_if_agent_rand_seq.start(configuration.fuse_ctrl_secreg_axi_read_in_if_agent_config.sequencer);
    if ( configuration.fuse_ctrl_lc_otp_in_if_agent_config.sequencer != null )
       repeat (25) fuse_ctrl_lc_otp_in_if_agent_rand_seq.start(configuration.fuse_ctrl_lc_otp_in_if_agent_config.sequencer);
    if ( configuration.fuse_ctrl_in_if_agent_config.sequencer != null )
       repeat (25) fuse_ctrl_in_if_agent_rand_seq.start(configuration.fuse_ctrl_in_if_agent_config.sequencer);


  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

