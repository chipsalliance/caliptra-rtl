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
// Description: This file contains the top level and utility sequences
//     used by test_top. It can be extended to create derivative top
//     level sequences.
//
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
//


typedef pv_env_configuration  pv_env_configuration_t;

class pv_bench_sequence_base extends uvmf_sequence_base #(uvm_sequence_item);

  `uvm_object_utils( pv_bench_sequence_base );

  // pragma uvmf custom sequences begin

typedef pv_env_sequence_base #(
        .CONFIG_T(pv_env_configuration_t)
        )
        pv_env_sequence_base_t;
rand pv_env_sequence_base_t pv_env_seq;



  // UVMF_CHANGE_ME : Instantiate, construct, and start sequences as needed to create stimulus scenarios.
  // Instantiate sequences here
  typedef pv_rst_random_sequence  pv_rst_agent_random_seq_t;
  pv_rst_agent_random_seq_t pv_rst_agent_random_seq;
  typedef pv_write_random_sequence  pv_sha512_write_agent_random_seq_t;
  pv_sha512_write_agent_random_seq_t pv_sha512_write_agent_random_seq;
  typedef pv_read_random_sequence  pv_sha512_block_read_agent_random_seq_t;
  pv_sha512_block_read_agent_random_seq_t pv_sha512_block_read_agent_random_seq;
  // pragma uvmf custom sequences end

  // Sequencer handles for each active interface in the environment
  typedef pv_rst_transaction  pv_rst_agent_transaction_t;
  uvm_sequencer #(pv_rst_agent_transaction_t)  pv_rst_agent_sequencer; 
  typedef pv_write_transaction  pv_sha512_write_agent_transaction_t;
  uvm_sequencer #(pv_sha512_write_agent_transaction_t)  pv_sha512_write_agent_sequencer; 
  typedef pv_read_transaction  pv_sha512_block_read_agent_transaction_t;
  uvm_sequencer #(pv_sha512_block_read_agent_transaction_t)  pv_sha512_block_read_agent_sequencer; 

  // Sequencer handles for each QVIP interface
  mvc_sequencer uvm_test_top_environment_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_sqr;

  // Top level environment configuration handle
  pv_env_configuration_t top_configuration;

  // Configuration handles to access interface BFM's
  pv_rst_configuration  pv_rst_agent_config;
  pv_write_configuration  pv_sha512_write_agent_config;
  pv_read_configuration  pv_sha512_block_read_agent_config;
  // Local handle to register model for convenience
  pv_reg_model_top reg_model;
  uvm_status_e status;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  // ****************************************************************************
  function new( string name = "" );
    super.new( name );
    // Retrieve the configuration handles from the uvm_config_db

    // Retrieve top level configuration handle
    if ( !uvm_config_db#(pv_env_configuration_t)::get(null,UVMF_CONFIGURATIONS, "TOP_ENV_CONFIG",top_configuration) ) begin
      `uvm_info("CFG", "*** FATAL *** uvm_config_db::get can not find TOP_ENV_CONFIG.  Are you using an older UVMF release than what was used to generate this bench?",UVM_NONE);
      `uvm_fatal("CFG", "uvm_config_db#(pv_env_configuration_t)::get cannot find resource TOP_ENV_CONFIG");
    end

    // Retrieve config handles for all agents
    if( !uvm_config_db #( pv_rst_configuration )::get( null , UVMF_CONFIGURATIONS , pv_rst_agent_BFM , pv_rst_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( pv_rst_configuration )::get cannot find resource pv_rst_agent_BFM" )
    if( !uvm_config_db #( pv_write_configuration )::get( null , UVMF_CONFIGURATIONS , pv_sha512_write_agent_BFM , pv_sha512_write_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( pv_write_configuration )::get cannot find resource pv_sha512_write_agent_BFM" )
    if( !uvm_config_db #( pv_read_configuration )::get( null , UVMF_CONFIGURATIONS , pv_sha512_block_read_agent_BFM , pv_sha512_block_read_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( pv_read_configuration )::get cannot find resource pv_sha512_block_read_agent_BFM" )

    // Assign the sequencer handles from the handles within agent configurations
    pv_rst_agent_sequencer = pv_rst_agent_config.get_sequencer();
    pv_sha512_write_agent_sequencer = pv_sha512_write_agent_config.get_sequencer();
    pv_sha512_block_read_agent_sequencer = pv_sha512_block_read_agent_config.get_sequencer();

    // Retrieve QVIP sequencer handles from the uvm_config_db
    if( !uvm_config_db #(mvc_sequencer)::get( null,UVMF_SEQUENCERS,"uvm_test_top.environment.qvip_ahb_lite_slave_subenv.ahb_lite_slave_0", uvm_test_top_environment_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_sqr) ) 
      `uvm_warning("CFG" , "uvm_config_db #( mvc_sequencer )::get cannot find resource ahb_lite_slave_0" ) 
    reg_model = top_configuration.pv_rm;


    // pragma uvmf custom new begin
    // pragma uvmf custom new end

  endfunction

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin

    // Construct sequences here

    pv_env_seq = pv_env_sequence_base_t::type_id::create("pv_env_seq");

    pv_rst_agent_random_seq     = pv_rst_agent_random_seq_t::type_id::create("pv_rst_agent_random_seq");
    pv_sha512_write_agent_random_seq     = pv_sha512_write_agent_random_seq_t::type_id::create("pv_sha512_write_agent_random_seq");
    pv_sha512_block_read_agent_random_seq     = pv_sha512_block_read_agent_random_seq_t::type_id::create("pv_sha512_block_read_agent_random_seq");
    fork
      pv_rst_agent_config.wait_for_reset();
      pv_sha512_write_agent_config.wait_for_reset();
      pv_sha512_block_read_agent_config.wait_for_reset();
    join
    reg_model.reset();
    // Start RESPONDER sequences here
    fork
    join_none
    // Start INITIATOR sequences here
    fork
      repeat (25) pv_rst_agent_random_seq.start(pv_rst_agent_sequencer);
      repeat (25) pv_sha512_write_agent_random_seq.start(pv_sha512_write_agent_sequencer);
      repeat (25) pv_sha512_block_read_agent_random_seq.start(pv_sha512_block_read_agent_sequencer);
    join

pv_env_seq.start(top_configuration.vsqr);

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      pv_rst_agent_config.wait_for_num_clocks(400);
      pv_sha512_write_agent_config.wait_for_num_clocks(400);
      pv_sha512_block_read_agent_config.wait_for_num_clocks(400);
    join

    // pragma uvmf custom body end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

