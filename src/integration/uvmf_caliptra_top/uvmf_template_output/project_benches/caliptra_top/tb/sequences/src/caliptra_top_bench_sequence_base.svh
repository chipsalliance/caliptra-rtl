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


typedef caliptra_top_env_configuration  caliptra_top_env_configuration_t;

class caliptra_top_bench_sequence_base extends uvmf_sequence_base #(uvm_sequence_item);

  `uvm_object_utils( caliptra_top_bench_sequence_base );

  // pragma uvmf custom sequences begin

typedef caliptra_top_env_sequence_base #(
        .CONFIG_T(caliptra_top_env_configuration_t)
        )
        caliptra_top_env_sequence_base_t;
rand caliptra_top_env_sequence_base_t caliptra_top_env_seq;
typedef soc_ifc_env_sequence_base #(
        .CONFIG_T(soc_ifc_env_configuration_t)
        )
        soc_ifc_env_sequence_base_t;
rand soc_ifc_env_sequence_base_t soc_ifc_env_seq;



  // UVMF_CHANGE_ME : Instantiate, construct, and start sequences as needed to create stimulus scenarios.
  // Instantiate sequences here
  typedef soc_ifc_ctrl_random_sequence  soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq_t;
  soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq_t soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq;
  typedef soc_ifc_status_responder_sequence  soc_ifc_subenv_soc_ifc_status_agent_responder_seq_t;
  soc_ifc_subenv_soc_ifc_status_agent_responder_seq_t soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
  typedef mbox_sram_responder_sequence  soc_ifc_subenv_mbox_sram_agent_responder_seq_t;
  soc_ifc_subenv_mbox_sram_agent_responder_seq_t soc_ifc_subenv_mbox_sram_agent_responder_seq;
  // pragma uvmf custom sequences end

  // Sequencer handles for each active interface in the environment
  typedef soc_ifc_ctrl_transaction  soc_ifc_subenv_soc_ifc_ctrl_agent_transaction_t;
  uvm_sequencer #(soc_ifc_subenv_soc_ifc_ctrl_agent_transaction_t)  soc_ifc_subenv_soc_ifc_ctrl_agent_sequencer; 
  typedef soc_ifc_status_transaction  soc_ifc_subenv_soc_ifc_status_agent_transaction_t;
  uvm_sequencer #(soc_ifc_subenv_soc_ifc_status_agent_transaction_t)  soc_ifc_subenv_soc_ifc_status_agent_sequencer; 
  typedef mbox_sram_transaction  soc_ifc_subenv_mbox_sram_agent_transaction_t;
  uvm_sequencer #(soc_ifc_subenv_mbox_sram_agent_transaction_t)  soc_ifc_subenv_mbox_sram_agent_sequencer; 

  // Sequencer handles for each QVIP interface
  mvc_sequencer uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_sqr;
  mvc_sequencer uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_apb5_master_0_sqr;

  // Top level environment configuration handle
  caliptra_top_env_configuration_t top_configuration;

  // Configuration handles to access interface BFM's
  soc_ifc_ctrl_configuration  soc_ifc_subenv_soc_ifc_ctrl_agent_config;
  cptra_ctrl_configuration  soc_ifc_subenv_cptra_ctrl_agent_config;
  soc_ifc_status_configuration  soc_ifc_subenv_soc_ifc_status_agent_config;
  cptra_status_configuration  soc_ifc_subenv_cptra_status_agent_config;
  mbox_sram_configuration  soc_ifc_subenv_mbox_sram_agent_config;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  // ****************************************************************************
  function new( string name = "" );
    super.new( name );
    // Retrieve the configuration handles from the uvm_config_db

    // Retrieve top level configuration handle
    if ( !uvm_config_db#(caliptra_top_env_configuration_t)::get(null,UVMF_CONFIGURATIONS, "TOP_ENV_CONFIG",top_configuration) ) begin
      `uvm_info("CFG", "*** FATAL *** uvm_config_db::get can not find TOP_ENV_CONFIG.  Are you using an older UVMF release than what was used to generate this bench?",UVM_NONE);
      `uvm_fatal("CFG", "uvm_config_db#(caliptra_top_env_configuration_t)::get cannot find resource TOP_ENV_CONFIG");
    end

    // Retrieve config handles for all agents
    if( !uvm_config_db #( soc_ifc_ctrl_configuration )::get( null , UVMF_CONFIGURATIONS , soc_ifc_subenv_soc_ifc_ctrl_agent_BFM , soc_ifc_subenv_soc_ifc_ctrl_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( soc_ifc_ctrl_configuration )::get cannot find resource soc_ifc_subenv_soc_ifc_ctrl_agent_BFM" )
    if( !uvm_config_db #( cptra_ctrl_configuration )::get( null , UVMF_CONFIGURATIONS , soc_ifc_subenv_cptra_ctrl_agent_BFM , soc_ifc_subenv_cptra_ctrl_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( cptra_ctrl_configuration )::get cannot find resource soc_ifc_subenv_cptra_ctrl_agent_BFM" )
    if( !uvm_config_db #( soc_ifc_status_configuration )::get( null , UVMF_CONFIGURATIONS , soc_ifc_subenv_soc_ifc_status_agent_BFM , soc_ifc_subenv_soc_ifc_status_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( soc_ifc_status_configuration )::get cannot find resource soc_ifc_subenv_soc_ifc_status_agent_BFM" )
    if( !uvm_config_db #( cptra_status_configuration )::get( null , UVMF_CONFIGURATIONS , soc_ifc_subenv_cptra_status_agent_BFM , soc_ifc_subenv_cptra_status_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( cptra_status_configuration )::get cannot find resource soc_ifc_subenv_cptra_status_agent_BFM" )
    if( !uvm_config_db #( mbox_sram_configuration )::get( null , UVMF_CONFIGURATIONS , soc_ifc_subenv_mbox_sram_agent_BFM , soc_ifc_subenv_mbox_sram_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( mbox_sram_configuration )::get cannot find resource soc_ifc_subenv_mbox_sram_agent_BFM" )

    // Assign the sequencer handles from the handles within agent configurations
    soc_ifc_subenv_soc_ifc_ctrl_agent_sequencer = soc_ifc_subenv_soc_ifc_ctrl_agent_config.get_sequencer();
    soc_ifc_subenv_soc_ifc_status_agent_sequencer = soc_ifc_subenv_soc_ifc_status_agent_config.get_sequencer();
    soc_ifc_subenv_mbox_sram_agent_sequencer = soc_ifc_subenv_mbox_sram_agent_config.get_sequencer();

    // Retrieve QVIP sequencer handles from the uvm_config_db
    if( !uvm_config_db #(mvc_sequencer)::get( null,UVMF_SEQUENCERS,"uvm_test_top.environment.soc_ifc_subenv.qvip_apb5_slave_subenv.apb5_master_0", uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_apb5_master_0_sqr) ) 
      `uvm_warning("CFG" , "uvm_config_db #( mvc_sequencer )::get cannot find resource apb5_master_0" ) 


    // pragma uvmf custom new begin
    // pragma uvmf custom new end

  endfunction

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin

    // Construct sequences here

    caliptra_top_env_seq = caliptra_top_env_sequence_base_t::type_id::create("caliptra_top_env_seq");

    soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq      = soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq");
    soc_ifc_subenv_soc_ifc_status_agent_responder_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_status_agent_responder_seq");
    soc_ifc_subenv_mbox_sram_agent_responder_seq      = soc_ifc_subenv_mbox_sram_agent_responder_seq_t::type_id::create("soc_ifc_subenv_mbox_sram_agent_responder_seq");
    fork
      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_reset();
      soc_ifc_subenv_cptra_ctrl_agent_config.wait_for_reset();
      soc_ifc_subenv_soc_ifc_status_agent_config.wait_for_reset();
      soc_ifc_subenv_cptra_status_agent_config.wait_for_reset();
      soc_ifc_subenv_mbox_sram_agent_config.wait_for_reset();
    join
    // Start RESPONDER sequences here
    fork
      soc_ifc_subenv_soc_ifc_status_agent_responder_seq.start(soc_ifc_subenv_soc_ifc_status_agent_sequencer);
      soc_ifc_subenv_mbox_sram_agent_responder_seq.start(soc_ifc_subenv_mbox_sram_agent_sequencer);
    join_none
    // Start INITIATOR sequences here
    fork
      repeat (25) soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq.start(soc_ifc_subenv_soc_ifc_ctrl_agent_sequencer);
    join

caliptra_top_env_seq.start(top_configuration.vsqr);

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(400);
      soc_ifc_subenv_cptra_ctrl_agent_config.wait_for_num_clocks(400);
      soc_ifc_subenv_soc_ifc_status_agent_config.wait_for_num_clocks(400);
      soc_ifc_subenv_cptra_status_agent_config.wait_for_num_clocks(400);
      soc_ifc_subenv_mbox_sram_agent_config.wait_for_num_clocks(400);
    join

    // pragma uvmf custom body end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

