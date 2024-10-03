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


typedef fuse_ctrl_env_configuration  fuse_ctrl_env_configuration_t;

class fuse_ctrl_bench_sequence_base extends uvmf_sequence_base #(uvm_sequence_item);

  `uvm_object_utils( fuse_ctrl_bench_sequence_base );

  // pragma uvmf custom sequences begin

typedef fuse_ctrl_env_sequence_base #(
        .CONFIG_T(fuse_ctrl_env_configuration_t)
        )
        fuse_ctrl_env_sequence_base_t;
rand fuse_ctrl_env_sequence_base_t fuse_ctrl_env_seq;



  // UVMF_CHANGE_ME : Instantiate, construct, and start sequences as needed to create stimulus scenarios.
  // Instantiate sequences here
  typedef fuse_ctrl_rst_random_sequence  fuse_ctrl_rst_agent_random_seq_t;
  fuse_ctrl_rst_agent_random_seq_t fuse_ctrl_rst_agent_random_seq;
  typedef fuse_ctrl_core_axi_write_if_random_sequence  fuse_ctrl_core_axi_write_agent_random_seq_t;
  fuse_ctrl_core_axi_write_agent_random_seq_t fuse_ctrl_core_axi_write_agent_random_seq;
  typedef fuse_ctrl_prim_axi_write_if_random_sequence  fuse_ctrl_prim_axi_write_agent_random_seq_t;
  fuse_ctrl_prim_axi_write_agent_random_seq_t fuse_ctrl_prim_axi_write_agent_random_seq;
  typedef fuse_ctrl_core_axi_read_if_random_sequence  fuse_ctrl_core_axi_read_agent_random_seq_t;
  fuse_ctrl_core_axi_read_agent_random_seq_t fuse_ctrl_core_axi_read_agent_random_seq;
  typedef fuse_ctrl_prim_axi_read_if_random_sequence  fuse_ctrl_prim_axi_read_agent_random_seq_t;
  fuse_ctrl_prim_axi_read_agent_random_seq_t fuse_ctrl_prim_axi_read_agent_random_seq;
  typedef fuse_ctrl_secreg_axi_read_if_random_sequence  fuse_ctrl_secreg_axi_read_agent_random_seq_t;
  fuse_ctrl_secreg_axi_read_agent_random_seq_t fuse_ctrl_secreg_axi_read_agent_random_seq;
  typedef fuse_ctrl_lc_otp_if_random_sequence  fuse_ctrl_lc_otp_if_agent_random_seq_t;
  fuse_ctrl_lc_otp_if_agent_random_seq_t fuse_ctrl_lc_otp_if_agent_random_seq;
  // pragma uvmf custom sequences end

  // Sequencer handles for each active interface in the environment
  typedef fuse_ctrl_rst_transaction  fuse_ctrl_rst_agent_transaction_t;
  uvm_sequencer #(fuse_ctrl_rst_agent_transaction_t)  fuse_ctrl_rst_agent_sequencer; 
  typedef fuse_ctrl_core_axi_write_if_transaction  fuse_ctrl_core_axi_write_agent_transaction_t;
  uvm_sequencer #(fuse_ctrl_core_axi_write_agent_transaction_t)  fuse_ctrl_core_axi_write_agent_sequencer; 
  typedef fuse_ctrl_prim_axi_write_if_transaction  fuse_ctrl_prim_axi_write_agent_transaction_t;
  uvm_sequencer #(fuse_ctrl_prim_axi_write_agent_transaction_t)  fuse_ctrl_prim_axi_write_agent_sequencer; 
  typedef fuse_ctrl_core_axi_read_if_transaction  fuse_ctrl_core_axi_read_agent_transaction_t;
  uvm_sequencer #(fuse_ctrl_core_axi_read_agent_transaction_t)  fuse_ctrl_core_axi_read_agent_sequencer; 
  typedef fuse_ctrl_prim_axi_read_if_transaction  fuse_ctrl_prim_axi_read_agent_transaction_t;
  uvm_sequencer #(fuse_ctrl_prim_axi_read_agent_transaction_t)  fuse_ctrl_prim_axi_read_agent_sequencer; 
  typedef fuse_ctrl_secreg_axi_read_if_transaction  fuse_ctrl_secreg_axi_read_agent_transaction_t;
  uvm_sequencer #(fuse_ctrl_secreg_axi_read_agent_transaction_t)  fuse_ctrl_secreg_axi_read_agent_sequencer; 
  typedef fuse_ctrl_lc_otp_if_transaction  fuse_ctrl_lc_otp_if_agent_transaction_t;
  uvm_sequencer #(fuse_ctrl_lc_otp_if_agent_transaction_t)  fuse_ctrl_lc_otp_if_agent_sequencer; 
  typedef fuse_ctrl_in_if_transaction  fuse_ctrl_in_if_agent_transaction_t;
  uvm_sequencer #(fuse_ctrl_in_if_agent_transaction_t)  fuse_ctrl_in_if_agent_sequencer; 


  // Top level environment configuration handle
  fuse_ctrl_env_configuration_t top_configuration;

  // Configuration handles to access interface BFM's
  fuse_ctrl_rst_configuration  fuse_ctrl_rst_agent_config;
  fuse_ctrl_core_axi_write_if_configuration  fuse_ctrl_core_axi_write_agent_config;
  fuse_ctrl_prim_axi_write_if_configuration  fuse_ctrl_prim_axi_write_agent_config;
  fuse_ctrl_core_axi_read_if_configuration  fuse_ctrl_core_axi_read_agent_config;
  fuse_ctrl_prim_axi_read_if_configuration  fuse_ctrl_prim_axi_read_agent_config;
  fuse_ctrl_secreg_axi_read_if_configuration  fuse_ctrl_secreg_axi_read_agent_config;
  fuse_ctrl_lc_otp_if_configuration  fuse_ctrl_lc_otp_if_agent_config;
  fuse_ctrl_in_if_configuration  fuse_ctrl_in_if_agent_config;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  // ****************************************************************************
  function new( string name = "" );
    super.new( name );
    // Retrieve the configuration handles from the uvm_config_db

    // Retrieve top level configuration handle
    if ( !uvm_config_db#(fuse_ctrl_env_configuration_t)::get(null,UVMF_CONFIGURATIONS, "TOP_ENV_CONFIG",top_configuration) ) begin
      `uvm_info("CFG", "*** FATAL *** uvm_config_db::get can not find TOP_ENV_CONFIG.  Are you using an older UVMF release than what was used to generate this bench?",UVM_NONE);
      `uvm_fatal("CFG", "uvm_config_db#(fuse_ctrl_env_configuration_t)::get cannot find resource TOP_ENV_CONFIG");
    end

    // Retrieve config handles for all agents
    if( !uvm_config_db #( fuse_ctrl_rst_configuration )::get( null , UVMF_CONFIGURATIONS , fuse_ctrl_rst_agent_BFM , fuse_ctrl_rst_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( fuse_ctrl_rst_configuration )::get cannot find resource fuse_ctrl_rst_agent_BFM" )
    if( !uvm_config_db #( fuse_ctrl_core_axi_write_if_configuration )::get( null , UVMF_CONFIGURATIONS , fuse_ctrl_core_axi_write_agent_BFM , fuse_ctrl_core_axi_write_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( fuse_ctrl_core_axi_write_if_configuration )::get cannot find resource fuse_ctrl_core_axi_write_agent_BFM" )
    if( !uvm_config_db #( fuse_ctrl_prim_axi_write_if_configuration )::get( null , UVMF_CONFIGURATIONS , fuse_ctrl_prim_axi_write_agent_BFM , fuse_ctrl_prim_axi_write_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( fuse_ctrl_prim_axi_write_if_configuration )::get cannot find resource fuse_ctrl_prim_axi_write_agent_BFM" )
    if( !uvm_config_db #( fuse_ctrl_core_axi_read_if_configuration )::get( null , UVMF_CONFIGURATIONS , fuse_ctrl_core_axi_read_agent_BFM , fuse_ctrl_core_axi_read_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( fuse_ctrl_core_axi_read_if_configuration )::get cannot find resource fuse_ctrl_core_axi_read_agent_BFM" )
    if( !uvm_config_db #( fuse_ctrl_prim_axi_read_if_configuration )::get( null , UVMF_CONFIGURATIONS , fuse_ctrl_prim_axi_read_agent_BFM , fuse_ctrl_prim_axi_read_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( fuse_ctrl_prim_axi_read_if_configuration )::get cannot find resource fuse_ctrl_prim_axi_read_agent_BFM" )
    if( !uvm_config_db #( fuse_ctrl_secreg_axi_read_if_configuration )::get( null , UVMF_CONFIGURATIONS , fuse_ctrl_secreg_axi_read_agent_BFM , fuse_ctrl_secreg_axi_read_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( fuse_ctrl_secreg_axi_read_if_configuration )::get cannot find resource fuse_ctrl_secreg_axi_read_agent_BFM" )
    if( !uvm_config_db #( fuse_ctrl_lc_otp_if_configuration )::get( null , UVMF_CONFIGURATIONS , fuse_ctrl_lc_otp_if_agent_BFM , fuse_ctrl_lc_otp_if_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( fuse_ctrl_lc_otp_if_configuration )::get cannot find resource fuse_ctrl_lc_otp_if_agent_BFM" )
    if( !uvm_config_db #( fuse_ctrl_in_if_configuration )::get( null , UVMF_CONFIGURATIONS , fuse_ctrl_in_if_agent_BFM , fuse_ctrl_in_if_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( fuse_ctrl_in_if_configuration )::get cannot find resource fuse_ctrl_in_if_agent_BFM" )

    // Assign the sequencer handles from the handles within agent configurations
    fuse_ctrl_rst_agent_sequencer = fuse_ctrl_rst_agent_config.get_sequencer();
    fuse_ctrl_core_axi_write_agent_sequencer = fuse_ctrl_core_axi_write_agent_config.get_sequencer();
    fuse_ctrl_prim_axi_write_agent_sequencer = fuse_ctrl_prim_axi_write_agent_config.get_sequencer();
    fuse_ctrl_core_axi_read_agent_sequencer = fuse_ctrl_core_axi_read_agent_config.get_sequencer();
    fuse_ctrl_prim_axi_read_agent_sequencer = fuse_ctrl_prim_axi_read_agent_config.get_sequencer();
    fuse_ctrl_secreg_axi_read_agent_sequencer = fuse_ctrl_secreg_axi_read_agent_config.get_sequencer();
    fuse_ctrl_lc_otp_if_agent_sequencer = fuse_ctrl_lc_otp_if_agent_config.get_sequencer();
    fuse_ctrl_in_if_agent_sequencer = fuse_ctrl_in_if_agent_config.get_sequencer();



    // pragma uvmf custom new begin
    // pragma uvmf custom new end

  endfunction

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin

    // Construct sequences here

    fuse_ctrl_env_seq = fuse_ctrl_env_sequence_base_t::type_id::create("fuse_ctrl_env_seq");

    fuse_ctrl_rst_agent_random_seq     = fuse_ctrl_rst_agent_random_seq_t::type_id::create("fuse_ctrl_rst_agent_random_seq");
    fuse_ctrl_core_axi_write_agent_random_seq     = fuse_ctrl_core_axi_write_agent_random_seq_t::type_id::create("fuse_ctrl_core_axi_write_agent_random_seq");
    fuse_ctrl_prim_axi_write_agent_random_seq     = fuse_ctrl_prim_axi_write_agent_random_seq_t::type_id::create("fuse_ctrl_prim_axi_write_agent_random_seq");
    fuse_ctrl_core_axi_read_agent_random_seq     = fuse_ctrl_core_axi_read_agent_random_seq_t::type_id::create("fuse_ctrl_core_axi_read_agent_random_seq");
    fuse_ctrl_prim_axi_read_agent_random_seq     = fuse_ctrl_prim_axi_read_agent_random_seq_t::type_id::create("fuse_ctrl_prim_axi_read_agent_random_seq");
    fuse_ctrl_secreg_axi_read_agent_random_seq     = fuse_ctrl_secreg_axi_read_agent_random_seq_t::type_id::create("fuse_ctrl_secreg_axi_read_agent_random_seq");
    fuse_ctrl_lc_otp_if_agent_random_seq     = fuse_ctrl_lc_otp_if_agent_random_seq_t::type_id::create("fuse_ctrl_lc_otp_if_agent_random_seq");
    fork
      fuse_ctrl_rst_agent_config.wait_for_reset();
      fuse_ctrl_core_axi_write_agent_config.wait_for_reset();
      fuse_ctrl_prim_axi_write_agent_config.wait_for_reset();
      fuse_ctrl_core_axi_read_agent_config.wait_for_reset();
      fuse_ctrl_prim_axi_read_agent_config.wait_for_reset();
      fuse_ctrl_secreg_axi_read_agent_config.wait_for_reset();
      fuse_ctrl_lc_otp_if_agent_config.wait_for_reset();
    join
    // Start RESPONDER sequences here
    fork
    join_none
    // Start INITIATOR sequences here
    fork
      repeat (25) fuse_ctrl_rst_agent_random_seq.start(fuse_ctrl_rst_agent_sequencer);
      repeat (25) fuse_ctrl_core_axi_write_agent_random_seq.start(fuse_ctrl_core_axi_write_agent_sequencer);
      repeat (25) fuse_ctrl_prim_axi_write_agent_random_seq.start(fuse_ctrl_prim_axi_write_agent_sequencer);
      repeat (25) fuse_ctrl_core_axi_read_agent_random_seq.start(fuse_ctrl_core_axi_read_agent_sequencer);
      repeat (25) fuse_ctrl_prim_axi_read_agent_random_seq.start(fuse_ctrl_prim_axi_read_agent_sequencer);
      repeat (25) fuse_ctrl_secreg_axi_read_agent_random_seq.start(fuse_ctrl_secreg_axi_read_agent_sequencer);
      repeat (25) fuse_ctrl_lc_otp_if_agent_random_seq.start(fuse_ctrl_lc_otp_if_agent_sequencer);
    join

fuse_ctrl_env_seq.start(top_configuration.vsqr);

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      fuse_ctrl_rst_agent_config.wait_for_num_clocks(400);
      fuse_ctrl_core_axi_write_agent_config.wait_for_num_clocks(400);
      fuse_ctrl_prim_axi_write_agent_config.wait_for_num_clocks(400);
      fuse_ctrl_core_axi_read_agent_config.wait_for_num_clocks(400);
      fuse_ctrl_prim_axi_read_agent_config.wait_for_num_clocks(400);
      fuse_ctrl_secreg_axi_read_agent_config.wait_for_num_clocks(400);
      fuse_ctrl_lc_otp_if_agent_config.wait_for_num_clocks(400);
    join

    // pragma uvmf custom body end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

