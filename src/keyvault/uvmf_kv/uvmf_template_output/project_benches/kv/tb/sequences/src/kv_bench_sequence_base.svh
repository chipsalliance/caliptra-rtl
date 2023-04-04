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


typedef kv_env_configuration  kv_env_configuration_t;

class kv_bench_sequence_base extends uvmf_sequence_base #(uvm_sequence_item);

  `uvm_object_utils( kv_bench_sequence_base );

  // pragma uvmf custom sequences begin

typedef kv_env_sequence_base #(
        .CONFIG_T(kv_env_configuration_t)
        )
        kv_env_sequence_base_t;
rand kv_env_sequence_base_t kv_env_seq;



  // UVMF_CHANGE_ME : Instantiate, construct, and start sequences as needed to create stimulus scenarios.
  // Instantiate sequences here
  typedef kv_rst_random_sequence  kv_rst_agent_random_seq_t;
  kv_rst_agent_random_seq_t kv_rst_agent_random_seq;
  typedef kv_write_random_sequence  kv_hmac_write_agent_random_seq_t;
  kv_hmac_write_agent_random_seq_t kv_hmac_write_agent_random_seq;
  typedef kv_write_random_sequence  kv_sha512_write_agent_random_seq_t;
  kv_sha512_write_agent_random_seq_t kv_sha512_write_agent_random_seq;
  typedef kv_write_random_sequence  kv_ecc_write_agent_random_seq_t;
  kv_ecc_write_agent_random_seq_t kv_ecc_write_agent_random_seq;
  typedef kv_write_random_sequence  kv_doe_write_agent_random_seq_t;
  kv_doe_write_agent_random_seq_t kv_doe_write_agent_random_seq;
  typedef kv_read_random_sequence  kv_hmac_key_read_agent_random_seq_t;
  kv_hmac_key_read_agent_random_seq_t kv_hmac_key_read_agent_random_seq;
  typedef kv_read_random_sequence  kv_hmac_block_read_agent_random_seq_t;
  kv_hmac_block_read_agent_random_seq_t kv_hmac_block_read_agent_random_seq;
  typedef kv_read_random_sequence  kv_sha512_block_read_agent_random_seq_t;
  kv_sha512_block_read_agent_random_seq_t kv_sha512_block_read_agent_random_seq;
  typedef kv_read_random_sequence  kv_ecc_privkey_read_agent_random_seq_t;
  kv_ecc_privkey_read_agent_random_seq_t kv_ecc_privkey_read_agent_random_seq;
  typedef kv_read_random_sequence  kv_ecc_seed_read_agent_random_seq_t;
  kv_ecc_seed_read_agent_random_seq_t kv_ecc_seed_read_agent_random_seq;
  // pragma uvmf custom sequences end

  // Sequencer handles for each active interface in the environment
  typedef kv_rst_transaction  kv_rst_agent_transaction_t;
  uvm_sequencer #(kv_rst_agent_transaction_t)  kv_rst_agent_sequencer; 
  typedef kv_write_transaction  kv_hmac_write_agent_transaction_t;
  uvm_sequencer #(kv_hmac_write_agent_transaction_t)  kv_hmac_write_agent_sequencer; 
  typedef kv_write_transaction  kv_sha512_write_agent_transaction_t;
  uvm_sequencer #(kv_sha512_write_agent_transaction_t)  kv_sha512_write_agent_sequencer; 
  typedef kv_write_transaction  kv_ecc_write_agent_transaction_t;
  uvm_sequencer #(kv_ecc_write_agent_transaction_t)  kv_ecc_write_agent_sequencer; 
  typedef kv_write_transaction  kv_doe_write_agent_transaction_t;
  uvm_sequencer #(kv_doe_write_agent_transaction_t)  kv_doe_write_agent_sequencer; 
  typedef kv_read_transaction  kv_hmac_key_read_agent_transaction_t;
  uvm_sequencer #(kv_hmac_key_read_agent_transaction_t)  kv_hmac_key_read_agent_sequencer; 
  typedef kv_read_transaction  kv_hmac_block_read_agent_transaction_t;
  uvm_sequencer #(kv_hmac_block_read_agent_transaction_t)  kv_hmac_block_read_agent_sequencer; 
  typedef kv_read_transaction  kv_sha512_block_read_agent_transaction_t;
  uvm_sequencer #(kv_sha512_block_read_agent_transaction_t)  kv_sha512_block_read_agent_sequencer; 
  typedef kv_read_transaction  kv_ecc_privkey_read_agent_transaction_t;
  uvm_sequencer #(kv_ecc_privkey_read_agent_transaction_t)  kv_ecc_privkey_read_agent_sequencer; 
  typedef kv_read_transaction  kv_ecc_seed_read_agent_transaction_t;
  uvm_sequencer #(kv_ecc_seed_read_agent_transaction_t)  kv_ecc_seed_read_agent_sequencer; 

  // Sequencer handles for each QVIP interface
  mvc_sequencer uvm_test_top_environment_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_sqr;

  // Top level environment configuration handle
  kv_env_configuration_t top_configuration;

  // Configuration handles to access interface BFM's
  kv_rst_configuration  kv_rst_agent_config;
  kv_write_configuration  kv_hmac_write_agent_config;
  kv_write_configuration  kv_sha512_write_agent_config;
  kv_write_configuration  kv_ecc_write_agent_config;
  kv_write_configuration  kv_doe_write_agent_config;
  kv_read_configuration  kv_hmac_key_read_agent_config;
  kv_read_configuration  kv_hmac_block_read_agent_config;
  kv_read_configuration  kv_sha512_block_read_agent_config;
  kv_read_configuration  kv_ecc_privkey_read_agent_config;
  kv_read_configuration  kv_ecc_seed_read_agent_config;
  // Local handle to register model for convenience
  kv_reg_model_top reg_model;
  uvm_status_e status;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  // ****************************************************************************
  function new( string name = "" );
    super.new( name );
    // Retrieve the configuration handles from the uvm_config_db

    // Retrieve top level configuration handle
    if ( !uvm_config_db#(kv_env_configuration_t)::get(null,UVMF_CONFIGURATIONS, "TOP_ENV_CONFIG",top_configuration) ) begin
      `uvm_info("CFG", "*** FATAL *** uvm_config_db::get can not find TOP_ENV_CONFIG.  Are you using an older UVMF release than what was used to generate this bench?",UVM_NONE);
      `uvm_fatal("CFG", "uvm_config_db#(kv_env_configuration_t)::get cannot find resource TOP_ENV_CONFIG");
    end

    // Retrieve config handles for all agents
    if( !uvm_config_db #( kv_rst_configuration )::get( null , UVMF_CONFIGURATIONS , kv_rst_agent_BFM , kv_rst_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( kv_rst_configuration )::get cannot find resource kv_rst_agent_BFM" )
    if( !uvm_config_db #( kv_write_configuration )::get( null , UVMF_CONFIGURATIONS , kv_hmac_write_agent_BFM , kv_hmac_write_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( kv_write_configuration )::get cannot find resource kv_hmac_write_agent_BFM" )
    if( !uvm_config_db #( kv_write_configuration )::get( null , UVMF_CONFIGURATIONS , kv_sha512_write_agent_BFM , kv_sha512_write_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( kv_write_configuration )::get cannot find resource kv_sha512_write_agent_BFM" )
    if( !uvm_config_db #( kv_write_configuration )::get( null , UVMF_CONFIGURATIONS , kv_ecc_write_agent_BFM , kv_ecc_write_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( kv_write_configuration )::get cannot find resource kv_ecc_write_agent_BFM" )
    if( !uvm_config_db #( kv_write_configuration )::get( null , UVMF_CONFIGURATIONS , kv_doe_write_agent_BFM , kv_doe_write_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( kv_write_configuration )::get cannot find resource kv_doe_write_agent_BFM" )
    if( !uvm_config_db #( kv_read_configuration )::get( null , UVMF_CONFIGURATIONS , kv_hmac_key_read_agent_BFM , kv_hmac_key_read_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( kv_read_configuration )::get cannot find resource kv_hmac_key_read_agent_BFM" )
    if( !uvm_config_db #( kv_read_configuration )::get( null , UVMF_CONFIGURATIONS , kv_hmac_block_read_agent_BFM , kv_hmac_block_read_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( kv_read_configuration )::get cannot find resource kv_hmac_block_read_agent_BFM" )
    if( !uvm_config_db #( kv_read_configuration )::get( null , UVMF_CONFIGURATIONS , kv_sha512_block_read_agent_BFM , kv_sha512_block_read_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( kv_read_configuration )::get cannot find resource kv_sha512_block_read_agent_BFM" )
    if( !uvm_config_db #( kv_read_configuration )::get( null , UVMF_CONFIGURATIONS , kv_ecc_privkey_read_agent_BFM , kv_ecc_privkey_read_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( kv_read_configuration )::get cannot find resource kv_ecc_privkey_read_agent_BFM" )
    if( !uvm_config_db #( kv_read_configuration )::get( null , UVMF_CONFIGURATIONS , kv_ecc_seed_read_agent_BFM , kv_ecc_seed_read_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( kv_read_configuration )::get cannot find resource kv_ecc_seed_read_agent_BFM" )

    // Assign the sequencer handles from the handles within agent configurations
    kv_rst_agent_sequencer = kv_rst_agent_config.get_sequencer();
    kv_hmac_write_agent_sequencer = kv_hmac_write_agent_config.get_sequencer();
    kv_sha512_write_agent_sequencer = kv_sha512_write_agent_config.get_sequencer();
    kv_ecc_write_agent_sequencer = kv_ecc_write_agent_config.get_sequencer();
    kv_doe_write_agent_sequencer = kv_doe_write_agent_config.get_sequencer();
    kv_hmac_key_read_agent_sequencer = kv_hmac_key_read_agent_config.get_sequencer();
    kv_hmac_block_read_agent_sequencer = kv_hmac_block_read_agent_config.get_sequencer();
    kv_sha512_block_read_agent_sequencer = kv_sha512_block_read_agent_config.get_sequencer();
    kv_ecc_privkey_read_agent_sequencer = kv_ecc_privkey_read_agent_config.get_sequencer();
    kv_ecc_seed_read_agent_sequencer = kv_ecc_seed_read_agent_config.get_sequencer();

    // Retrieve QVIP sequencer handles from the uvm_config_db
    if( !uvm_config_db #(mvc_sequencer)::get( null,UVMF_SEQUENCERS,"uvm_test_top.environment.qvip_ahb_lite_slave_subenv.ahb_lite_slave_0", uvm_test_top_environment_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_sqr) ) 
      `uvm_warning("CFG" , "uvm_config_db #( mvc_sequencer )::get cannot find resource ahb_lite_slave_0" ) 
    reg_model = top_configuration.kv_rm;


    // pragma uvmf custom new begin
    // pragma uvmf custom new end

  endfunction

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin

    // Construct sequences here

    kv_env_seq = kv_env_sequence_base_t::type_id::create("kv_env_seq");

    kv_rst_agent_random_seq     = kv_rst_agent_random_seq_t::type_id::create("kv_rst_agent_random_seq");
    kv_hmac_write_agent_random_seq     = kv_hmac_write_agent_random_seq_t::type_id::create("kv_hmac_write_agent_random_seq");
    kv_sha512_write_agent_random_seq     = kv_sha512_write_agent_random_seq_t::type_id::create("kv_sha512_write_agent_random_seq");
    kv_ecc_write_agent_random_seq     = kv_ecc_write_agent_random_seq_t::type_id::create("kv_ecc_write_agent_random_seq");
    kv_doe_write_agent_random_seq     = kv_doe_write_agent_random_seq_t::type_id::create("kv_doe_write_agent_random_seq");
    kv_hmac_key_read_agent_random_seq     = kv_hmac_key_read_agent_random_seq_t::type_id::create("kv_hmac_key_read_agent_random_seq");
    kv_hmac_block_read_agent_random_seq     = kv_hmac_block_read_agent_random_seq_t::type_id::create("kv_hmac_block_read_agent_random_seq");
    kv_sha512_block_read_agent_random_seq     = kv_sha512_block_read_agent_random_seq_t::type_id::create("kv_sha512_block_read_agent_random_seq");
    kv_ecc_privkey_read_agent_random_seq     = kv_ecc_privkey_read_agent_random_seq_t::type_id::create("kv_ecc_privkey_read_agent_random_seq");
    kv_ecc_seed_read_agent_random_seq     = kv_ecc_seed_read_agent_random_seq_t::type_id::create("kv_ecc_seed_read_agent_random_seq");

    fork
      kv_rst_agent_config.wait_for_reset();
      kv_hmac_write_agent_config.wait_for_reset();
      kv_sha512_write_agent_config.wait_for_reset();
      kv_ecc_write_agent_config.wait_for_reset();
      kv_doe_write_agent_config.wait_for_reset();
      kv_hmac_key_read_agent_config.wait_for_reset();
      kv_hmac_block_read_agent_config.wait_for_reset();
      kv_sha512_block_read_agent_config.wait_for_reset();
      kv_ecc_privkey_read_agent_config.wait_for_reset();
      kv_ecc_seed_read_agent_config.wait_for_reset();
    join
    reg_model.reset();
    // Start RESPONDER sequences here
    fork
    join_none
    // Start INITIATOR sequences here
    fork
      repeat (25) kv_rst_agent_random_seq.start(kv_rst_agent_sequencer);
      repeat (25) kv_hmac_write_agent_random_seq.start(kv_hmac_write_agent_sequencer);
      repeat (25) kv_sha512_write_agent_random_seq.start(kv_sha512_write_agent_sequencer);
      repeat (25) kv_ecc_write_agent_random_seq.start(kv_ecc_write_agent_sequencer);
      repeat (25) kv_doe_write_agent_random_seq.start(kv_doe_write_agent_sequencer);
      repeat (25) kv_hmac_key_read_agent_random_seq.start(kv_hmac_key_read_agent_sequencer);
      repeat (25) kv_hmac_block_read_agent_random_seq.start(kv_hmac_block_read_agent_sequencer);
      repeat (25) kv_sha512_block_read_agent_random_seq.start(kv_sha512_block_read_agent_sequencer);
      repeat (25) kv_ecc_privkey_read_agent_random_seq.start(kv_ecc_privkey_read_agent_sequencer);
      repeat (25) kv_ecc_seed_read_agent_random_seq.start(kv_ecc_seed_read_agent_sequencer);
    join

kv_env_seq.start(top_configuration.vsqr);

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      kv_rst_agent_config.wait_for_num_clocks(400);
      kv_hmac_write_agent_config.wait_for_num_clocks(400);
      kv_sha512_write_agent_config.wait_for_num_clocks(400);
      kv_ecc_write_agent_config.wait_for_num_clocks(400);
      kv_doe_write_agent_config.wait_for_num_clocks(400);
      kv_hmac_key_read_agent_config.wait_for_num_clocks(400);
      kv_hmac_block_read_agent_config.wait_for_num_clocks(400);
      kv_sha512_block_read_agent_config.wait_for_num_clocks(400);
      kv_ecc_privkey_read_agent_config.wait_for_num_clocks(400);
      kv_ecc_seed_read_agent_config.wait_for_num_clocks(400);
    join

    // pragma uvmf custom body end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

