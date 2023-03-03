//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
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

class SHA512_bench_sequence_base extends uvmf_sequence_base #(uvm_sequence_item);

  `uvm_object_utils( SHA512_bench_sequence_base );

  // pragma uvmf custom sequences begin
  // UVMF_CHANGE_ME : Instantiate, construct, and start sequences as needed to create stimulus scenarios.
  // Instantiate sequences here
  typedef SHA512_in_random_sequence  SHA512_in_agent_random_seq_t;
  SHA512_in_agent_random_seq_t SHA512_in_agent_random_seq;
  // pragma uvmf custom sequences end

  // Sequencer handles for each active interface in the environment
  typedef SHA512_in_transaction  SHA512_in_agent_transaction_t;
  uvm_sequencer #(SHA512_in_agent_transaction_t)  SHA512_in_agent_sequencer; 


  // Top level environment configuration handle
  typedef SHA512_env_configuration  SHA512_env_configuration_t;
  SHA512_env_configuration_t top_configuration;

  // Configuration handles to access interface BFM's
  SHA512_in_configuration  SHA512_in_agent_config;
  SHA512_out_configuration  SHA512_out_agent_config;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  // ****************************************************************************
  function new( string name = "" );
    super.new( name );
    // Retrieve the configuration handles from the uvm_config_db

    // Retrieve top level configuration handle
    if ( !uvm_config_db#(SHA512_env_configuration_t)::get(null,UVMF_CONFIGURATIONS, "TOP_ENV_CONFIG",top_configuration) ) begin
      `uvm_info("CFG", "*** FATAL *** uvm_config_db::get can not find TOP_ENV_CONFIG.  Are you using an older UVMF release than what was used to generate this bench?",UVM_NONE);
      `uvm_fatal("CFG", "uvm_config_db#(SHA512_env_configuration_t)::get cannot find resource TOP_ENV_CONFIG");
    end

    // Retrieve config handles for all agents
    if( !uvm_config_db #( SHA512_in_configuration )::get( null , UVMF_CONFIGURATIONS , SHA512_in_agent_BFM , SHA512_in_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( SHA512_in_configuration )::get cannot find resource SHA512_in_agent_BFM" )
    if( !uvm_config_db #( SHA512_out_configuration )::get( null , UVMF_CONFIGURATIONS , SHA512_out_agent_BFM , SHA512_out_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( SHA512_out_configuration )::get cannot find resource SHA512_out_agent_BFM" )

    // Assign the sequencer handles from the handles within agent configurations
    SHA512_in_agent_sequencer = SHA512_in_agent_config.get_sequencer();



    // pragma uvmf custom new begin
    // pragma uvmf custom new end

  endfunction

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin

    // Construct sequences here
    SHA512_in_agent_random_seq     = SHA512_in_agent_random_seq_t::type_id::create("SHA512_in_agent_random_seq");
    fork
      SHA512_in_agent_config.wait_for_reset();
      SHA512_out_agent_config.wait_for_reset();
    join
    // Start RESPONDER sequences here
    fork
    join_none
    // Start INITIATOR sequences here
    fork
      repeat (25) SHA512_in_agent_random_seq.start(SHA512_in_agent_sequencer);
    join
    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      SHA512_in_agent_config.wait_for_num_clocks(400);
      SHA512_out_agent_config.wait_for_num_clocks(400);
    join

    // pragma uvmf custom body end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

