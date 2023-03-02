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

class AES_bench_sequence_base extends uvmf_sequence_base #(uvm_sequence_item);

  `uvm_object_utils( AES_bench_sequence_base );

  // pragma uvmf custom sequences begin
  // UVMF_CHANGE_ME : Instantiate, construct, and start sequences as needed to create stimulus scenarios.
  // Instantiate sequences here
  typedef AES_in_random_sequence  AES_in_agent_random_seq_t;
  AES_in_agent_random_seq_t AES_in_agent_random_seq;
  // pragma uvmf custom sequences end

  // Sequencer handles for each active interface in the environment
  typedef AES_in_transaction  AES_in_agent_transaction_t;
  uvm_sequencer #(AES_in_agent_transaction_t)  AES_in_agent_sequencer; 


  // Top level environment configuration handle
  typedef AES_env_configuration  AES_env_configuration_t;
  AES_env_configuration_t top_configuration;

  // Configuration handles to access interface BFM's
  AES_in_configuration  AES_in_agent_config;
  AES_out_configuration  AES_out_agent_config;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  // ****************************************************************************
  function new( string name = "" );
    super.new( name );
    // Retrieve the configuration handles from the uvm_config_db

    // Retrieve top level configuration handle
    if ( !uvm_config_db#(AES_env_configuration_t)::get(null,UVMF_CONFIGURATIONS, "TOP_ENV_CONFIG",top_configuration) ) begin
      `uvm_info("CFG", "*** FATAL *** uvm_config_db::get can not find TOP_ENV_CONFIG.  Are you using an older UVMF release than what was used to generate this bench?",UVM_NONE);
      `uvm_fatal("CFG", "uvm_config_db#(AES_env_configuration_t)::get cannot find resource TOP_ENV_CONFIG");
    end

    // Retrieve config handles for all agents
    if( !uvm_config_db #( AES_in_configuration )::get( null , UVMF_CONFIGURATIONS , AES_in_agent_BFM , AES_in_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( AES_in_configuration )::get cannot find resource AES_in_agent_BFM" )
    if( !uvm_config_db #( AES_out_configuration )::get( null , UVMF_CONFIGURATIONS , AES_out_agent_BFM , AES_out_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( AES_out_configuration )::get cannot find resource AES_out_agent_BFM" )

    // Assign the sequencer handles from the handles within agent configurations
    AES_in_agent_sequencer = AES_in_agent_config.get_sequencer();



    // pragma uvmf custom new begin
    // pragma uvmf custom new end

  endfunction

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin

    // Construct sequences here
    AES_in_agent_random_seq     = AES_in_agent_random_seq_t::type_id::create("AES_in_agent_random_seq");
    fork
      AES_in_agent_config.wait_for_reset();
      AES_out_agent_config.wait_for_reset();
    join
    // Start RESPONDER sequences here
    fork
    join_none
    // Start INITIATOR sequences here
    fork
      repeat (25) AES_in_agent_random_seq.start(AES_in_agent_sequencer);
    join
    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      AES_in_agent_config.wait_for_num_clocks(400);
      AES_out_agent_config.wait_for_num_clocks(400);
    join

    // pragma uvmf custom body end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

