//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: This environment contains all agents, predictors and
// scoreboards required for the block level design.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class SHA512_environment  extends uvmf_environment_base #(
    .CONFIG_T( SHA512_env_configuration 
  ));
  `uvm_component_utils( SHA512_environment )





  typedef SHA512_in_agent  SHA512_in_agent_t;
  SHA512_in_agent_t SHA512_in_agent;

  typedef SHA512_out_agent  SHA512_out_agent_t;
  SHA512_out_agent_t SHA512_out_agent;




  typedef SHA512_predictor #(
                .CONFIG_T(CONFIG_T)
                )
 SHA512_pred_t;
  SHA512_pred_t SHA512_pred;

  typedef uvmf_in_order_scoreboard #(.T(SHA512_out_transaction))  SHA512_sb_t;
  SHA512_sb_t SHA512_sb;


  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
 
// ****************************************************************************
// FUNCTION : new()
// This function is the standard SystemVerilog constructor.
//
  function new( string name = "", uvm_component parent = null );
    super.new( name, parent );
  endfunction

// ****************************************************************************
// FUNCTION: build_phase()
// This function builds all components within this environment.
//
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    SHA512_in_agent = SHA512_in_agent_t::type_id::create("SHA512_in_agent",this);
    SHA512_in_agent.set_config(configuration.SHA512_in_agent_config);
    SHA512_out_agent = SHA512_out_agent_t::type_id::create("SHA512_out_agent",this);
    SHA512_out_agent.set_config(configuration.SHA512_out_agent_config);
    SHA512_pred = SHA512_pred_t::type_id::create("SHA512_pred",this);
    SHA512_pred.configuration = configuration;
    SHA512_sb = SHA512_sb_t::type_id::create("SHA512_sb",this);
    // pragma uvmf custom build_phase begin
    // pragma uvmf custom build_phase end
  endfunction

// ****************************************************************************
// FUNCTION: connect_phase()
// This function makes all connections within this environment.  Connections
// typically inclue agent to predictor, predictor to scoreboard and scoreboard
// to agent.
//
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    SHA512_in_agent.monitored_ap.connect(SHA512_pred.SHA512_in_agent_ae);
    SHA512_pred.SHA512_sb_ap.connect(SHA512_sb.expected_analysis_export);
    SHA512_out_agent.monitored_ap.connect(SHA512_sb.actual_analysis_export);
    // pragma uvmf custom reg_model_connect_phase begin
    // pragma uvmf custom reg_model_connect_phase end
  endfunction

// ****************************************************************************
// FUNCTION: end_of_simulation_phase()
// This function is executed just prior to executing run_phase.  This function
// was added to the environment to sample environment configuration settings
// just before the simulation exits time 0.  The configuration structure is 
// randomized in the build phase before the environment structure is constructed.
// Configuration variables can be customized after randomization in the build_phase
// of the extended test.
// If a sequence modifies values in the configuration structure then the sequence is
// responsible for sampling the covergroup in the configuration if required.
//
  virtual function void start_of_simulation_phase(uvm_phase phase);
     configuration.SHA512_configuration_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

