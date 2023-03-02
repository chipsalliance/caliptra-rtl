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

class AES_environment  extends uvmf_environment_base #(
    .CONFIG_T( AES_env_configuration 
  ));
  `uvm_component_utils( AES_environment )





  typedef AES_in_agent  AES_in_agent_t;
  AES_in_agent_t AES_in_agent;

  typedef AES_out_agent  AES_out_agent_t;
  AES_out_agent_t AES_out_agent;




  typedef AES_predictor #(
                .CONFIG_T(CONFIG_T)
                )
 AES_pred_t;
  AES_pred_t AES_pred;

  typedef uvmf_in_order_scoreboard #(.T(AES_out_transaction))  AES_sb_t;
  AES_sb_t AES_sb;


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
    AES_in_agent = AES_in_agent_t::type_id::create("AES_in_agent",this);
    AES_in_agent.set_config(configuration.AES_in_agent_config);
    AES_out_agent = AES_out_agent_t::type_id::create("AES_out_agent",this);
    AES_out_agent.set_config(configuration.AES_out_agent_config);
    AES_pred = AES_pred_t::type_id::create("AES_pred",this);
    AES_pred.configuration = configuration;
    AES_sb = AES_sb_t::type_id::create("AES_sb",this);
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
    AES_in_agent.monitored_ap.connect(AES_pred.AES_in_agent_ae);
    AES_pred.AES_sb_ap.connect(AES_sb.expected_analysis_export);
    AES_out_agent.monitored_ap.connect(AES_sb.actual_analysis_export);
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
     configuration.AES_configuration_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

