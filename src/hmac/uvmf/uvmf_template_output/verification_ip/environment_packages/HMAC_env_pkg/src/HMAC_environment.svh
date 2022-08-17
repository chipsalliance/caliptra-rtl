//----------------------------------------------------------------------
// Created with uvmf_gen version 2021.3
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

class HMAC_environment  extends uvmf_environment_base #(
    .CONFIG_T( HMAC_env_configuration 
  ));
  `uvm_component_utils( HMAC_environment )





  typedef HMAC_in_agent  HMAC_in_agent_agent_t;
  HMAC_in_agent_agent_t HMAC_in_agent;

  typedef HMAC_out_agent  HMAC_out_agent_agent_t;
  HMAC_out_agent_agent_t HMAC_out_agent;




  typedef HMAC_predictor #(
                .CONFIG_T(CONFIG_T)
                ) HMAC_pred_t;
  HMAC_pred_t HMAC_pred;

  typedef uvmf_in_order_scoreboard #(.T(HMAC_out_transaction))  HMAC_sb_t;
  HMAC_sb_t HMAC_sb;


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
    HMAC_in_agent = HMAC_in_agent_agent_t::type_id::create("HMAC_in_agent",this);
    HMAC_in_agent.set_config(configuration.HMAC_in_agent_config);
    HMAC_out_agent = HMAC_out_agent_agent_t::type_id::create("HMAC_out_agent",this);
    HMAC_out_agent.set_config(configuration.HMAC_out_agent_config);
    HMAC_pred = HMAC_pred_t::type_id::create("HMAC_pred",this);
    HMAC_pred.configuration = configuration;
    HMAC_sb = HMAC_sb_t::type_id::create("HMAC_sb",this);
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
    HMAC_in_agent.monitored_ap.connect(HMAC_pred.HMAC_in_agent_ae);
    HMAC_pred.HMAC_sb_ap.connect(HMAC_sb.expected_analysis_export);
    HMAC_out_agent.monitored_ap.connect(HMAC_sb.actual_analysis_export);
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
     configuration.HMAC_configuration_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

