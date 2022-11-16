//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: THis is the configuration for the ECC environment.
//  it contains configuration classes for each agent.  It also contains
//  environment level configuration variables.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class ECC_env_configuration 
extends uvmf_environment_configuration_base;

  `uvm_object_utils( ECC_env_configuration )


//Constraints for the configuration variables:


  covergroup ECC_configuration_cg;
    // pragma uvmf custom covergroup begin
    option.auto_bin_max=1024;
    // pragma uvmf custom covergroup end
  endgroup


    typedef ECC_in_configuration ECC_in_agent_config_t;
    rand ECC_in_agent_config_t ECC_in_agent_config;

    typedef ECC_out_configuration ECC_out_agent_config_t;
    rand ECC_out_agent_config_t ECC_out_agent_config;




  typedef uvmf_virtual_sequencer_base #(.CONFIG_T(ECC_env_configuration)) ECC_vsqr_t;
  ECC_vsqr_t vsqr;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

// ****************************************************************************
// FUNCTION : new()
// This function is the standard SystemVerilog constructor.
// This function constructs the configuration object for each agent in the environment.
//
  function new( string name = "" );
    super.new( name );


    ECC_in_agent_config = ECC_in_agent_config_t::type_id::create("ECC_in_agent_config");
    ECC_out_agent_config = ECC_out_agent_config_t::type_id::create("ECC_out_agent_config");


    ECC_configuration_cg=new;
    `uvm_info("COVERAGE_MODEL_REVIEW", "A covergroup has been constructed which may need review because of either generation or re-generation with merging.  Please note that configuration variables added as a result of re-generation and merging are not automatically added to the covergroup.  Remove this message after the covergroup has been reviewed. Demoted to UVM_INFO to allow sim_log_parse to pass", UVM_NONE)

  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

// ****************************************************************************
// FUNCTION : set_vsqr()
// This function is used to assign the vsqr handle.
  virtual function void set_vsqr( ECC_vsqr_t vsqr);
     this.vsqr = vsqr;
  endfunction : set_vsqr

// ****************************************************************************
// FUNCTION: post_randomize()
// This function is automatically called after the randomize() function 
// is executed.
//
  function void post_randomize();
    super.post_randomize();
    // pragma uvmf custom post_randomize begin
    // pragma uvmf custom post_randomize end
  endfunction
  
// ****************************************************************************
// FUNCTION: convert2string()
// This function converts all variables in this class to a single string for
// logfile reporting. This function concatenates the convert2string result for
// each agent configuration in this configuration class.
//
  virtual function string convert2string();
    // pragma uvmf custom convert2string begin
    return {
     
     "\n", ECC_in_agent_config.convert2string,
     "\n", ECC_out_agent_config.convert2string


       };
    // pragma uvmf custom convert2string end
  endfunction
// ****************************************************************************
// FUNCTION: initialize();
// This function configures each interface agents configuration class.  The 
// sim level determines the active/passive state of the agent.  The environment_path
// identifies the hierarchy down to and including the instantiation name of the
// environment for this configuration class.  Each instance of the environment 
// has its own configuration class.  The string interface names are used by 
// the agent configurations to identify the virtual interface handle to pull from
// the uvm_config_db.  
//
  function void initialize(uvmf_sim_level_t sim_level, 
                                      string environment_path,
                                      string interface_names[],
                                      uvm_reg_block register_model = null,
                                      uvmf_active_passive_t interface_activity[] = {}
                                     );

    super.initialize(sim_level, environment_path, interface_names, register_model, interface_activity);



  // Interface initialization for local agents
     ECC_in_agent_config.initialize( interface_activity[0], {environment_path,".ECC_in_agent"}, interface_names[0]);
     ECC_in_agent_config.initiator_responder = INITIATOR;
     // ECC_in_agent_config.has_coverage = 1;
     ECC_out_agent_config.initialize( interface_activity[1], {environment_path,".ECC_out_agent"}, interface_names[1]);
     ECC_out_agent_config.initiator_responder = RESPONDER;
     // ECC_out_agent_config.has_coverage = 1;





  // pragma uvmf custom initialize begin
  // pragma uvmf custom initialize end

  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

