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
// DESCRIPTION: THis is the configuration for the hmac256 environment.
//  it contains configuration classes for each agent.  It also contains
//  environment level configuration variables.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class HMAC256_env_configuration 
extends uvmf_environment_configuration_base;

  `uvm_object_utils( HMAC256_env_configuration )


//Constraints for the configuration variables:

// Instantiate the register model
  hmac256_reg_model_top  hmac256_rm;

  covergroup hmac256_configuration_cg;
    // pragma uvmf custom covergroup begin
    option.auto_bin_max=1024;
    // pragma uvmf custom covergroup end
  endgroup


    typedef HMAC256_rst_configuration hmac256_rst_agent_config_t;
    rand hmac256_rst_agent_config_t hmac256_rst_agent_config;



    qvip_ahb_lite_slave_env_configuration     qvip_ahb_lite_slave_subenv_config;
    string                                   qvip_ahb_lite_slave_subenv_interface_names[];
    uvmf_active_passive_t                    qvip_ahb_lite_slave_subenv_interface_activity[];

  typedef uvmf_virtual_sequencer_base #(.CONFIG_T(HMAC256_env_configuration)) hmac256_vsqr_t;
  hmac256_vsqr_t vsqr;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

// ****************************************************************************
// FUNCTION : new()
// This function is the standard SystemVerilog constructor.
// This function constructs the configuration object for each agent in the environment.
//
  function new( string name = "" );
    super.new( name );


    hmac256_rst_agent_config = hmac256_rst_agent_config_t::type_id::create("hmac256_rst_agent_config");

    qvip_ahb_lite_slave_subenv_config = qvip_ahb_lite_slave_env_configuration::type_id::create("qvip_ahb_lite_slave_subenv_config");

    hmac256_configuration_cg=new;
    `uvm_warning("COVERAGE_MODEL_REVIEW", "A covergroup has been constructed which may need review because of either generation or re-generation with merging.  Please note that configuration variables added as a result of re-generation and merging are not automatically added to the covergroup.  Remove this warning after the covergroup has been reviewed.")

  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

// ****************************************************************************
// FUNCTION : set_vsqr()
// This function is used to assign the vsqr handle.
  virtual function void set_vsqr( hmac256_vsqr_t vsqr);
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
     
     "\n", hmac256_rst_agent_config.convert2string,

     "\n", qvip_ahb_lite_slave_subenv_config.convert2string
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


  // Interface initialization for QVIP sub-environments
    qvip_ahb_lite_slave_subenv_interface_names    = new[1];
    qvip_ahb_lite_slave_subenv_interface_activity = new[1];

    qvip_ahb_lite_slave_subenv_interface_names     = interface_names[0:0];
    qvip_ahb_lite_slave_subenv_interface_activity  = interface_activity[0:0];


  // Interface initialization for local agents
     hmac256_rst_agent_config.initialize( interface_activity[1], {environment_path,".HMAC256_rst_agent"}, interface_names[1]);
     hmac256_rst_agent_config.initiator_responder = INITIATOR;
     // hmac256_rst_agent_config.has_coverage = 1;

    // pragma uvmf custom reg_model_config_initialize begin
    // Register model creation and configuation
    if (register_model == null) begin
      hmac256_rm = hmac256_reg_model_top::type_id::create("hmac256_rm");
      hmac256_rm.build();
      hmac256_rm.lock_model();
      enable_reg_adaptation = 1;
      enable_reg_prediction = 1;
    end else begin
      $cast(hmac256_rm,register_model);
      enable_reg_prediction = 1;
    end
    // pragma uvmf custom reg_model_config_initialize end


     qvip_ahb_lite_slave_subenv_config.initialize( sim_level, {environment_path,".qvip_ahb_lite_slave_subenv"}, qvip_ahb_lite_slave_subenv_interface_names, null,   qvip_ahb_lite_slave_subenv_interface_activity);


  // pragma uvmf custom initialize begin
  // pragma uvmf custom initialize end

  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

