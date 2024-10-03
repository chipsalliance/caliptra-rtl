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
// DESCRIPTION: THis is the configuration for the fuse_ctrl environment.
//  it contains configuration classes for each agent.  It also contains
//  environment level configuration variables.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class fuse_ctrl_env_configuration 
extends uvmf_environment_configuration_base;

  `uvm_object_utils( fuse_ctrl_env_configuration )


//Constraints for the configuration variables:


  covergroup fuse_ctrl_configuration_cg;
    // pragma uvmf custom covergroup begin
    option.auto_bin_max=1024;
    // pragma uvmf custom covergroup end
  endgroup


    typedef fuse_ctrl_rst_in_configuration fuse_ctrl_rst_in_agent_config_t;
    rand fuse_ctrl_rst_in_agent_config_t fuse_ctrl_rst_in_agent_config;

    typedef fuse_ctrl_rst_out_configuration fuse_ctrl_rst_out_agent_config_t;
    rand fuse_ctrl_rst_out_agent_config_t fuse_ctrl_rst_out_agent_config;

    typedef fuse_ctrl_core_axi_write_in_configuration fuse_ctrl_core_axi_write_in_if_agent_config_t;
    rand fuse_ctrl_core_axi_write_in_if_agent_config_t fuse_ctrl_core_axi_write_in_if_agent_config;

    typedef fuse_ctrl_core_axi_write_out_configuration fuse_ctrl_core_axi_write_out_if_agent_config_t;
    rand fuse_ctrl_core_axi_write_out_if_agent_config_t fuse_ctrl_core_axi_write_out_if_agent_config;

    typedef fuse_ctrl_prim_axi_write_in_configuration fuse_ctrl_prim_axi_write_in_if_agent_config_t;
    rand fuse_ctrl_prim_axi_write_in_if_agent_config_t fuse_ctrl_prim_axi_write_in_if_agent_config;

    typedef fuse_ctrl_prim_axi_write_out_configuration fuse_ctrl_prim_axi_write_out_if_agent_config_t;
    rand fuse_ctrl_prim_axi_write_out_if_agent_config_t fuse_ctrl_prim_axi_write_out_if_agent_config;

    typedef fuse_ctrl_core_axi_read_in_configuration fuse_ctrl_core_axi_read_in_if_agent_config_t;
    rand fuse_ctrl_core_axi_read_in_if_agent_config_t fuse_ctrl_core_axi_read_in_if_agent_config;

    typedef fuse_ctrl_core_axi_read_out_configuration fuse_ctrl_core_axi_read_out_if_agent_config_t;
    rand fuse_ctrl_core_axi_read_out_if_agent_config_t fuse_ctrl_core_axi_read_out_if_agent_config;

    typedef fuse_ctrl_prim_axi_read_in_configuration fuse_ctrl_prim_axi_read_in_if_agent_config_t;
    rand fuse_ctrl_prim_axi_read_in_if_agent_config_t fuse_ctrl_prim_axi_read_in_if_agent_config;

    typedef fuse_ctrl_prim_axi_read_out_configuration fuse_ctrl_prim_axi_read_out_if_agent_config_t;
    rand fuse_ctrl_prim_axi_read_out_if_agent_config_t fuse_ctrl_prim_axi_read_out_if_agent_config;

    typedef fuse_ctrl_secreg_axi_read_in_configuration fuse_ctrl_secreg_axi_read_in_if_agent_config_t;
    rand fuse_ctrl_secreg_axi_read_in_if_agent_config_t fuse_ctrl_secreg_axi_read_in_if_agent_config;

    typedef fuse_ctrl_secreg_axi_read_out_configuration fuse_ctrl_secreg_axi_read_out_if_agent_config_t;
    rand fuse_ctrl_secreg_axi_read_out_if_agent_config_t fuse_ctrl_secreg_axi_read_out_if_agent_config;

    typedef fuse_ctrl_lc_otp_in_configuration fuse_ctrl_lc_otp_in_if_agent_config_t;
    rand fuse_ctrl_lc_otp_in_if_agent_config_t fuse_ctrl_lc_otp_in_if_agent_config;

    typedef fuse_ctrl_lc_otp_out_configuration fuse_ctrl_lc_otp_out_if_agent_config_t;
    rand fuse_ctrl_lc_otp_out_if_agent_config_t fuse_ctrl_lc_otp_out_if_agent_config;

    typedef fuse_ctrl_in_configuration fuse_ctrl_in_if_agent_config_t;
    rand fuse_ctrl_in_if_agent_config_t fuse_ctrl_in_if_agent_config;

    typedef fuse_ctrl_out_configuration fuse_ctrl_out_if_agent_config_t;
    rand fuse_ctrl_out_if_agent_config_t fuse_ctrl_out_if_agent_config;




  typedef uvmf_virtual_sequencer_base #(.CONFIG_T(fuse_ctrl_env_configuration)) fuse_ctrl_vsqr_t;
  fuse_ctrl_vsqr_t vsqr;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

// ****************************************************************************
// FUNCTION : new()
// This function is the standard SystemVerilog constructor.
// This function constructs the configuration object for each agent in the environment.
//
  function new( string name = "" );
    super.new( name );


    fuse_ctrl_rst_in_agent_config = fuse_ctrl_rst_in_agent_config_t::type_id::create("fuse_ctrl_rst_in_agent_config");
    fuse_ctrl_rst_out_agent_config = fuse_ctrl_rst_out_agent_config_t::type_id::create("fuse_ctrl_rst_out_agent_config");
    fuse_ctrl_core_axi_write_in_if_agent_config = fuse_ctrl_core_axi_write_in_if_agent_config_t::type_id::create("fuse_ctrl_core_axi_write_in_if_agent_config");
    fuse_ctrl_core_axi_write_out_if_agent_config = fuse_ctrl_core_axi_write_out_if_agent_config_t::type_id::create("fuse_ctrl_core_axi_write_out_if_agent_config");
    fuse_ctrl_prim_axi_write_in_if_agent_config = fuse_ctrl_prim_axi_write_in_if_agent_config_t::type_id::create("fuse_ctrl_prim_axi_write_in_if_agent_config");
    fuse_ctrl_prim_axi_write_out_if_agent_config = fuse_ctrl_prim_axi_write_out_if_agent_config_t::type_id::create("fuse_ctrl_prim_axi_write_out_if_agent_config");
    fuse_ctrl_core_axi_read_in_if_agent_config = fuse_ctrl_core_axi_read_in_if_agent_config_t::type_id::create("fuse_ctrl_core_axi_read_in_if_agent_config");
    fuse_ctrl_core_axi_read_out_if_agent_config = fuse_ctrl_core_axi_read_out_if_agent_config_t::type_id::create("fuse_ctrl_core_axi_read_out_if_agent_config");
    fuse_ctrl_prim_axi_read_in_if_agent_config = fuse_ctrl_prim_axi_read_in_if_agent_config_t::type_id::create("fuse_ctrl_prim_axi_read_in_if_agent_config");
    fuse_ctrl_prim_axi_read_out_if_agent_config = fuse_ctrl_prim_axi_read_out_if_agent_config_t::type_id::create("fuse_ctrl_prim_axi_read_out_if_agent_config");
    fuse_ctrl_secreg_axi_read_in_if_agent_config = fuse_ctrl_secreg_axi_read_in_if_agent_config_t::type_id::create("fuse_ctrl_secreg_axi_read_in_if_agent_config");
    fuse_ctrl_secreg_axi_read_out_if_agent_config = fuse_ctrl_secreg_axi_read_out_if_agent_config_t::type_id::create("fuse_ctrl_secreg_axi_read_out_if_agent_config");
    fuse_ctrl_lc_otp_in_if_agent_config = fuse_ctrl_lc_otp_in_if_agent_config_t::type_id::create("fuse_ctrl_lc_otp_in_if_agent_config");
    fuse_ctrl_lc_otp_out_if_agent_config = fuse_ctrl_lc_otp_out_if_agent_config_t::type_id::create("fuse_ctrl_lc_otp_out_if_agent_config");
    fuse_ctrl_in_if_agent_config = fuse_ctrl_in_if_agent_config_t::type_id::create("fuse_ctrl_in_if_agent_config");
    fuse_ctrl_out_if_agent_config = fuse_ctrl_out_if_agent_config_t::type_id::create("fuse_ctrl_out_if_agent_config");


    fuse_ctrl_configuration_cg=new;
    `uvm_warning("COVERAGE_MODEL_REVIEW", "A covergroup has been constructed which may need review because of either generation or re-generation with merging.  Please note that configuration variables added as a result of re-generation and merging are not automatically added to the covergroup.  Remove this warning after the covergroup has been reviewed.")

  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

// ****************************************************************************
// FUNCTION : set_vsqr()
// This function is used to assign the vsqr handle.
  virtual function void set_vsqr( fuse_ctrl_vsqr_t vsqr);
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
     
     "\n", fuse_ctrl_rst_agent_config.convert2string,
     "\n", fuse_ctrl_core_axi_write_agent_config.convert2string,
     "\n", fuse_ctrl_prim_axi_write_agent_config.convert2string,
     "\n", fuse_ctrl_core_axi_read_agent_config.convert2string,
     "\n", fuse_ctrl_prim_axi_read_agent_config.convert2string,
     "\n", fuse_ctrl_secreg_axi_read_agent_config.convert2string,
     "\n", fuse_ctrl_lc_otp_if_agent_config.convert2string


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
     fuse_ctrl_rst_in_agent_config.initialize( interface_activity[0], {environment_path,".fuse_ctrl_rst_in_agent"}, interface_names[0]);
     fuse_ctrl_rst_in_agent_config.initiator_responder = INITIATOR;
     // fuse_ctrl_rst_in_agent_config.has_coverage = 1;
     fuse_ctrl_rst_out_agent_config.initialize( interface_activity[1], {environment_path,".fuse_ctrl_rst_out_agent"}, interface_names[1]);
     fuse_ctrl_rst_out_agent_config.initiator_responder = RESPONDER;
     // fuse_ctrl_rst_out_agent_config.has_coverage = 1;
     fuse_ctrl_core_axi_write_in_if_agent_config.initialize( interface_activity[2], {environment_path,".fuse_ctrl_core_axi_write_in_if_agent"}, interface_names[2]);
     fuse_ctrl_core_axi_write_in_if_agent_config.initiator_responder = INITIATOR;
     // fuse_ctrl_core_axi_write_in_if_agent_config.has_coverage = 1;
     fuse_ctrl_core_axi_write_out_if_agent_config.initialize( interface_activity[3], {environment_path,".fuse_ctrl_core_axi_write_out_if_agent"}, interface_names[3]);
     fuse_ctrl_core_axi_write_out_if_agent_config.initiator_responder = RESPONDER;
     // fuse_ctrl_core_axi_write_out_if_agent_config.has_coverage = 1;
     fuse_ctrl_prim_axi_write_in_if_agent_config.initialize( interface_activity[4], {environment_path,".fuse_ctrl_prim_axi_write_in_if_agent"}, interface_names[4]);
     fuse_ctrl_prim_axi_write_in_if_agent_config.initiator_responder = INITIATOR;
     // fuse_ctrl_prim_axi_write_in_if_agent_config.has_coverage = 1;
     fuse_ctrl_prim_axi_write_out_if_agent_config.initialize( interface_activity[5], {environment_path,".fuse_ctrl_prim_axi_write_out_if_agent"}, interface_names[5]);
     fuse_ctrl_prim_axi_write_out_if_agent_config.initiator_responder = RESPONDER;
     // fuse_ctrl_prim_axi_write_out_if_agent_config.has_coverage = 1;
     fuse_ctrl_core_axi_read_in_if_agent_config.initialize( interface_activity[6], {environment_path,".fuse_ctrl_core_axi_read_in_if_agent"}, interface_names[6]);
     fuse_ctrl_core_axi_read_in_if_agent_config.initiator_responder = INITIATOR;
     // fuse_ctrl_core_axi_read_in_if_agent_config.has_coverage = 1;
     fuse_ctrl_core_axi_read_out_if_agent_config.initialize( interface_activity[7], {environment_path,".fuse_ctrl_core_axi_read_out_if_agent"}, interface_names[7]);
     fuse_ctrl_core_axi_read_out_if_agent_config.initiator_responder = RESPONDER;
     // fuse_ctrl_core_axi_read_out_if_agent_config.has_coverage = 1;
     fuse_ctrl_prim_axi_read_in_if_agent_config.initialize( interface_activity[8], {environment_path,".fuse_ctrl_prim_axi_read_in_if_agent"}, interface_names[8]);
     fuse_ctrl_prim_axi_read_in_if_agent_config.initiator_responder = INITIATOR;
     // fuse_ctrl_prim_axi_read_in_if_agent_config.has_coverage = 1;
     fuse_ctrl_prim_axi_read_out_if_agent_config.initialize( interface_activity[9], {environment_path,".fuse_ctrl_prim_axi_read_out_if_agent"}, interface_names[9]);
     fuse_ctrl_prim_axi_read_out_if_agent_config.initiator_responder = RESPONDER;
     // fuse_ctrl_prim_axi_read_out_if_agent_config.has_coverage = 1;
     fuse_ctrl_secreg_axi_read_in_if_agent_config.initialize( interface_activity[10], {environment_path,".fuse_ctrl_secreg_axi_read_in_if_agent"}, interface_names[10]);
     fuse_ctrl_secreg_axi_read_in_if_agent_config.initiator_responder = INITIATOR;
     // fuse_ctrl_secreg_axi_read_in_if_agent_config.has_coverage = 1;
     fuse_ctrl_secreg_axi_read_out_if_agent_config.initialize( interface_activity[11], {environment_path,".fuse_ctrl_secreg_axi_read_out_if_agent"}, interface_names[11]);
     fuse_ctrl_secreg_axi_read_out_if_agent_config.initiator_responder = RESPONDER;
     // fuse_ctrl_secreg_axi_read_out_if_agent_config.has_coverage = 1;
     fuse_ctrl_lc_otp_in_if_agent_config.initialize( interface_activity[12], {environment_path,".fuse_ctrl_lc_otp_in_if_agent"}, interface_names[12]);
     fuse_ctrl_lc_otp_in_if_agent_config.initiator_responder = INITIATOR;
     // fuse_ctrl_lc_otp_in_if_agent_config.has_coverage = 1;
     fuse_ctrl_lc_otp_out_if_agent_config.initialize( interface_activity[13], {environment_path,".fuse_ctrl_lc_otp_out_if_agent"}, interface_names[13]);
     fuse_ctrl_lc_otp_out_if_agent_config.initiator_responder = RESPONDER;
     // fuse_ctrl_lc_otp_out_if_agent_config.has_coverage = 1;
     fuse_ctrl_in_if_agent_config.initialize( interface_activity[14], {environment_path,".fuse_ctrl_in_if_agent"}, interface_names[14]);
     fuse_ctrl_in_if_agent_config.initiator_responder = INITIATOR;
     // fuse_ctrl_in_if_agent_config.has_coverage = 1;
     fuse_ctrl_out_if_agent_config.initialize( interface_activity[15], {environment_path,".fuse_ctrl_out_if_agent"}, interface_names[15]);
     fuse_ctrl_out_if_agent_config.initiator_responder = RESPONDER;
     // fuse_ctrl_out_if_agent_config.has_coverage = 1;





  // pragma uvmf custom initialize begin
  // pragma uvmf custom initialize end

  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

