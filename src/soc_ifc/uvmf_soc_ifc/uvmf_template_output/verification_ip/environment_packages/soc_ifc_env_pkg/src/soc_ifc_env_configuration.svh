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
// DESCRIPTION: THis is the configuration for the soc_ifc environment.
//  it contains configuration classes for each agent.  It also contains
//  environment level configuration variables.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_configuration 
extends uvmf_environment_configuration_base;

  `uvm_object_utils( soc_ifc_env_configuration )


//Constraints for the configuration variables:

// Instantiate the register model
  soc_ifc_reg_model_top  soc_ifc_rm;

  covergroup soc_ifc_configuration_cg;
    // pragma uvmf custom covergroup begin
    option.auto_bin_max=1024;
    // pragma uvmf custom covergroup end
  endgroup


    typedef soc_ifc_ctrl_configuration soc_ifc_ctrl_agent_config_t;
    rand soc_ifc_ctrl_agent_config_t soc_ifc_ctrl_agent_config;

    typedef cptra_ctrl_configuration cptra_ctrl_agent_config_t;
    rand cptra_ctrl_agent_config_t cptra_ctrl_agent_config;

    typedef soc_ifc_status_configuration soc_ifc_status_agent_config_t;
    rand soc_ifc_status_agent_config_t soc_ifc_status_agent_config;

    typedef cptra_status_configuration cptra_status_agent_config_t;
    rand cptra_status_agent_config_t cptra_status_agent_config;



    qvip_ahb_lite_slave_env_configuration     qvip_ahb_lite_slave_subenv_config;
    string                                   qvip_ahb_lite_slave_subenv_interface_names[];
    uvmf_active_passive_t                    qvip_ahb_lite_slave_subenv_interface_activity[];
    qvip_apb5_slave_env_configuration     qvip_apb5_slave_subenv_config;
    string                                   qvip_apb5_slave_subenv_interface_names[];
    uvmf_active_passive_t                    qvip_apb5_slave_subenv_interface_activity[];

  typedef uvmf_virtual_sequencer_base #(.CONFIG_T(soc_ifc_env_configuration)) soc_ifc_vsqr_t;
  soc_ifc_vsqr_t vsqr;

  // pragma uvmf custom class_item_additional begin
   typedef apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT,
                                        apb5_master_0_params::APB3_PADDR_BIT_WIDTH,
                                        apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,
                                        apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_reg_transfer_t;

  // pragma uvmf custom class_item_additional end

// ****************************************************************************
// FUNCTION : new()
// This function is the standard SystemVerilog constructor.
// This function constructs the configuration object for each agent in the environment.
//
  function new( string name = "" );
    super.new( name );


    soc_ifc_ctrl_agent_config = soc_ifc_ctrl_agent_config_t::type_id::create("soc_ifc_ctrl_agent_config");
    cptra_ctrl_agent_config = cptra_ctrl_agent_config_t::type_id::create("cptra_ctrl_agent_config");
    soc_ifc_status_agent_config = soc_ifc_status_agent_config_t::type_id::create("soc_ifc_status_agent_config");
    cptra_status_agent_config = cptra_status_agent_config_t::type_id::create("cptra_status_agent_config");

    qvip_ahb_lite_slave_subenv_config = qvip_ahb_lite_slave_env_configuration::type_id::create("qvip_ahb_lite_slave_subenv_config");
    qvip_apb5_slave_subenv_config = qvip_apb5_slave_env_configuration::type_id::create("qvip_apb5_slave_subenv_config");

    soc_ifc_configuration_cg=new;
    `uvm_info("COVERAGE_MODEL_REVIEW", "TODO!!!!!!!!! A covergroup has been constructed which may need review because of either generation or re-generation with merging.  Please note that configuration variables added as a result of re-generation and merging are not automatically added to the covergroup.  Remove this message after the covergroup has been reviewed.", UVM_NONE)

  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

// ****************************************************************************
// FUNCTION : set_vsqr()
// This function is used to assign the vsqr handle.
  virtual function void set_vsqr( soc_ifc_vsqr_t vsqr);
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
     
     "\n", soc_ifc_ctrl_agent_config.convert2string,
     "\n", cptra_ctrl_agent_config.convert2string,
     "\n", soc_ifc_status_agent_config.convert2string,
     "\n", cptra_status_agent_config.convert2string,

     "\n", qvip_ahb_lite_slave_subenv_config.convert2string,
     "\n", qvip_apb5_slave_subenv_config.convert2string
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

    qvip_apb5_slave_subenv_interface_names    = new[1];
    qvip_apb5_slave_subenv_interface_activity = new[1];

    qvip_apb5_slave_subenv_interface_names     = interface_names[1:1];
    qvip_apb5_slave_subenv_interface_activity  = interface_activity[1:1];


  // Interface initialization for local agents
     soc_ifc_ctrl_agent_config.initialize( interface_activity[2], {environment_path,".soc_ifc_ctrl_agent"}, interface_names[2]);
     soc_ifc_ctrl_agent_config.initiator_responder = INITIATOR;
     soc_ifc_ctrl_agent_config.has_coverage = 1;
     cptra_ctrl_agent_config.initialize( interface_activity[3], {environment_path,".cptra_ctrl_agent"}, interface_names[3]);
     cptra_ctrl_agent_config.initiator_responder = INITIATOR;
     cptra_ctrl_agent_config.has_coverage = 1;
     soc_ifc_status_agent_config.initialize( interface_activity[4], {environment_path,".soc_ifc_status_agent"}, interface_names[4]);
     soc_ifc_status_agent_config.initiator_responder = RESPONDER;
     soc_ifc_status_agent_config.has_coverage = 1;
     cptra_status_agent_config.initialize( interface_activity[5], {environment_path,".cptra_status_agent"}, interface_names[5]);
     cptra_status_agent_config.initiator_responder = RESPONDER;
     cptra_status_agent_config.has_coverage = 1;

    // pragma uvmf custom reg_model_config_initialize begin
    // Register model creation and configuation
    if (register_model == null) begin
      uvm_reg::include_coverage("*", UVM_CVR_ALL); // Register coverage config with resource DB, used later by build_coverage()
      soc_ifc_rm = soc_ifc_reg_model_top::type_id::create("soc_ifc_rm");
      soc_ifc_rm.build();
      soc_ifc_rm.lock_model();
      soc_ifc_rm.build_ext_maps();
      enable_reg_adaptation = 1;
      enable_reg_prediction = 1;
    end else begin
      $cast(soc_ifc_rm,register_model);
      enable_reg_prediction = 1;
    end
    // pragma uvmf custom reg_model_config_initialize end


     qvip_ahb_lite_slave_subenv_config.initialize( sim_level, {environment_path,".qvip_ahb_lite_slave_subenv"}, qvip_ahb_lite_slave_subenv_interface_names, soc_ifc_rm,   qvip_ahb_lite_slave_subenv_interface_activity);
     qvip_apb5_slave_subenv_config.initialize( sim_level, {environment_path,".qvip_apb5_slave_subenv"}, qvip_apb5_slave_subenv_interface_names, soc_ifc_rm,   qvip_apb5_slave_subenv_interface_activity);


  // pragma uvmf custom initialize begin
     qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.agent_cfg.en_cvg.slave = 1'b1;
     qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.agent_cfg.en_cvg.master = 1'b1;
     qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.agent_cfg.en_cvg.response = 1'b1;

     qvip_apb5_slave_subenv_config.apb5_master_0_cfg.agent_cfg.en_sb = 1'b0; /* FIXME -- apb scoreboard flags ERRORs when read_data != write_data to a given address, which happens frequently (non-erroneously) in this environment */
     qvip_apb5_slave_subenv_config.apb5_master_0_cfg.agent_cfg.en_cvg = 1'b1;
    // Add analysis ports to send Bus traffic to the scoreboard, so that the predictor/scoreboard can check read transfer data
    void'(qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.set_monitor_item( "burst_transfer_sb" , ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                                                                                                                                     ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                                                                                                                                     ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                                                                                                                                     ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                                                                                                                                     ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                                                                                                                                     ahb_lite_slave_0_params::AHB_RDATA_WIDTH)::type_id::get() ));
    void'(qvip_apb5_slave_subenv_config.apb5_master_0_cfg.set_monitor_item( "trans_ap_sb" , apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT,
                                                                                                                         apb5_master_0_params::APB3_PADDR_BIT_WIDTH,
                                                                                                                         apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,
                                                                                                                         apb5_master_0_params::APB3_PRDATA_BIT_WIDTH)::type_id::get() ));
    // Add analysis ports to send Bus traffic to the coverage subscriber
    void'(qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.set_monitor_item( "burst_transfer_cov" , ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                                                                                                                                      ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                                                                                                                                      ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                                                                                                                                      ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                                                                                                                                      ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                                                                                                                                      ahb_lite_slave_0_params::AHB_RDATA_WIDTH)::type_id::get() ));
    void'(qvip_apb5_slave_subenv_config.apb5_master_0_cfg.set_monitor_item( "trans_ap_cov" , apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT,
                                                                                                                          apb5_master_0_params::APB3_PADDR_BIT_WIDTH,
                                                                                                                          apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,
                                                                                                                          apb5_master_0_params::APB3_PRDATA_BIT_WIDTH)::type_id::get() ));
  // pragma uvmf custom initialize end

  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

