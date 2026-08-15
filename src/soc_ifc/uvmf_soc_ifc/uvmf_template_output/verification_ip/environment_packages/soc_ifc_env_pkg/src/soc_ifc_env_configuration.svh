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

    typedef ss_mode_ctrl_configuration ss_mode_ctrl_agent_config_t;
    rand ss_mode_ctrl_agent_config_t ss_mode_ctrl_agent_config;

    typedef soc_ifc_status_configuration soc_ifc_status_agent_config_t;
    rand soc_ifc_status_agent_config_t soc_ifc_status_agent_config;

    typedef cptra_status_configuration cptra_status_agent_config_t;
    rand cptra_status_agent_config_t cptra_status_agent_config;

    typedef ss_mode_status_configuration ss_mode_status_agent_config_t;
    rand ss_mode_status_agent_config_t ss_mode_status_agent_config;

    typedef mbox_sram_configuration mbox_sram_agent_config_t;
    rand mbox_sram_agent_config_t mbox_sram_agent_config;

    qvip_ahb_lite_slave_env_configuration     qvip_ahb_lite_slave_subenv_config;
    string                                   qvip_ahb_lite_slave_subenv_interface_names[];
    uvmf_active_passive_t                    qvip_ahb_lite_slave_subenv_interface_activity[];

  // UVMF launch bridge only. The environment factory-creates and owns this
  // component; configuration merely mirrors the same class handle because
  // generated soc_ifc_bench_sequence_base starts its environment sequence with
  // top_configuration.vsqr. Custom sequences use their active m_sequencer.
  soc_ifc_virtual_sequencer vsqr;

  // pragma uvmf custom class_item_additional begin
  // -------------------------------------------------------------------------
  // Global environment facts shared by every sequence and component:
  //   * subsystem_mode      - compile-time integration mode, initialized when
  //                           this configuration object is created.
  //   * ss_dma_axi_user     - effective (post-fuse) SoC DMA AxUSER identity, i.e.
  //                           the authorized SoC-AXI SHA/DMA requester.
  //   * global_straps_captured - valid only for the current boot; cleared on
  //                           cold reset and set after fuse download recaptures
  //                           the runtime straps.
  // -------------------------------------------------------------------------
  bit        subsystem_mode;
  bit [31:0] ss_dma_axi_user;
  bit        global_straps_captured;
  // SHA boot-lock release is opt-in and is requested only by tests that need
  // legal subsystem-mode SHA traffic.
  bit enable_sha_iccm_unlock;
  virtual soc_ifc_sha_status_if sha_status_vif;

  // Runtime components remain environment-owned; only policies live here.
  soc_ifc_axi_sram_config axi_sram_config;
  soc_ifc_recovery_fifo_config recovery_fifo_config;
  aaxi_addr_t axi_soc_ifc_base_addr;
  aaxi_addr_t axi_soc_ifc_limit_addr;
  int unsigned axi_outstanding_depth;
  bit axi_endpoints_configured;

  // Parse one fixed delay or a complete minimum/maximum pair.
  virtual function void parse_response_delay(input string prefix, input int unsigned default_min, input int unsigned default_max,
                                             output int unsigned delay_min, output int unsigned delay_max);
    int unsigned fixed_delay;
    bit has_fixed_delay;
    bit has_min_delay;
    bit has_max_delay;
    string fixed_arg;
    string min_arg;
    string max_arg;

    delay_min = default_min;
    delay_max = default_max;
    fixed_arg = {prefix, "=%d"};
    min_arg = {prefix, "_MIN=%d"};
    max_arg = {prefix, "_MAX=%d"};
    has_fixed_delay = $value$plusargs(fixed_arg, fixed_delay);
    has_min_delay = $value$plusargs(min_arg, delay_min);
    has_max_delay = $value$plusargs(max_arg, delay_max);
    if (has_fixed_delay && (has_min_delay || has_max_delay))
      `uvm_fatal("AXI_FABRIC_CFG", $sformatf("%s cannot be combined with %s_MIN or %s_MAX", prefix, prefix, prefix))
    if (has_min_delay != has_max_delay)
      `uvm_fatal("AXI_FABRIC_CFG", $sformatf("%s_MIN and %s_MAX must be specified together", prefix, prefix))
    if (has_fixed_delay) begin
      delay_min = fixed_delay;
      delay_max = fixed_delay;
    end
    if (delay_min > delay_max)
      `uvm_fatal("AXI_FABRIC_CFG", $sformatf("%s minimum %0d exceeds maximum %0d", prefix, delay_min, delay_max))
  endfunction

  // Configure the SRAM and recovery endpoint policies.
  virtual function void configure_axi_endpoints(
      input aaxi_addr_t soc_ifc_base_addr,
      input aaxi_addr_t soc_ifc_limit_addr,
      input aaxi_addr_t sram_base_addr,
      input longint unsigned sram_size_bytes,
      input int unsigned sram_word_bytes,
      input aaxi_addr_t recovery_fifo_addr,
      input int unsigned recovery_fifo_depth_dwords_default,
      input int unsigned outstanding_depth,
      input int unsigned sram_b_delay_min_default,
      input int unsigned sram_b_delay_max_default,
      input int unsigned sram_r_delay_min_default,
      input int unsigned sram_r_delay_max_default,
      input int unsigned recovery_r_delay_min_default,
      input int unsigned recovery_r_delay_max_default,
      input int unsigned recovery_refill_delay_min_default,
      input int unsigned recovery_refill_delay_max_default);
    virtual soc_ifc_recovery_if recovery_vif;
    int unsigned sram_b_delay_min;
    int unsigned sram_b_delay_max;
    int unsigned sram_r_delay_min;
    int unsigned sram_r_delay_max;
    int unsigned recovery_r_delay_min;
    int unsigned recovery_r_delay_max;
    int unsigned recovery_refill_delay_min;
    int unsigned recovery_refill_delay_max;
    int unsigned recovery_fifo_depth_dwords;

    axi_soc_ifc_base_addr = soc_ifc_base_addr;
    axi_soc_ifc_limit_addr = soc_ifc_limit_addr;
    axi_outstanding_depth = outstanding_depth;

    parse_response_delay("AXI_SRAM_B_DELAY", sram_b_delay_min_default, sram_b_delay_max_default, sram_b_delay_min, sram_b_delay_max);
    parse_response_delay("AXI_SRAM_R_DELAY", sram_r_delay_min_default, sram_r_delay_max_default, sram_r_delay_min, sram_r_delay_max);
    parse_response_delay("AXI_RECOVERY_R_DELAY", recovery_r_delay_min_default, recovery_r_delay_max_default,
                         recovery_r_delay_min, recovery_r_delay_max);
    parse_response_delay("AXI_RECOVERY_FIFO_REFILL_DELAY", recovery_refill_delay_min_default, recovery_refill_delay_max_default,
                         recovery_refill_delay_min, recovery_refill_delay_max);
    recovery_fifo_depth_dwords = recovery_fifo_depth_dwords_default;
    void'($value$plusargs("AXI_RECOVERY_FIFO_DEPTH_DWORDS=%d", recovery_fifo_depth_dwords));

    axi_sram_config.configure(sram_base_addr, sram_base_addr + sram_size_bytes - 1, sram_word_bytes,
                              sram_b_delay_min, sram_b_delay_max, sram_r_delay_min, sram_r_delay_max);

    if (!uvm_config_db #(virtual soc_ifc_recovery_if)::get(null, UVMF_VIRTUAL_INTERFACES, SOC_IFC_RECOVERY_VIF, recovery_vif))
      `uvm_fatal("RECOVERY_FIFO_CFG", "Unable to retrieve recovery FIFO virtual interface")
    recovery_fifo_config.configure(recovery_vif, recovery_fifo_addr, recovery_fifo_depth_dwords, recovery_r_delay_min,
                                   recovery_r_delay_max, recovery_refill_delay_min, recovery_refill_delay_max);
    axi_endpoints_configured = 1'b1;

    `uvm_info("SOC_IFC_CFG", $sformatf("Configured AXI SRAM [0x%0h:0x%0h] and recovery FIFO 0x%0h depth %0d DWORDs",
              axi_sram_config.base_addr, axi_sram_config.limit_addr, recovery_fifo_config.fifo_data_addr,
              recovery_fifo_config.depth_dwords), UVM_LOW)
  endfunction
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
    ss_mode_ctrl_agent_config = ss_mode_ctrl_agent_config_t::type_id::create("ss_mode_ctrl_agent_config");
    soc_ifc_status_agent_config = soc_ifc_status_agent_config_t::type_id::create("soc_ifc_status_agent_config");
    cptra_status_agent_config = cptra_status_agent_config_t::type_id::create("cptra_status_agent_config");
    ss_mode_status_agent_config = ss_mode_status_agent_config_t::type_id::create("ss_mode_status_agent_config");
    mbox_sram_agent_config = mbox_sram_agent_config_t::type_id::create("mbox_sram_agent_config");

    qvip_ahb_lite_slave_subenv_config = qvip_ahb_lite_slave_env_configuration::type_id::create("qvip_ahb_lite_slave_subenv_config");
    axi_sram_config = soc_ifc_axi_sram_config::type_id::create("axi_sram_config");
    recovery_fifo_config = soc_ifc_recovery_fifo_config::type_id::create("recovery_fifo_config");

    soc_ifc_configuration_cg=new;
    `uvm_info("COVERAGE_MODEL_REVIEW", "TODO!!!!!!!!! A covergroup has been constructed which may need review because of either generation or re-generation with merging.  Please note that configuration variables added as a result of re-generation and merging are not automatically added to the covergroup.  Remove this message after the covergroup has been reviewed.", UVM_NONE)

  // pragma uvmf custom new begin
    subsystem_mode = CALIPTRA_SS_MODE_C;
    axi_endpoints_configured = 1'b0;
    enable_sha_iccm_unlock =
        subsystem_mode && $test$plusargs("ENABLE_SHA_ICCM_UNLOCK");
  // pragma uvmf custom new end
  endfunction

// ****************************************************************************
// FUNCTION : set_vsqr()
// This function is used to assign the vsqr handle.
  virtual function void set_vsqr(soc_ifc_virtual_sequencer vsqr);
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
     $sformatf("\nsubsystem_mode=%0b ss_dma_axi_user=0x%08x global_straps_captured=%0b enable_sha_iccm_unlock=%0b sha_status_vif_configured=%0b",
               subsystem_mode, ss_dma_axi_user, global_straps_captured,
               enable_sha_iccm_unlock, (sha_status_vif != null)),
     $sformatf("\naxi_soc_ifc_window=[0x%0h:0x%0h]", axi_soc_ifc_base_addr, axi_soc_ifc_limit_addr),
     "\n", soc_ifc_ctrl_agent_config.convert2string,
     "\n", cptra_ctrl_agent_config.convert2string,
     "\n", ss_mode_ctrl_agent_config.convert2string,
     "\n", soc_ifc_status_agent_config.convert2string,
     "\n", cptra_status_agent_config.convert2string,
     "\n", ss_mode_status_agent_config.convert2string,
     "\n", mbox_sram_agent_config.convert2string,

     "\n", qvip_ahb_lite_slave_subenv_config.convert2string
     //FIXME AXI sprint() call
//     "\n", qvip_apb5_slave_subenv_config.convert2string
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
     soc_ifc_ctrl_agent_config.initialize( interface_activity[1], {environment_path,".soc_ifc_ctrl_agent"}, interface_names[1]);
     soc_ifc_ctrl_agent_config.initiator_responder = INITIATOR;
     soc_ifc_ctrl_agent_config.has_coverage = 1;
     cptra_ctrl_agent_config.initialize( interface_activity[2], {environment_path,".cptra_ctrl_agent"}, interface_names[2]);
     cptra_ctrl_agent_config.initiator_responder = INITIATOR;
     cptra_ctrl_agent_config.has_coverage = 1;
     ss_mode_ctrl_agent_config.initialize( interface_activity[3], {environment_path,".ss_mode_ctrl_agent"}, interface_names[3]);
     ss_mode_ctrl_agent_config.initiator_responder = INITIATOR;
     ss_mode_ctrl_agent_config.has_coverage = 1;
     soc_ifc_status_agent_config.initialize( interface_activity[4], {environment_path,".soc_ifc_status_agent"}, interface_names[4]);
     soc_ifc_status_agent_config.initiator_responder = RESPONDER;
     soc_ifc_status_agent_config.has_coverage = 1;
     cptra_status_agent_config.initialize( interface_activity[5], {environment_path,".cptra_status_agent"}, interface_names[5]);
     cptra_status_agent_config.initiator_responder = RESPONDER;
     cptra_status_agent_config.has_coverage = 1;
     ss_mode_status_agent_config.initialize( interface_activity[6], {environment_path,".ss_mode_status_agent"}, interface_names[6]);
     ss_mode_status_agent_config.initiator_responder = RESPONDER;
     ss_mode_status_agent_config.has_coverage = 1;
     mbox_sram_agent_config.initialize( interface_activity[7], {environment_path,".mbox_sram_agent"}, interface_names[7]);
     mbox_sram_agent_config.initiator_responder = RESPONDER;
     mbox_sram_agent_config.has_coverage = 1;

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


  // pragma uvmf custom initialize begin
     // Retry in the unlock task if time-zero initialization ordering means the
     // interface has not reached the config DB yet.
     void'(uvm_config_db #(virtual soc_ifc_sha_status_if)::get(
         null, UVMF_VIRTUAL_INTERFACES, SOC_IFC_SHA_STATUS_VIF,
         sha_status_vif));

     qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.agent_cfg.en_cvg.slave = 1'b1;
     qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.agent_cfg.en_cvg.master = 1'b1;
     qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.agent_cfg.en_cvg.response = 1'b1;

     // TODO Avery AXI enable coverage?
    // Add analysis ports to send Bus traffic to the scoreboard, so that the predictor/scoreboard can check read transfer data
    void'(qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.set_monitor_item( "burst_transfer_sb" , ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                                                                                                                                     ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                                                                                                                                     ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                                                                                                                                     ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                                                                                                                                     ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                                                                                                                                     ahb_lite_slave_0_params::AHB_RDATA_WIDTH)::type_id::get() ));
    // Add analysis ports to send Bus traffic to the coverage subscriber
    void'(qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.set_monitor_item( "burst_transfer_cov" , ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                                                                                                                                      ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                                                                                                                                      ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                                                                                                                                      ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                                                                                                                                      ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                                                                                                                                      ahb_lite_slave_0_params::AHB_RDATA_WIDTH)::type_id::get() ));
  // pragma uvmf custom initialize end

  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
