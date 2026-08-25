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
// DESCRIPTION: This environment contains all agents, predictors and
// scoreboards required for the block level design.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

// Owns soc_ifc stimulus agents, passive checking, and AXI endpoint services.
class soc_ifc_environment  extends uvmf_environment_base #(
    .CONFIG_T( soc_ifc_env_configuration 
  ));
  `uvm_component_utils( soc_ifc_environment )


  qvip_ahb_lite_slave_environment #()  qvip_ahb_lite_slave_subenv;

  // TODO: Replace this native Avery agent with a UVMF/Avery adapter agent declared in environment YAML.
  aaxi_agent axi_soc_manager_agent;
  // TODO: Replace this native Avery agent with a UVMF/Avery adapter agent declared in environment YAML.
  aaxi_agent axi_dma_manager_agent;
  // TODO: Replace this native Avery agent with a UVMF/Avery adapter agent declared in environment YAML.
  aaxi_agent axi_soc_ifc_subordinate_agent;
  // TODO: Replace this native Avery agent with a UVMF/Avery adapter agent declared in environment YAML.
  aaxi_agent axi_sram_subordinate_agent;
  // TODO: Replace this native Avery agent with a UVMF/Avery adapter agent declared in environment YAML.
  aaxi_agent axi_recovery_fifo_subordinate_agent;
  aaxi_pkg_xactor::aaxi_intc_agent axi_interconnect_agent;

  aaxi_vip_config axi_soc_manager_config;
  aaxi_vip_config axi_dma_manager_config;
  aaxi_vip_config axi_soc_ifc_subordinate_config;
  aaxi_vip_config axi_sram_subordinate_config;
  aaxi_vip_config axi_recovery_fifo_subordinate_config;
  aaxi_pkg_xactor::aaxi_intc_config axi_interconnect_config;

  virtual aaxi_intf axi_soc_manager_vif;
  virtual aaxi_intf axi_dma_manager_vif;
  virtual aaxi_intf axi_soc_ifc_subordinate_vif;
  virtual aaxi_intf axi_sram_subordinate_vif;
  virtual aaxi_intf axi_recovery_fifo_subordinate_vif;
  virtual aaxi_interconnect_intf axi_interconnect_vif;

  soc_ifc_axi_sram_agent axi_sram_agent;
  soc_ifc_recovery_fifo_agent recovery_fifo_agent;



  uvm_analysis_port #( mvc_sequence_item_base ) qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap [string];

  typedef soc_ifc_ctrl_agent  soc_ifc_ctrl_agent_t;
  soc_ifc_ctrl_agent_t soc_ifc_ctrl_agent;

  typedef cptra_ctrl_agent  cptra_ctrl_agent_t;
  cptra_ctrl_agent_t cptra_ctrl_agent;

  typedef ss_mode_ctrl_agent  ss_mode_ctrl_agent_t;
  ss_mode_ctrl_agent_t ss_mode_ctrl_agent;

  typedef soc_ifc_status_agent  soc_ifc_status_agent_t;
  soc_ifc_status_agent_t soc_ifc_status_agent;

  typedef cptra_status_agent  cptra_status_agent_t;
  cptra_status_agent_t cptra_status_agent;

  typedef ss_mode_status_agent  ss_mode_status_agent_t;
  ss_mode_status_agent_t ss_mode_status_agent;

  typedef mbox_sram_agent  mbox_sram_agent_t;
  mbox_sram_agent_t mbox_sram_agent;




  typedef soc_ifc_predictor #(
                .CONFIG_T(CONFIG_T)
                )
 soc_ifc_pred_t;
  soc_ifc_pred_t soc_ifc_pred;
  typedef soc_ifc_scoreboard #(
                .CONFIG_T(CONFIG_T)
                )
 soc_ifc_sb_t;
  soc_ifc_sb_t soc_ifc_sb;
  typedef soc_ifc_env_cov_subscriber #(
                .PRED_T(soc_ifc_pred_t),
                .CONFIG_T(CONFIG_T)
  )
  soc_ifc_env_cov_sub_t;
 soc_ifc_env_cov_sub_t soc_ifc_env_cov_sub;
  typedef soc_ifc_reg_cov_subscriber #(
                .CONFIG_T(CONFIG_T)
                )
 soc_ifc_reg_cov_sub_t;
  soc_ifc_reg_cov_sub_t soc_ifc_reg_cov_sub;


// Identify the UVM reg adapter in the QVIP installation for the protocol agent.
// Change the typedef below to reflect the reg adapter class type and any parameters.
// Be sure to modify the environment package to import the QVIP protocol package
// that contains the selected adapter.
   // Instantiate register model adapter and predictor
   typedef ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                                       ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                                       ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                                       ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                                       ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                                       ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_reg_transfer_t;

   typedef reg2ahb_adapter #(ahb_reg_transfer_t,
                             ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                             ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                             ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                             ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                             ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                             ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_reg_adapter_t;

   ahb_reg_adapter_t        ahb_reg_adapter;
   caliptra_reg2axi_adapter axi_reg_adapter;

   typedef ahb_reg_predictor #(ahb_reg_transfer_t,
                               ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                               ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                               ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                               ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                               ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                               ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_reg_predictor_t;

   typedef aaxi_uvm_reg_predictor #(aaxi_master_tr) axi_reg_predictor_t;

   ahb_reg_predictor_t    ahb_reg_predictor;
   axi_reg_predictor_t    axi_reg_predictor;


  soc_ifc_virtual_sequencer vsqr;

  // pragma uvmf custom class_item_additional begin
  bit can_handle_reset = 1'b1;
  extern task          detect_reset();
  extern function void set_can_handle_reset(bit en = 1'b1);
  extern task          handle_reset(string kind = "HARD");
  extern task          run_phase(uvm_phase phase);

  typedef enum bit [1:0] {
    AXI_TRACK_NONE,
    AXI_TRACK_ENDPOINTS,
    AXI_TRACK_ALL
  } axi_tracker_mode_e;

  // Enable or disable both tracker directions on one Avery BFM.
  protected function void set_axi_tracker(aaxi_device_class_base bfm, bit enable, string tracker_name);
    if (bfm == null)
      `uvm_fatal("AXI_TRACKER", $sformatf("Cannot configure null Avery BFM %s", tracker_name))
    bfm.log.enable_rx_tracker = enable;
    bfm.log.enable_tx_tracker = enable;
  endfunction

  // Apply one tracker state to every external and internal Avery BFM.
  protected function void set_all_axi_trackers(bit enable);
    set_axi_tracker(axi_soc_manager_agent.driver, enable, "axi_soc_manager_agent");
    set_axi_tracker(axi_dma_manager_agent.driver, enable, "axi_dma_manager_agent");
    set_axi_tracker(axi_soc_ifc_subordinate_agent.driver, enable, "axi_soc_ifc_subordinate_agent");
    set_axi_tracker(axi_sram_subordinate_agent.driver, enable, "axi_sram_subordinate_agent");
    set_axi_tracker(axi_recovery_fifo_subordinate_agent.driver, enable, "axi_recovery_fifo_subordinate_agent");
    foreach (axi_interconnect_agent.driver.master_ports[i])
      set_axi_tracker(axi_interconnect_agent.driver.master_ports[i], enable, $sformatf("axi_interconnect_master_port[%0d]", i));
    for (int unsigned i = 0; i < AXI_FABRIC_NUM_SUBORDINATES; i++)
      set_axi_tracker(axi_interconnect_agent.driver.slave_ports[i], enable, $sformatf("axi_interconnect_slave_port[%0d]", i));
    set_axi_tracker(axi_interconnect_agent.driver.default_slave, enable, "axi_interconnect_default_slave");
    set_axi_tracker(axi_interconnect_agent.driver.default_slave_port, enable, "axi_interconnect_default_slave_port");
  endfunction

  // Apply project tracker policy after every external and interconnect BFM exists.
  protected function void configure_axi_trackers();
    axi_tracker_mode_e mode;

    if ($test$plusargs("SOC_IFC_AXI_TRACK_ALL"))
      mode = AXI_TRACK_ALL;
    else if ($test$plusargs("SOC_IFC_AXI_TRACK_ENDPOINTS"))
      mode = AXI_TRACK_ENDPOINTS;
    else
      mode = AXI_TRACK_NONE;

    // Establish a project-owned default independent of Avery command-line
    // defaults, then enable only the BFMs selected by the project plusargs.
    set_all_axi_trackers(1'b0);

    if (mode inside {AXI_TRACK_ENDPOINTS, AXI_TRACK_ALL}) begin
      set_axi_tracker(axi_dma_manager_agent.driver, 1'b1, "axi_dma_manager_agent");
      set_axi_tracker(axi_soc_ifc_subordinate_agent.driver, 1'b1, "axi_soc_ifc_subordinate_agent");
      set_axi_tracker(axi_sram_subordinate_agent.driver, 1'b1, "axi_sram_subordinate_agent");
      set_axi_tracker(axi_recovery_fifo_subordinate_agent.driver, 1'b1, "axi_recovery_fifo_subordinate_agent");
    end

    if (mode == AXI_TRACK_ALL) begin
      set_all_axi_trackers(1'b1);
    end

    `uvm_info("AXI_TRACKER", $sformatf("Applied AXI tracker policy: %s", mode.name()), UVM_LOW)
  endfunction

  // Initialize one Avery port config. The caller supplies the physical VIF,
  // fixed port index, and legal activity mode, then adds the port-specific
  // manager/subordinate role and address map.
  protected function void configure_axi_common(input aaxi_vip_config cfg, input virtual aaxi_intf vif, input int unsigned port_id,
                                               input uvmf_active_passive_t activity);
    cfg.vif = vif;
    cfg.set_config_int("version", AAXI4);
    cfg.set_config_int("is_active", activity == ACTIVE);
    cfg.set_config_int("port_id", port_id);
    cfg.set_config_int("data_bus_bytes", soc_ifc_pkg::CPTRA_AXI_DMA_DATA_WIDTH / 8);
    cfg.set_config_int("total_outstanding_depth", configuration.axi_outstanding_depth);
    cfg.set_config_int("id_outstanding_depth", configuration.axi_outstanding_depth);
    cfg.set_config_int("opt_awuser_enable", 1);
    cfg.set_config_int("opt_wuser_enable", 1);
    cfg.set_config_int("opt_buser_enable", 1);
    cfg.set_config_int("opt_aruser_enable", 1);
    cfg.set_config_int("opt_ruser_enable", 1);
    cfg.set_config_int("uvm_resp", 1);
  endfunction

  // Assign the first Avery address-map entry. This helper is used for both the
  // five external agents and the interconnect's separate internal port configs.
  protected function void configure_axi_address_map(input aaxi_vip_config cfg, input aaxi_addr_t base_addr, input aaxi_addr_t limit_addr);
    cfg.set_config_int("base_address", base_addr, 0);
    cfg.set_config_int("limit_address", limit_addr, 0);
  endfunction

  // Retrieve a static HDL interface by its parameterized field name. Missing
  // VIFs are fatal because no Avery agent can be built safely without one.
  protected function virtual aaxi_intf get_axi_vif(string field_name);
    virtual aaxi_intf vif;
    if (!uvm_config_db #(virtual aaxi_intf)::get(this, "", field_name, vif))
      `uvm_fatal("AXI_CFG", $sformatf("Unable to retrieve AXI virtual interface %s", field_name))
    return vif;
  endfunction

  // Build the fixed 2x3 Avery topology directly in this environment.
  //
  // Avery requires two configuration layers:
  //   1. Five external aaxi_agent configs model the testbench/DUT-facing ports.
  //   2. aaxi_intc_config owns another config for every internal fabric port.
  //
  // Both layers reference the same VIFs and address windows. The external
  // agents provide stimulus, observation, and endpoint BFMs; the interconnect
  // configs provide routing between those ports.
  protected function void build_axi_components();
    virtual aaxi_intf manager_vif[AXI_FABRIC_NUM_MANAGERS];
    virtual aaxi_intf subordinate_vif[AXI_FABRIC_NUM_SUBORDINATES];
    string field_name;

    // Reject compile-time Avery settings that cannot represent this fixed
    // topology before any vendor components are constructed.
    if (aaxi_pkg::AAXI_INTC_MASTER_CNT != AXI_FABRIC_NUM_MANAGERS || aaxi_pkg::AAXI_INTC_SLAVE_CNT != AXI_FABRIC_NUM_SUBORDINATES)
      `uvm_fatal("AXI_CFG", $sformatf("Avery fabric must compile as %0dx%0d, got %0dx%0d", AXI_FABRIC_NUM_MANAGERS,
                                     AXI_FABRIC_NUM_SUBORDINATES, aaxi_pkg::AAXI_INTC_MASTER_CNT, aaxi_pkg::AAXI_INTC_SLAVE_CNT))
    if (aaxi_pkg::AAXI_ID_WIDTH != soc_ifc_pkg::CPTRA_AXI_DMA_ID_WIDTH)
      `uvm_fatal("AXI_CFG", $sformatf("Avery manager ID width %0d must match DMA ID width %0d", aaxi_pkg::AAXI_ID_WIDTH,
                                     soc_ifc_pkg::CPTRA_AXI_DMA_ID_WIDTH))
    if (aaxi_pkg::AAXI_INTC_ID_WIDTH != soc_ifc_pkg::SOC_IFC_ID_W)
      `uvm_fatal("AXI_CFG", $sformatf("Avery expanded ID width %0d must match SoC IFC ID width %0d", aaxi_pkg::AAXI_INTC_ID_WIDTH,
                                     soc_ifc_pkg::SOC_IFC_ID_W))
    if (!configuration.axi_endpoints_configured)
      `uvm_fatal("AXI_CFG", "Parent bench did not configure AXI endpoint topology")
    if (configuration.axi_sram_config == null || configuration.recovery_fifo_config == null)
      `uvm_fatal("AXI_CFG", "SRAM or recovery endpoint configuration is null")
    if (configuration.axi_soc_ifc_limit_addr < configuration.axi_soc_ifc_base_addr ||
        configuration.axi_sram_config.limit_addr < configuration.axi_sram_config.base_addr)
      `uvm_fatal("AXI_CFG", "AXI address window has a limit below its base")
    if (!((configuration.axi_soc_ifc_limit_addr < configuration.axi_sram_config.base_addr) ||
          (configuration.axi_sram_config.limit_addr < configuration.axi_soc_ifc_base_addr)))
      `uvm_fatal("AXI_CFG", "SoC IFC and SRAM windows overlap")
    if (configuration.recovery_fifo_config.fifo_data_addr inside {
          [configuration.axi_soc_ifc_base_addr:configuration.axi_soc_ifc_limit_addr],
          [configuration.axi_sram_config.base_addr:configuration.axi_sram_config.limit_addr]})
      `uvm_fatal("AXI_CFG", "Recovery FIFO address overlaps another window")
    if (configuration.recovery_fifo_config.depth_dwords == 0)
      `uvm_fatal("AXI_CFG", "Recovery FIFO depth must be nonzero")
    if (configuration.axi_outstanding_depth <= 16)
      `uvm_fatal("AXI_CFG", $sformatf("Outstanding depth %0d cannot run response-pressure stress", configuration.axi_outstanding_depth))

    // Resolve the five HDL-facing interfaces. These names are also published
    // by hdl_top, avoiding direct hierarchy references in the UVM environment.
    axi_soc_manager_vif = get_axi_vif(AXI_FABRIC_SOC_MANAGER_VIF);
    axi_dma_manager_vif = get_axi_vif(AXI_FABRIC_DMA_MANAGER_VIF);
    axi_soc_ifc_subordinate_vif = get_axi_vif(AXI_FABRIC_CALIPTRA_SUBORDINATE_VIF);
    axi_sram_subordinate_vif = get_axi_vif(AXI_FABRIC_SRAM_SUBORDINATE_VIF);
    axi_recovery_fifo_subordinate_vif = get_axi_vif(AXI_FABRIC_RECOVERY_SUBORDINATE_VIF);
    if (!uvm_config_db #(virtual aaxi_interconnect_intf)::get(this, "", AXI_FABRIC_INTERCONNECT_VIF, axi_interconnect_vif))
      `uvm_fatal("AXI_CFG", "Unable to retrieve the AXI interconnect virtual interface")

    // Indexed aliases are needed only while configuring Avery's interconnect,
    // whose API uses fixed manager/slave arrays rather than named ports.
    manager_vif[AXI_FABRIC_SOC_MANAGER_IDX] = axi_soc_manager_vif;
    manager_vif[AXI_FABRIC_DMA_MANAGER_IDX] = axi_dma_manager_vif;
    subordinate_vif[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX] = axi_soc_ifc_subordinate_vif;
    subordinate_vif[AXI_FABRIC_SRAM_SUBORDINATE_IDX] = axi_sram_subordinate_vif;
    subordinate_vif[AXI_FABRIC_RECOVERY_SUBORDINATE_IDX] = axi_recovery_fifo_subordinate_vif;

    // The testbench drives SoC requests into the DUT, so this manager is active.
    axi_soc_manager_config = aaxi_vip_config::type_id::create("axi_soc_manager_config");
    configure_axi_common(axi_soc_manager_config, axi_soc_manager_vif, AXI_FABRIC_SOC_MANAGER_IDX, ACTIVE);
    axi_soc_manager_config.set_config_int("id_width", soc_ifc_pkg::CPTRA_AXI_DMA_ID_WIDTH);
    axi_soc_manager_config.set_config_int("agent_type", AAXI_MASTER);
    configure_axi_address_map(axi_soc_manager_config, '0, '1);

    // The DUT drives DMA requests, so the corresponding manager VIP is passive.
    axi_dma_manager_config = aaxi_vip_config::type_id::create("axi_dma_manager_config");
    configure_axi_common(axi_dma_manager_config, axi_dma_manager_vif, AXI_FABRIC_DMA_MANAGER_IDX, PASSIVE);
    axi_dma_manager_config.set_config_int("id_width", soc_ifc_pkg::CPTRA_AXI_DMA_ID_WIDTH);
    axi_dma_manager_config.set_config_int("agent_type", AAXI_MASTER);
    configure_axi_address_map(axi_dma_manager_config, '0, '1);

    // The RTL supplies responses on the SoC IFC subordinate port; Avery only
    // observes this port while the interconnect routes requests to it.
    axi_soc_ifc_subordinate_config = aaxi_vip_config::type_id::create("axi_soc_ifc_subordinate_config");
    configure_axi_common(axi_soc_ifc_subordinate_config, axi_soc_ifc_subordinate_vif, AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX, PASSIVE);
    axi_soc_ifc_subordinate_config.set_config_int("agent_type", AAXI_SLAVE_TO_INTERCONNECT);
    configure_axi_address_map(axi_soc_ifc_subordinate_config, configuration.axi_soc_ifc_base_addr, configuration.axi_soc_ifc_limit_addr);

    // SRAM is testbench-owned, so Avery actively responds and exposes the BFM
    // memory object later bound to axi_sram_agent.
    axi_sram_subordinate_config = aaxi_vip_config::type_id::create("axi_sram_subordinate_config");
    configure_axi_common(axi_sram_subordinate_config, axi_sram_subordinate_vif, AXI_FABRIC_SRAM_SUBORDINATE_IDX, ACTIVE);
    axi_sram_subordinate_config.set_config_int("agent_type", AAXI_SLAVE_TO_INTERCONNECT);
    configure_axi_address_map(axi_sram_subordinate_config, configuration.axi_sram_config.base_addr, configuration.axi_sram_config.limit_addr);
    axi_sram_subordinate_config.set_config_int("awready_default", 1);
    axi_sram_subordinate_config.set_config_int("dwready_default", 1);
    axi_sram_subordinate_config.set_config_int("arready_default", 1);

    // Recovery is also testbench-owned. FIFO address markers make repeated
    // reads target the streaming endpoint rather than ordinary memory.
    axi_recovery_fifo_subordinate_config = aaxi_vip_config::type_id::create("axi_recovery_fifo_subordinate_config");
    configure_axi_common(axi_recovery_fifo_subordinate_config, axi_recovery_fifo_subordinate_vif,
                         AXI_FABRIC_RECOVERY_SUBORDINATE_IDX, ACTIVE);
    axi_recovery_fifo_subordinate_config.set_config_int("agent_type", AAXI_SLAVE_TO_INTERCONNECT);
    configure_axi_address_map(axi_recovery_fifo_subordinate_config, configuration.recovery_fifo_config.fifo_data_addr,
                              configuration.recovery_fifo_config.fifo_data_addr);
    axi_recovery_fifo_subordinate_config.set_config_int("fifo_address", configuration.recovery_fifo_config.fifo_data_addr, 0);
    axi_recovery_fifo_subordinate_config.set_config_int("fifo_limit", configuration.recovery_fifo_config.fifo_data_addr, 0);
    axi_recovery_fifo_subordinate_config.set_config_int("warn_on_uninitialized_read", 0);
    axi_recovery_fifo_subordinate_config.set_config_int("awready_default", 1);
    axi_recovery_fifo_subordinate_config.set_config_int("dwready_default", 1);
    axi_recovery_fifo_subordinate_config.set_config_int("arready_default", 1);

    // Construct every external agent only after its complete native Avery
    // configuration is available.
    axi_soc_manager_agent = aaxi_agent::type_id::create("axi_soc_manager_agent", this);
    axi_soc_manager_agent.set_config(axi_soc_manager_config);
    axi_dma_manager_agent = aaxi_agent::type_id::create("axi_dma_manager_agent", this);
    axi_dma_manager_agent.set_config(axi_dma_manager_config);
    axi_soc_ifc_subordinate_agent = aaxi_agent::type_id::create("axi_soc_ifc_subordinate_agent", this);
    axi_soc_ifc_subordinate_agent.set_config(axi_soc_ifc_subordinate_config);
    axi_sram_subordinate_agent = aaxi_agent::type_id::create("axi_sram_subordinate_agent", this);
    axi_sram_subordinate_agent.set_config(axi_sram_subordinate_config);
    axi_recovery_fifo_subordinate_agent = aaxi_agent::type_id::create("axi_recovery_fifo_subordinate_agent", this);
    axi_recovery_fifo_subordinate_agent.set_config(axi_recovery_fifo_subordinate_config);

    // Avery's interconnect config allocates its own active internal port agents.
    // They move transactions between the external VIFs but do not replace the
    // external active/passive agents configured above.
    axi_interconnect_config = new("axi_interconnect_config", AXI_FABRIC_NUM_MANAGERS, AXI_FABRIC_NUM_SUBORDINATES);
    axi_interconnect_config.intc_top_name = "SOC_IFC_AXI_FABRIC_";
    axi_interconnect_config.configure_cfgs();
    axi_interconnect_config.vif = axi_interconnect_vif;

    foreach (axi_interconnect_config.master_cfg[i]) begin
      configure_axi_common(axi_interconnect_config.master_cfg[i], manager_vif[i], i, ACTIVE);
      axi_interconnect_config.master_cfg[i].set_config_int("id_width", soc_ifc_pkg::CPTRA_AXI_DMA_ID_WIDTH);
      axi_interconnect_config.master_cfg[i].set_config_int("agent_type", AAXI_INTERCONNECT_MASTER_PORT);
      field_name = $sformatf("%smaster_intfs[%0d]", axi_interconnect_config.intc_top_name, i);
      // The vendor interconnect retrieves this exact generated field name from
      // its component scope during build_phase.
      uvm_config_db #(aaxi_vip_config)::set(this, "axi_interconnect_agent", field_name, axi_interconnect_config.master_cfg[i]);
    end
    foreach (axi_interconnect_config.slave_cfg[i]) begin
      configure_axi_common(axi_interconnect_config.slave_cfg[i], subordinate_vif[i], i, ACTIVE);
      axi_interconnect_config.slave_cfg[i].set_config_int("agent_type", AAXI_INTERCONNECT_SLAVE_PORT);
      field_name = $sformatf("%sslave_intfs[%0d]", axi_interconnect_config.intc_top_name, i);
      uvm_config_db #(aaxi_vip_config)::set(this, "axi_interconnect_agent", field_name, axi_interconnect_config.slave_cfg[i]);
    end
    configure_axi_address_map(axi_interconnect_config.slave_cfg[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX],
                              configuration.axi_soc_ifc_base_addr, configuration.axi_soc_ifc_limit_addr);
    configure_axi_address_map(axi_interconnect_config.slave_cfg[AXI_FABRIC_SRAM_SUBORDINATE_IDX],
                              configuration.axi_sram_config.base_addr, configuration.axi_sram_config.limit_addr);
    configure_axi_address_map(axi_interconnect_config.slave_cfg[AXI_FABRIC_RECOVERY_SUBORDINATE_IDX],
                              configuration.recovery_fifo_config.fifo_data_addr, configuration.recovery_fifo_config.fifo_data_addr);
    axi_interconnect_config.slave_cfg[AXI_FABRIC_RECOVERY_SUBORDINATE_IDX].set_config_int(
      "fifo_address", configuration.recovery_fifo_config.fifo_data_addr, 0);
    axi_interconnect_config.slave_cfg[AXI_FABRIC_RECOVERY_SUBORDINATE_IDX].set_config_int(
      "fifo_limit", configuration.recovery_fifo_config.fifo_data_addr, 0);

    // Publish the dedicated interconnect control VIF under Avery's required key
    // before factory-creating the interconnect component.
    uvm_config_db #(virtual aaxi_interconnect_intf)::set(this, "axi_interconnect_agent", "INTERCONNECT", axi_interconnect_vif);
    axi_interconnect_agent = aaxi_pkg_xactor::aaxi_intc_agent::type_id::create("axi_interconnect_agent", this);
    axi_interconnect_agent.set_config(axi_interconnect_config);
    `uvm_info("AXI_CFG", "Built fixed SoC stimulus, DUT DMA, DUT Caliptra, SRAM, recovery, and interconnect agents", UVM_LOW)
  endfunction
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
// pragma uvmf custom build_phase_pre_super begin
    int unsigned tr_recording_detail;
    tr_recording_detail = $test$plusargs("SOC_IFC_ENABLE_TR_RECORDING") ? UVM_FULL : UVM_NONE;
    uvm_config_int::set(this, "*", "recording_detail", tr_recording_detail);
    `uvm_info("SOC_IFC_ENV", $sformatf("UVM transaction recording (tr_db.log) %s (recording_detail=%0d); toggle with +SOC_IFC_ENABLE_TR_RECORDING", (tr_recording_detail == UVM_NONE) ? "DISABLED" : "ENABLED", tr_recording_detail), UVM_LOW)
// pragma uvmf custom build_phase_pre_super end
    super.build_phase(phase);
    uvm_config_db #(aaxi_protocol_version)::set(uvm_root::get(), "*", "vers", AAXI4);
    build_axi_components();
    axi_sram_agent = soc_ifc_axi_sram_agent::type_id::create("axi_sram_agent", this);
    axi_sram_agent.set_config(configuration.axi_sram_config);
    recovery_fifo_agent = soc_ifc_recovery_fifo_agent::type_id::create("recovery_fifo_agent", this);
    recovery_fifo_agent.set_config(configuration.recovery_fifo_config);
    qvip_ahb_lite_slave_subenv = qvip_ahb_lite_slave_environment#()::type_id::create("qvip_ahb_lite_slave_subenv",this);
    qvip_ahb_lite_slave_subenv.set_config(configuration.qvip_ahb_lite_slave_subenv_config);
    soc_ifc_ctrl_agent = soc_ifc_ctrl_agent_t::type_id::create("soc_ifc_ctrl_agent",this);
    soc_ifc_ctrl_agent.set_config(configuration.soc_ifc_ctrl_agent_config);
    cptra_ctrl_agent = cptra_ctrl_agent_t::type_id::create("cptra_ctrl_agent",this);
    cptra_ctrl_agent.set_config(configuration.cptra_ctrl_agent_config);
    ss_mode_ctrl_agent = ss_mode_ctrl_agent_t::type_id::create("ss_mode_ctrl_agent",this);
    ss_mode_ctrl_agent.set_config(configuration.ss_mode_ctrl_agent_config);
    soc_ifc_status_agent = soc_ifc_status_agent_t::type_id::create("soc_ifc_status_agent",this);
    soc_ifc_status_agent.set_config(configuration.soc_ifc_status_agent_config);
    cptra_status_agent = cptra_status_agent_t::type_id::create("cptra_status_agent",this);
    cptra_status_agent.set_config(configuration.cptra_status_agent_config);
    ss_mode_status_agent = ss_mode_status_agent_t::type_id::create("ss_mode_status_agent",this);
    ss_mode_status_agent.set_config(configuration.ss_mode_status_agent_config);
    mbox_sram_agent = mbox_sram_agent_t::type_id::create("mbox_sram_agent",this);
    mbox_sram_agent.set_config(configuration.mbox_sram_agent_config);
    soc_ifc_pred = soc_ifc_pred_t::type_id::create("soc_ifc_pred",this);
    soc_ifc_pred.configuration = configuration;
    soc_ifc_sb = soc_ifc_sb_t::type_id::create("soc_ifc_sb",this);
    soc_ifc_sb.configuration = configuration;
    soc_ifc_sb.enable_wait_for_scoreboard_empty();
    soc_ifc_env_cov_sub = soc_ifc_env_cov_sub_t::type_id::create("soc_ifc_env_cov_sub",this);
    soc_ifc_env_cov_sub.configuration = configuration;
    soc_ifc_env_cov_sub.pred = soc_ifc_pred;
    soc_ifc_reg_cov_sub = soc_ifc_reg_cov_sub_t::type_id::create("soc_ifc_reg_cov_sub",this);
    soc_ifc_reg_cov_sub.configuration = configuration;
// pragma uvmf custom reg_model_build_phase begin
  // Build register model predictor if prediction is enabled
  if (configuration.enable_reg_prediction) begin
    ahb_reg_predictor = ahb_reg_predictor_t::type_id::create("ahb_reg_predictor", this);
    axi_reg_predictor = axi_reg_predictor_t::type_id::create("axi_reg_predictor", this);
  end
// pragma uvmf custom reg_model_build_phase end

    vsqr = soc_ifc_virtual_sequencer::type_id::create("vsqr", this);
    vsqr.set_config(configuration);
    configuration.set_vsqr(vsqr);
    `uvm_info("SOC_IFC_ENV",
      "Built protocol agents, endpoint services, predictor, scoreboard, coverage, and virtual sequencer",
      UVM_LOW)

    // pragma uvmf custom build_phase begin
    // pragma uvmf custom build_phase end
  endfunction

// ****************************************************************************
// FUNCTION: connect_phase()
// This function makes all connections within this environment.  Connections
// typically include agent to predictor, predictor to scoreboard and scoreboard
// to agent.
//
  virtual function void connect_phase(uvm_phase phase);
// pragma uvmf custom connect_phase_pre_super begin
// pragma uvmf custom connect_phase_pre_super end
    super.connect_phase(phase);
    axi_sram_agent.bind_bfm(axi_sram_subordinate_agent.bfm);
    recovery_fifo_agent.bind_bfm(axi_recovery_fifo_subordinate_agent.bfm);
    axi_sram_subordinate_agent.add_callback(axi_sram_agent.delay_callback);
    axi_recovery_fifo_subordinate_agent.add_callback(recovery_fifo_agent.callback);
    axi_recovery_fifo_subordinate_agent.add_callback(
      recovery_fifo_agent.delay_callback);
    vsqr.soc_axi_sequencer = axi_soc_manager_agent.sequencer;
    vsqr.axi_sram_sequencer = axi_sram_agent.sequencer;
    vsqr.recovery_fifo_sequencer = recovery_fifo_agent.sequencer;
    soc_ifc_ctrl_agent.monitored_ap.connect(soc_ifc_pred.soc_ifc_ctrl_agent_ae);
    cptra_ctrl_agent.monitored_ap.connect(soc_ifc_pred.cptra_ctrl_agent_ae);
    ss_mode_ctrl_agent.monitored_ap.connect(soc_ifc_pred.ss_mode_ctrl_agent_ae);
    mbox_sram_agent.monitored_ap.connect(soc_ifc_pred.mbox_sram_agent_ae);
    soc_ifc_pred.soc_ifc_sb_ap.connect(soc_ifc_sb.expected_analysis_export);
    soc_ifc_pred.cptra_sb_ap.connect(soc_ifc_sb.expected_cptra_analysis_export);
    soc_ifc_pred.ss_mode_sb_ap.connect(soc_ifc_sb.expected_ss_mode_analysis_export);
    soc_ifc_pred.soc_ifc_sb_ahb_ap.connect(soc_ifc_sb.expected_ahb_analysis_export);
    soc_ifc_pred.soc_ifc_sb_axi_ap.connect(soc_ifc_sb.expected_axi_analysis_export);
    soc_ifc_status_agent.monitored_ap.connect(soc_ifc_sb.actual_analysis_export);
    cptra_status_agent.monitored_ap.connect(soc_ifc_sb.actual_cptra_analysis_export);
    ss_mode_status_agent.monitored_ap.connect(soc_ifc_sb.actual_ss_mode_analysis_export);
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap = qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.ap; 
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap["burst_transfer"].connect(soc_ifc_pred.ahb_slave_0_ae);
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap["burst_transfer_sb"].connect(soc_ifc_sb.actual_ahb_analysis_export);
    // Predict from completed DUT-side transfers so variable interconnect
    // latency is reflected without fixed cycle delays.
    axi_soc_ifc_subordinate_agent.driver.slv_rx_W_port.connect(soc_ifc_pred.axi_dut_ae);
    axi_soc_ifc_subordinate_agent.driver.slv_tx_R_port.connect(soc_ifc_pred.axi_dut_ae);
    axi_soc_manager_agent.driver.write_done_port.connect(
      soc_ifc_sb.actual_axi_analysis_export);
    axi_soc_manager_agent.driver.read_done_port.connect(
      soc_ifc_sb.actual_axi_analysis_export);
    if ( configuration.qvip_ahb_lite_slave_subenv_interface_activity[0] == ACTIVE )
       uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,configuration.qvip_ahb_lite_slave_subenv_interface_names[0],qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer  );
    uvm_config_db #(aaxi_sequencer)::set(
      null, UVMF_SEQUENCERS, AXI_FABRIC_SOC_MANAGER_VIF,
      axi_soc_manager_agent.sequencer);
    `uvm_info("SOC_IFC_ENV",
      "Connected AXI endpoint services, passive checking, coverage, and virtual sequencer aliases",
      UVM_LOW)
    // pragma uvmf custom reg_model_connect_phase begin
    /*if (TODO) */begin:connect_coverage
        soc_ifc_pred.soc_ifc_cov_ap      .connect                                   (soc_ifc_env_cov_sub.soc_ifc_ctrl_ae  );
        soc_ifc_pred.cptra_cov_ap        .connect                                   (soc_ifc_env_cov_sub.cptra_ctrl_ae    );
        soc_ifc_pred.ss_mode_cov_ap      .connect                                   (soc_ifc_env_cov_sub.ss_mode_ctrl_ae  );
        soc_ifc_status_agent.monitored_ap.connect                                   (soc_ifc_env_cov_sub.soc_ifc_status_ae);
        cptra_status_agent  .monitored_ap.connect                                   (soc_ifc_env_cov_sub.cptra_status_ae  );
        ss_mode_status_agent.monitored_ap.connect                                   (soc_ifc_env_cov_sub.ss_mode_status_ae);
        mbox_sram_agent     .monitored_ap.connect                                   (soc_ifc_env_cov_sub.mbox_sram_ae     );
        qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap["burst_transfer_cov"].connect(soc_ifc_env_cov_sub.ahb_ae           );
        axi_soc_manager_agent.driver.ms_tx_AW_W_port.connect                      (soc_ifc_env_cov_sub.axi_ae           );
        axi_soc_manager_agent.driver.ms_rx_rvalid_port.connect                    (soc_ifc_env_cov_sub.axi_ae           );
        axi_soc_manager_agent.driver.write_done_port.connect                      (soc_ifc_env_cov_sub.axi_completed_ae );
        axi_soc_manager_agent.driver.read_done_port.connect                       (soc_ifc_env_cov_sub.axi_completed_ae );
    end:connect_coverage
    // Create register model adapter if required
    if (configuration.enable_reg_prediction ||
        configuration.enable_reg_adaptation) begin
      ahb_reg_adapter = ahb_reg_adapter_t::type_id::create("reg2ahb_adapter");
      ahb_reg_adapter.en_n_bits = 1; // This is to allow the adapter to generate addresses
                                     // that are not aligned to 64-bit width (the native AHB interface width)
      axi_reg_adapter = caliptra_reg2axi_adapter::type_id::create("reg2axi_adapter");
    end
    // Set sequencer and adapter in register model map
    if ((configuration.enable_reg_adaptation) && (qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer != null ))
      configuration.soc_ifc_rm.soc_ifc_AHB_map.set_sequencer(qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer, ahb_reg_adapter);
    if ((configuration.enable_reg_adaptation) &&
        (axi_soc_manager_agent.sequencer != null))
      configuration.soc_ifc_rm.soc_ifc_AXI_map.set_sequencer(
        axi_soc_manager_agent.sequencer, axi_reg_adapter);
    // Set map and adapter handles within uvm predictor
    if (configuration.enable_reg_prediction) begin
      ahb_reg_predictor.map     = configuration.soc_ifc_rm.soc_ifc_AHB_map;
      axi_reg_predictor.map     = configuration.soc_ifc_rm.soc_ifc_AXI_map;
      ahb_reg_predictor.adapter = ahb_reg_adapter;
      axi_reg_predictor.adapter = axi_reg_adapter;
//      configuration.soc_ifc_rm.soc_ifc_AHB_map.set_auto_predict(1);
//      configuration.soc_ifc_rm.soc_ifc_AXI_map.set_auto_predict(1);
      // The connection between the agent analysis_port and uvm_reg_predictor 
      // analysis_export could cause problems due to a uvm register package bug,
      // if this environment is used as a sub-environment at a higher level.
      // The uvm register package does not construct sub-maps within register
      // sub blocks.  While the connection below succeeds, the execution of the
      // write method associated with the analysis_export fails.  It fails because
      // the write method executes the get_reg_by_offset method of the register
      // map, which is null because of the uvm register package bug.
      // The call works when operating at block level because the uvm register 
      // package constructs the top level register map.  The call fails when the 
      // register map associated with this environment is a sub-map.  Construction
      // of the sub-maps must be done manually.
      soc_ifc_pred.soc_ifc_ahb_reg_ap.connect(ahb_reg_predictor.bus_item_export);
      soc_ifc_pred.soc_ifc_axi_reg_wr_ap.connect(axi_reg_predictor.bus_item_write_export);
      soc_ifc_pred.soc_ifc_axi_reg_rd_ap.connect(axi_reg_predictor.bus_item_read_export);
      ahb_reg_predictor.reg_ap.connect(soc_ifc_reg_cov_sub.analysis_export);
      axi_reg_predictor.reg_ap.connect(soc_ifc_reg_cov_sub.analysis_export);
//      qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap["burst_transfer"].connect(ahb_reg_predictor.bus_item_export);
//      qvip_apb5_slave_subenv_apb5_master_0_ap["trans_ap"].connect(apb_reg_predictor.bus_item_export);
    end
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
     super.start_of_simulation_phase(phase);
     configure_axi_trackers();
     configuration.soc_ifc_configuration_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// Wait for reset assertion and dispatch environment reset handling.
task soc_ifc_environment::detect_reset();
    string kind = "SOFT";

    // Detect reset assertion from soc_ifc_ctrl_agent
    this.configuration.soc_ifc_ctrl_agent_config.wait_for_reset_assertion(kind);

    // Handle
    this.handle_reset(kind);
endtask

// Called by a super-environment, if present, to bubble reset responsibility up
// Enable or disable this environment's reset-monitor process.
function void soc_ifc_environment::set_can_handle_reset(bit en = 1'b1);
    this.can_handle_reset = en;
endfunction

// Reset agents, predictor, and scoreboard for the requested reset kind.
task soc_ifc_environment::handle_reset(string kind = "HARD");
    uvm_object obj;
    uvm_event reset_synchro;
    reset_flag rst_sync_flag;

    if (kind == "HARD")
        configuration.global_straps_captured = 1'b0;

    // Reset status agents (needed to reset monitor transaction keys)
    this.cptra_status_agent.handle_reset(kind);
    this.soc_ifc_status_agent.handle_reset(kind);
    this.ss_mode_status_agent.handle_reset(kind);

    // Reset mbox_sram agent (needed to reset the ECC error injection)
    this.mbox_sram_agent.handle_reset(kind);

//    // Reset AXI agent TODO investigating correct way to do this as of 2/4/2025
//    this.axi_fabric.manager[0].driver.master_reset();

    // Reset scoreboard according to kind
    this.soc_ifc_sb.handle_reset(kind);

    // Reset predictor according to kind
    this.soc_ifc_pred.handle_reset(kind, reset_synchro);

    // A "SOFT" reset (cptra_rst_b) is followed by noncore reset assertion; we
    // need to time the assertion of the reset to all the soc_ifc_env components
    // based on the predictor
    if (kind == "SOFT") begin
        `uvm_info("SOC_IFC_ENV_HANDLE_RESET", "After receiving SOFT reset, waiting for predictor to signal the NONCORE reset so environment can be reset", UVM_LOW)

        reset_synchro.wait_trigger_data(obj);
        $cast(rst_sync_flag, obj);
        if (rst_sync_flag.get_name() != "noncore_reset_flag")
            `uvm_error("SOC_IFC_ENV_HANDLE_RESET", {"Reset synchronization event returned a reset event of unexpected type! ", rst_sync_flag.get_name()})

        // Reset status agents (needed to reset monitor transaction keys)
        this.cptra_status_agent.handle_reset("NONCORE");
        this.soc_ifc_status_agent.handle_reset("NONCORE");
        this.ss_mode_status_agent.handle_reset("NONCORE");

        // Reset mbox_sram agent (needed to reset the ECC error injection)
        this.mbox_sram_agent.handle_reset("NONCORE");

        // Reset scoreboard according to kind
        this.soc_ifc_sb.handle_reset("NONCORE");

        `uvm_info("SOC_IFC_ENV_HANDLE_RESET", "After receiving NONCORE reset signal from soc_ifc_predictor, completed environment-level NONCORE reset prerequisites and continuing with reset prediction", UVM_LOW)
        reset_synchro.reset();
    end

    // TODO does this happen naturally from hdl_top driving reset?
    // Reset AHB
endtask

// Monitor resets when this environment owns reset handling.
task soc_ifc_environment::run_phase(uvm_phase phase);
    if (this.can_handle_reset) begin
        fork
            forever detect_reset();
        join
    end
endtask
// pragma uvmf custom external end
