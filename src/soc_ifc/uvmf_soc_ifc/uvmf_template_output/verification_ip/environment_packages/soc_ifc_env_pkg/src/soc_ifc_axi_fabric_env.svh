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

// Builds the Avery AXI fabric joining SoC and DMA managers to Caliptra, SRAM,
// and recovery subordinates. This component owns Avery transport agents; SRAM
// and recovery behavior remains in separate endpoint components.
class soc_ifc_axi_fabric_env extends uvm_env;

  `uvm_component_utils(soc_ifc_axi_fabric_env)

  soc_ifc_axi_fabric_config configuration;

  aaxi_agent      manager[];
  aaxi_agent      subordinate[];
  aaxi_intc_agent interconnect_agent;

  aaxi_vip_config manager_config[];
  aaxi_vip_config subordinate_config[];
  aaxi_intc_config interconnect_config;

  virtual aaxi_intf manager_vif[];
  virtual aaxi_intf subordinate_vif[];
  virtual aaxi_interconnect_intf interconnect_vif;

  // Construct the AXI fabric environment.
  function new(string name = "soc_ifc_axi_fabric_env",
               uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Assign the topology consumed during build_phase.
  function void set_config(soc_ifc_axi_fabric_config configuration);
    this.configuration = configuration;
  endfunction

  // Return the SRAM subordinate BFM for endpoint binding.
  function aaxi_device_class get_sram_bfm();
    return subordinate[configuration.sram_subordinate_idx].bfm;
  endfunction

  // Return the recovery subordinate BFM for endpoint binding.
  function aaxi_device_class get_recovery_bfm();
    return subordinate[configuration.recovery_subordinate_idx].bfm;
  endfunction

  // Register a callback on the recovery subordinate.
  function void add_recovery_callback(aaxi_callbacks callback);
    subordinate[configuration.recovery_subordinate_idx].add_callback(callback);
  endfunction

  // Register a callback on the SRAM subordinate.
  function void add_sram_callback(aaxi_callbacks callback);
    subordinate[configuration.sram_subordinate_idx].add_callback(callback);
  endfunction

  // Apply protocol, ID, user-signal, and outstanding-depth settings shared by
  // every port. Port-specific active/passive role and address ownership are
  // configured by build_phase after this common setup.
  protected function void configure_common(
      input aaxi_vip_config cfg,
      input virtual aaxi_intf vif,
      input int unsigned port_id,
      input int unsigned id_width,
      input bit is_active);
    cfg.vif = vif;
    cfg.set_config_int("version", AAXI4);
    cfg.set_config_int("is_active", is_active);
    cfg.set_config_int("port_id", port_id);
    cfg.set_config_int("data_bus_bytes", soc_ifc_pkg::CPTRA_AXI_DMA_DATA_WIDTH / 8);
    if (id_width != 0)
      cfg.set_config_int("id_width", id_width);
    cfg.set_config_int("total_outstanding_depth", configuration.outstanding_depth);
    cfg.set_config_int("id_outstanding_depth", configuration.outstanding_depth);
    cfg.set_config_int("opt_awuser_enable", 1);
    cfg.set_config_int("opt_wuser_enable", 1);
    cfg.set_config_int("opt_buser_enable", 1);
    cfg.set_config_int("opt_aruser_enable", 1);
    cfg.set_config_int("opt_ruser_enable", 1);
    cfg.set_config_int("uvm_resp", 1);
  endfunction

  // Assign one subordinate address window.
  protected function void configure_address_map(
      input aaxi_vip_config cfg,
      input aaxi_addr_t base_addr,
      input aaxi_addr_t limit_addr);
    cfg.cfg_info.base_address[0]  = base_addr;
    cfg.cfg_info.limit_address[0] = limit_addr;
  endfunction

  // Build and configure all Avery manager, subordinate, and interconnect agents.
  virtual function void build_phase(uvm_phase phase);
    string field_name;

    super.build_phase(phase);
    if (configuration == null)
      `uvm_fatal("AXI_FABRIC", "soc_ifc AXI fabric configuration is null")
    configuration.validate();

    manager = new[configuration.manager_vif_name.size()];
    subordinate = new[configuration.subordinate_vif_name.size()];
    manager_config = new[configuration.manager_vif_name.size()];
    subordinate_config = new[configuration.subordinate_vif_name.size()];
    manager_vif = new[configuration.manager_vif_name.size()];
    subordinate_vif = new[configuration.subordinate_vif_name.size()];

    foreach (manager_vif[i])
      if (!uvm_config_db #(virtual aaxi_intf)::get(
            this, "", configuration.manager_vif_name[i], manager_vif[i]))
        `uvm_fatal("AXI_FABRIC",
          $sformatf("Unable to retrieve manager virtual interface %s",
                    configuration.manager_vif_name[i]))
    foreach (subordinate_vif[i])
      if (!uvm_config_db #(virtual aaxi_intf)::get(
            this, "", configuration.subordinate_vif_name[i], subordinate_vif[i]))
        `uvm_fatal("AXI_FABRIC",
          $sformatf("Unable to retrieve subordinate virtual interface %s",
                    configuration.subordinate_vif_name[i]))
    if (!uvm_config_db #(virtual aaxi_interconnect_intf)::get(
          this, "", configuration.interconnect_vif_name, interconnect_vif))
      `uvm_fatal("AXI_FABRIC",
        $sformatf("Unable to retrieve interconnect virtual interface %s",
                  configuration.interconnect_vif_name))

    // The SoC manager is active because UVM drives SoC traffic. The DMA manager
    // is passive because its pins are driven by the DUT DMA.
    foreach (manager_config[i]) begin
      manager_config[i] = aaxi_vip_config::type_id::create(
        $sformatf("manager_config[%0d]", i));
      configure_common(manager_config[i], manager_vif[i], i,
                       aaxi_pkg::AAXI_ID_WIDTH,
                       (i == configuration.soc_manager_idx));
      manager_config[i].set_config_int("agent_type", AAXI_MASTER);
    end
    configure_address_map(manager_config[configuration.soc_manager_idx],
                          configuration.caliptra_base_addr,
                          configuration.caliptra_limit_addr);
    configure_address_map(manager_config[configuration.dma_manager_idx],
                          '0, '1);

    // Caliptra is an RTL subordinate and therefore passive. SRAM and recovery
    // are active Avery responders that provide testbench-owned storage.
    foreach (subordinate_config[i]) begin
      subordinate_config[i] = aaxi_vip_config::type_id::create(
        $sformatf("subordinate_config[%0d]", i));
      configure_common(subordinate_config[i], subordinate_vif[i], i,
                       0,
                       (i != configuration.caliptra_subordinate_idx));
      subordinate_config[i].set_config_int(
        "agent_type", AAXI_SLAVE_TO_INTERCONNECT);
    end
    configure_address_map(
      subordinate_config[configuration.caliptra_subordinate_idx],
      configuration.caliptra_base_addr,
      configuration.caliptra_limit_addr);
    configure_address_map(subordinate_config[configuration.sram_subordinate_idx],
                          configuration.sram_config.base_addr,
                          configuration.sram_config.limit_addr);
    configure_address_map(
      subordinate_config[configuration.recovery_subordinate_idx],
      configuration.recovery_config.fifo_data_addr,
      configuration.recovery_config.fifo_data_addr);
    subordinate_config[configuration.recovery_subordinate_idx].
      cfg_info.fifo_address[0] =
      configuration.recovery_config.fifo_data_addr;
    subordinate_config[configuration.recovery_subordinate_idx].
      cfg_info.fifo_limit[0] =
      configuration.recovery_config.fifo_data_addr;
    subordinate_config[configuration.recovery_subordinate_idx].set_config_int(
      "warn_on_uninitialized_read", 0);
    foreach (subordinate_config[i]) begin
      if (i != configuration.caliptra_subordinate_idx) begin
        subordinate_config[i].set_config_int("awready_default", 1);
        subordinate_config[i].set_config_int("dwready_default", 1);
        subordinate_config[i].set_config_int("arready_default", 1);
      end
    end

    foreach (manager[i]) begin
      manager[i] = aaxi_agent::type_id::create($sformatf("manager[%0d]", i), this);
      manager[i].set_config(manager_config[i]);
    end
    foreach (subordinate[i]) begin
      subordinate[i] =
        aaxi_agent::type_id::create($sformatf("subordinate[%0d]", i), this);
      subordinate[i].set_config(subordinate_config[i]);
    end

    // Avery requires a second set of port configurations inside its
    // interconnect agent. These reference the same static interfaces but use
    // interconnect-specific agent roles.
    interconnect_config =
      new("interconnect_config", $size(manager), $size(subordinate));
    interconnect_config.intc_top_name = "SOC_IFC_AXI_FABRIC_";
    interconnect_config.configure_cfgs();
    interconnect_config.vif = interconnect_vif;

    foreach (interconnect_config.master_cfg[i]) begin
      configure_common(interconnect_config.master_cfg[i], manager_vif[i], i,
                       aaxi_pkg::AAXI_ID_WIDTH, 1'b1);
      interconnect_config.master_cfg[i].set_config_int(
        "agent_type", AAXI_INTERCONNECT_MASTER_PORT);
      field_name =
        $sformatf("%smaster_intfs[%0d]",
                  interconnect_config.intc_top_name, i);
      uvm_config_db #(aaxi_vip_config)::set(
        this, "interconnect", field_name,
        interconnect_config.master_cfg[i]);
    end
    foreach (interconnect_config.slave_cfg[i]) begin
      configure_common(interconnect_config.slave_cfg[i], subordinate_vif[i], i,
                       0, 1'b1);
      interconnect_config.slave_cfg[i].set_config_int(
        "agent_type", AAXI_INTERCONNECT_SLAVE_PORT);
      field_name =
        $sformatf("%sslave_intfs[%0d]",
                  interconnect_config.intc_top_name, i);
      uvm_config_db #(aaxi_vip_config)::set(
        this, "interconnect", field_name,
        interconnect_config.slave_cfg[i]);
    end
    configure_address_map(
      interconnect_config.slave_cfg[configuration.caliptra_subordinate_idx],
      configuration.caliptra_base_addr,
      configuration.caliptra_limit_addr);
    configure_address_map(
      interconnect_config.slave_cfg[configuration.sram_subordinate_idx],
      configuration.sram_config.base_addr,
      configuration.sram_config.limit_addr);
    configure_address_map(
      interconnect_config.slave_cfg[configuration.recovery_subordinate_idx],
      configuration.recovery_config.fifo_data_addr,
      configuration.recovery_config.fifo_data_addr);
    interconnect_config.slave_cfg[configuration.recovery_subordinate_idx].
      cfg_info.fifo_address[0] =
      configuration.recovery_config.fifo_data_addr;
    interconnect_config.slave_cfg[configuration.recovery_subordinate_idx].
      cfg_info.fifo_limit[0] =
      configuration.recovery_config.fifo_data_addr;

    uvm_config_db #(virtual aaxi_interconnect_intf)::set(
      this, "interconnect", "INTERCONNECT", interconnect_vif);
    interconnect_agent =
      aaxi_intc_agent::type_id::create("interconnect", this);
    interconnect_agent.set_config(interconnect_config);
    `uvm_info("AXI_FABRIC",
      $sformatf(
        "Built %0d-manager/%0d-subordinate AXI fabric with outstanding depth %0d",
        $size(manager), $size(subordinate),
        configuration.outstanding_depth), UVM_LOW)
  endfunction

endclass
