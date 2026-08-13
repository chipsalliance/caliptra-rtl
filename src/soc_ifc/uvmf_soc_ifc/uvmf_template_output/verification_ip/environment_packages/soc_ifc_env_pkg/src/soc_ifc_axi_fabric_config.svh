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

// Describes the two-manager, three-subordinate Avery AXI fabric topology.
// It contains names, address ownership, and protocol limits only; Avery agents
// and endpoint models are constructed and owned by environment components.
class soc_ifc_axi_fabric_config extends uvm_object;

  `uvm_object_utils(soc_ifc_axi_fabric_config)

  string manager_vif_name[];
  string subordinate_vif_name[];
  string interconnect_vif_name;

  int unsigned soc_manager_idx;
  int unsigned dma_manager_idx;
  int unsigned caliptra_subordinate_idx;
  int unsigned sram_subordinate_idx;
  int unsigned recovery_subordinate_idx;

  aaxi_addr_t caliptra_base_addr;
  aaxi_addr_t caliptra_limit_addr;
  soc_ifc_axi_sram_config sram_config;
  soc_ifc_recovery_fifo_config recovery_config;
  int unsigned outstanding_depth;

  protected bit configured;

  // Construct an unconfigured fabric description.
  function new(string name = "soc_ifc_axi_fabric_config");
    super.new(name);
    configured = 1'b0;
  endfunction

  // Capture the complete topology in one call, then validate immediately so
  // malformed geometry cannot reach Avery component construction.
  function void configure(
      input string      manager_vif_name[],
      input string      subordinate_vif_name[],
      input string      interconnect_vif_name,
      input int unsigned soc_manager_idx,
      input int unsigned dma_manager_idx,
      input int unsigned caliptra_subordinate_idx,
      input int unsigned sram_subordinate_idx,
      input int unsigned recovery_subordinate_idx,
      input aaxi_addr_t caliptra_base_addr,
      input aaxi_addr_t caliptra_limit_addr,
      input soc_ifc_axi_sram_config sram_config,
      input soc_ifc_recovery_fifo_config recovery_config,
      input int unsigned outstanding_depth);
    this.manager_vif_name        = manager_vif_name;
    this.subordinate_vif_name    = subordinate_vif_name;
    this.interconnect_vif_name   = interconnect_vif_name;
    this.soc_manager_idx         = soc_manager_idx;
    this.dma_manager_idx         = dma_manager_idx;
    this.caliptra_subordinate_idx = caliptra_subordinate_idx;
    this.sram_subordinate_idx     = sram_subordinate_idx;
    this.recovery_subordinate_idx = recovery_subordinate_idx;
    this.caliptra_base_addr       = caliptra_base_addr;
    this.caliptra_limit_addr      = caliptra_limit_addr;
    this.sram_config              = sram_config;
    this.recovery_config          = recovery_config;
    this.outstanding_depth        = outstanding_depth;
    configured = 1'b1;
    validate();
  endfunction

  // Fail before agent construction when compile-time Avery widths/counts,
  // endpoint windows, or outstanding-depth assumptions disagree with the
  // topology expected by hdl_top and the environment.
  function void validate();
    if (!configured)
      `uvm_fatal("AXI_FABRIC_CFG", "Fabric configuration has not been initialized")
    if (sram_config == null || recovery_config == null)
      `uvm_fatal("AXI_FABRIC_CFG", "Endpoint configuration is null")
    if (aaxi_pkg::AAXI_INTC_MASTER_CNT != manager_vif_name.size() ||
        aaxi_pkg::AAXI_INTC_SLAVE_CNT != subordinate_vif_name.size())
      `uvm_fatal("AXI_FABRIC_CFG",
        $sformatf("Avery fabric must compile as %0dx%0d, got %0dx%0d",
                  manager_vif_name.size(),
                  subordinate_vif_name.size(),
                  aaxi_pkg::AAXI_INTC_MASTER_CNT,
                  aaxi_pkg::AAXI_INTC_SLAVE_CNT))
    if (soc_manager_idx >= manager_vif_name.size() ||
        dma_manager_idx >= manager_vif_name.size())
      `uvm_fatal("AXI_FABRIC_CFG", "Manager index exceeds configured topology")
    if (soc_manager_idx == dma_manager_idx)
      `uvm_fatal("AXI_FABRIC_CFG", "Manager indexes must be unique")
    if (caliptra_subordinate_idx >= subordinate_vif_name.size() ||
        sram_subordinate_idx >= subordinate_vif_name.size() ||
        recovery_subordinate_idx >= subordinate_vif_name.size())
      `uvm_fatal("AXI_FABRIC_CFG",
        "Subordinate index exceeds configured topology")
    if (caliptra_subordinate_idx == sram_subordinate_idx ||
        caliptra_subordinate_idx == recovery_subordinate_idx ||
        sram_subordinate_idx == recovery_subordinate_idx)
      `uvm_fatal("AXI_FABRIC_CFG", "Subordinate indexes must be unique")
    if (aaxi_pkg::AAXI_ID_WIDTH != soc_ifc_pkg::CPTRA_AXI_DMA_ID_WIDTH)
      `uvm_fatal("AXI_FABRIC_CFG",
        $sformatf("Avery manager ID width %0d must match DMA ID width %0d",
                  aaxi_pkg::AAXI_ID_WIDTH,
                  soc_ifc_pkg::CPTRA_AXI_DMA_ID_WIDTH))
    if (aaxi_pkg::AAXI_INTC_ID_WIDTH != soc_ifc_pkg::SOC_IFC_ID_W)
      `uvm_fatal("AXI_FABRIC_CFG",
        $sformatf("Avery expanded ID width %0d must match Caliptra subordinate ID width %0d",
                  aaxi_pkg::AAXI_INTC_ID_WIDTH,
                  soc_ifc_pkg::SOC_IFC_ID_W))
    if (caliptra_limit_addr < caliptra_base_addr ||
        sram_config.limit_addr < sram_config.base_addr)
      `uvm_fatal("AXI_FABRIC_CFG", "Fabric address window has limit below base")
    if (!((caliptra_limit_addr < sram_config.base_addr) ||
          (sram_config.limit_addr < caliptra_base_addr)))
      `uvm_fatal("AXI_FABRIC_CFG", "Caliptra and SRAM windows overlap")
    if (recovery_config.fifo_data_addr inside {
          [caliptra_base_addr:caliptra_limit_addr],
          [sram_config.base_addr:sram_config.limit_addr]})
      `uvm_fatal("AXI_FABRIC_CFG", "Recovery FIFO address overlaps another window")
    if (recovery_config.depth_dwords == 0)
      `uvm_fatal("AXI_FABRIC_CFG", "Recovery FIFO depth must be nonzero")
    if (outstanding_depth <= 16)
      `uvm_fatal("AXI_FABRIC_CFG",
        $sformatf("Outstanding depth %0d cannot run response-pressure stress",
                  outstanding_depth))
    foreach (manager_vif_name[i])
      if (manager_vif_name[i] == "")
        `uvm_fatal("AXI_FABRIC_CFG",
          $sformatf("Manager virtual-interface name %0d is empty", i))
    foreach (subordinate_vif_name[i])
      if (subordinate_vif_name[i] == "")
        `uvm_fatal("AXI_FABRIC_CFG",
          $sformatf("Subordinate virtual-interface name %0d is empty", i))
    if (interconnect_vif_name == "")
      `uvm_fatal("AXI_FABRIC_CFG", "Interconnect virtual-interface name is empty")
  endfunction

endclass
