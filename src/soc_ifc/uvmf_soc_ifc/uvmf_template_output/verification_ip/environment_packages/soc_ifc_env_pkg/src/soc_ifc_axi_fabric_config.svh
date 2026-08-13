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

  localparam int NUM_MANAGERS     = 2;
  localparam int NUM_SUBORDINATES = 3;

  string manager_vif_name[NUM_MANAGERS];
  string subordinate_vif_name[NUM_SUBORDINATES];
  string interconnect_vif_name;

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
      input string      soc_manager_vif_name,
      input string      dma_manager_vif_name,
      input string      caliptra_subordinate_vif_name,
      input string      sram_subordinate_vif_name,
      input string      recovery_subordinate_vif_name,
      input string      interconnect_vif_name,
      input aaxi_addr_t caliptra_base_addr,
      input aaxi_addr_t caliptra_limit_addr,
      input soc_ifc_axi_sram_config sram_config,
      input soc_ifc_recovery_fifo_config recovery_config,
      input int unsigned outstanding_depth);
    this.manager_vif_name[0]     = soc_manager_vif_name;
    this.manager_vif_name[1]     = dma_manager_vif_name;
    this.subordinate_vif_name[0] = caliptra_subordinate_vif_name;
    this.subordinate_vif_name[1] = sram_subordinate_vif_name;
    this.subordinate_vif_name[2] = recovery_subordinate_vif_name;
    this.interconnect_vif_name   = interconnect_vif_name;
    this.caliptra_base_addr      = caliptra_base_addr;
    this.caliptra_limit_addr     = caliptra_limit_addr;
    this.sram_config             = sram_config;
    this.recovery_config         = recovery_config;
    this.outstanding_depth       = outstanding_depth;
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
    if (aaxi_pkg::AAXI_INTC_MASTER_CNT != NUM_MANAGERS ||
        aaxi_pkg::AAXI_INTC_SLAVE_CNT != NUM_SUBORDINATES)
      `uvm_fatal("AXI_FABRIC_CFG",
        $sformatf("Avery fabric must compile as 2x3, got %0dx%0d",
                  aaxi_pkg::AAXI_INTC_MASTER_CNT,
                  aaxi_pkg::AAXI_INTC_SLAVE_CNT))
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
