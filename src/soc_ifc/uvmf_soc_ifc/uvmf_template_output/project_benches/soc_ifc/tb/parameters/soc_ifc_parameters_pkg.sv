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
// DESCRIPTION: This package contains test level parameters
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//


package soc_ifc_parameters_pkg;

  import uvmf_base_pkg_hdl::*;

  // pragma uvmf custom package_imports_additional begin 
  // pragma uvmf custom package_imports_additional end


  // These parameters are used to uniquely identify each interface.  The monitor_bfm and
  // driver_bfm are placed into and retrieved from the uvm_config_db using these string 
  // names as the field_name. The parameter is also used to enable transaction viewing 
  // from the command line for selected interfaces using the UVM command line processing.
  parameter string uvm_test_top_environment_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0  = "uvm_test_top.environment.qvip_ahb_lite_slave_subenv.ahb_lite_slave_0"; /* [0] */
  parameter string uvm_test_top_environment_aaxi_tb_env0_master_0  = "uvm_test_top.environment.axi_fabric.manager[0]"; /* [1] */
  parameter string soc_ifc_ctrl_agent_BFM  = "soc_ifc_ctrl_agent_BFM"; /* [2] */
  parameter string cptra_ctrl_agent_BFM  = "cptra_ctrl_agent_BFM"; /* [3] */
  parameter string ss_mode_ctrl_agent_BFM  = "ss_mode_ctrl_agent_BFM"; /* [4] */
  parameter string soc_ifc_status_agent_BFM  = "soc_ifc_status_agent_BFM"; /* [5] */
  parameter string cptra_status_agent_BFM  = "cptra_status_agent_BFM"; /* [6] */
  parameter string ss_mode_status_agent_BFM  = "ss_mode_status_agent_BFM"; /* [7] */
  parameter string mbox_sram_agent_BFM  = "mbox_sram_agent_BFM"; /* [8] */

  // pragma uvmf custom package_item_additional begin
  // AXI endpoint geometry is bench-owned. SRAM address width is the single
  // storage-size knob; word bytes come from soc_ifc_pkg so direct memory access
  // stride always matches the DUT DMA data width.
  parameter int AXI_SRAM_ADDR_WIDTH = 18; // 2**18 = 256KB window
  parameter int AXI_SRAM_WORD_BYTES = soc_ifc_pkg::CPTRA_AXI_DMA_DATA_WIDTH / 8;
  parameter longint unsigned AXI_SRAM_SIZE_BYTES = longint'(1) << AXI_SRAM_ADDR_WIDTH;
  parameter bit [63:0] AXI_SRAM_BASE_ADDR = 64'h8000_0000;
  parameter bit [63:0] AXI_RECOVERY_FIFO_ADDR = 64'h9000_0000;
  parameter int unsigned AXI_FABRIC_OUTSTANDING_DEPTH = 64;

  // Test configuration may override these defaults with endpoint plusargs.
  // Removing the _DEFAULT suffix yields the matching plusarg name, making the
  // startup value and external override relationship explicit.
  parameter int unsigned AXI_RECOVERY_FIFO_DEPTH_DWORDS_DEFAULT = 512;
  parameter int unsigned AXI_SRAM_B_DELAY_MIN_DEFAULT = 0;
  parameter int unsigned AXI_SRAM_B_DELAY_MAX_DEFAULT = 0;
  parameter int unsigned AXI_SRAM_R_DELAY_MIN_DEFAULT = 0;
  parameter int unsigned AXI_SRAM_R_DELAY_MAX_DEFAULT = 0;
  parameter int unsigned AXI_RECOVERY_R_DELAY_MIN_DEFAULT = 0;
  parameter int unsigned AXI_RECOVERY_R_DELAY_MAX_DEFAULT = 0;
  parameter int unsigned AXI_RECOVERY_FIFO_REFILL_DELAY_MIN_DEFAULT = 0;
  parameter int unsigned AXI_RECOVERY_FIFO_REFILL_DELAY_MAX_DEFAULT = 0;

  parameter int AXI_FABRIC_SOC_MANAGER_IDX = 0;
  parameter int AXI_FABRIC_DMA_MANAGER_IDX = 1;
  parameter int AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX = 0;
  parameter int AXI_FABRIC_SRAM_SUBORDINATE_IDX = 1;
  parameter int AXI_FABRIC_RECOVERY_SUBORDINATE_IDX = 2;

  parameter string AXI_FABRIC_SOC_MANAGER_VIF = "soc_ifc_axi_fabric_soc_manager_vif";
  parameter string AXI_FABRIC_DMA_MANAGER_VIF = "soc_ifc_axi_fabric_dma_manager_vif";
  parameter string AXI_FABRIC_CALIPTRA_SUBORDINATE_VIF = "soc_ifc_axi_fabric_caliptra_subordinate_vif";
  parameter string AXI_FABRIC_SRAM_SUBORDINATE_VIF = "soc_ifc_axi_fabric_sram_subordinate_vif";
  parameter string AXI_FABRIC_RECOVERY_SUBORDINATE_VIF = "soc_ifc_axi_fabric_recovery_subordinate_vif";
  parameter string AXI_FABRIC_INTERCONNECT_VIF = "soc_ifc_axi_fabric_interconnect_vif";
  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end
