// SPDX-License-Identifier: Apache-2.0

package soc_ifc_axi_topology_pkg;

  parameter int unsigned AXI_FABRIC_SOC_MANAGER_IDX = 0;
  parameter int unsigned AXI_FABRIC_DMA_MANAGER_IDX = 1;
  parameter int unsigned AXI_FABRIC_NUM_MANAGERS = 2;
  parameter int unsigned AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX = 0;
  parameter int unsigned AXI_FABRIC_SRAM_SUBORDINATE_IDX = 1;
  parameter int unsigned AXI_FABRIC_RECOVERY_SUBORDINATE_IDX = 2;
  parameter int unsigned AXI_FABRIC_NUM_SUBORDINATES = 3;

  parameter string AXI_FABRIC_SOC_MANAGER_VIF = "soc_ifc_axi_fabric_soc_manager_vif";
  parameter string AXI_FABRIC_DMA_MANAGER_VIF = "soc_ifc_axi_fabric_dma_manager_vif";
  parameter string AXI_FABRIC_CALIPTRA_SUBORDINATE_VIF = "soc_ifc_axi_fabric_caliptra_subordinate_vif";
  parameter string AXI_FABRIC_SRAM_SUBORDINATE_VIF = "soc_ifc_axi_fabric_sram_subordinate_vif";
  parameter string AXI_FABRIC_RECOVERY_SUBORDINATE_VIF = "soc_ifc_axi_fabric_recovery_subordinate_vif";
  parameter string AXI_FABRIC_INTERCONNECT_VIF = "soc_ifc_axi_fabric_interconnect_vif";

endpackage
