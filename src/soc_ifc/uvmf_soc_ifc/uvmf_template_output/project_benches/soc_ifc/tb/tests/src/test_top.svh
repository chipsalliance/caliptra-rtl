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
// Description: This top level UVM test is the base class for all
//     future tests created for this project.
//
//     This test class contains:
//          Configuration:  The top level configuration for the project.
//          Environment:    The top level environment for the project.
//          Top_level_sequence:  The top level sequence for the project.
//                                        
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

typedef soc_ifc_env_configuration soc_ifc_env_configuration_t;
typedef soc_ifc_environment soc_ifc_environment_t;

// Builds the soc_ifc environment and its bench-specific endpoint topology.
class test_top extends uvmf_test_base #(.CONFIG_T(soc_ifc_env_configuration_t), 
                                        .ENV_T(soc_ifc_environment_t), 
                                        .TOP_LEVEL_SEQ_T(soc_ifc_bench_sequence_base));

  `uvm_component_utils( test_top );

// This message handler can redirect QVIP memory-model messages through the UVM
// reporting mechanism. How to enable and use it is described in
//      $UVMF_HOME/common/utility_packages/qvip_utils_pkg/src/qvip_report_catcher.svh
qvip_memory_message_handler message_handler;


  string interface_names[] = {
    uvm_test_top_environment_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0 /* ahb_lite_slave_0     [0] */ , 
    uvm_test_top_environment_aaxi_tb_env0_master_0 /* aaxi_tb.env0.master[0] [1] */ , 
    soc_ifc_ctrl_agent_BFM /* soc_ifc_ctrl_agent     [2] */ , 
    cptra_ctrl_agent_BFM /* cptra_ctrl_agent     [3] */ , 
    ss_mode_ctrl_agent_BFM /* ss_mode_ctrl_agent     [4] */ , 
    soc_ifc_status_agent_BFM /* soc_ifc_status_agent     [5] */ , 
    cptra_status_agent_BFM /* cptra_status_agent     [6] */ , 
    ss_mode_status_agent_BFM /* ss_mode_status_agent     [7] */ , 
    mbox_sram_agent_BFM /* mbox_sram_agent     [8] */ 
};

uvmf_active_passive_t interface_activities[] = { 
    ACTIVE /* ahb_lite_slave_0     [0] */ , 
    ACTIVE /* aaxi_tb.env0.master[0] [1] */ , 
    ACTIVE /* soc_ifc_ctrl_agent     [2] */ , 
    ACTIVE /* cptra_ctrl_agent     [3] */ , 
    ACTIVE /* ss_mode_ctrl_agent     [4] */ , 
    ACTIVE /* soc_ifc_status_agent     [5] */ , 
    ACTIVE /* cptra_status_agent     [6] */ , 
    ACTIVE /* ss_mode_status_agent     [7] */ , 
    ACTIVE /* mbox_sram_agent     [8] */   };

  // pragma uvmf custom class_item_additional begin
  // Parse either one fixed-delay plusarg or a complete MIN/MAX pair. Reject
  // ambiguous combinations so every endpoint starts with one deterministic
  // delay policy before components are built.
  virtual function void parse_response_delay(
      input string prefix,
      input int unsigned default_min,
      input int unsigned default_max,
      output int unsigned delay_min,
      output int unsigned delay_max);
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
    has_fixed_delay = $value$plusargs(
      fixed_arg, fixed_delay);
    has_min_delay = $value$plusargs(
      min_arg, delay_min);
    has_max_delay = $value$plusargs(
      max_arg, delay_max);
    if (has_fixed_delay && (has_min_delay || has_max_delay))
      `uvm_fatal("AXI_FABRIC_CFG",
        $sformatf("%s cannot be combined with %s_MIN or %s_MAX",
                  prefix, prefix, prefix))
    if (has_min_delay != has_max_delay)
      `uvm_fatal("AXI_FABRIC_CFG",
        $sformatf("%s_MIN and %s_MAX must be specified together",
                  prefix, prefix))
    if (has_fixed_delay) begin
      delay_min = fixed_delay;
      delay_max = fixed_delay;
    end
    if (delay_min > delay_max)
      `uvm_fatal("AXI_FABRIC_CFG",
        $sformatf("%s minimum %0d exceeds maximum %0d",
                  prefix, delay_min, delay_max))
  endfunction

  // Convert bench parameters and plusargs into declarative endpoint configs.
  // This is the only layer that depends on bench parameter names; reusable
  // environment components consume typed configuration objects.
  virtual function void build_endpoint_configurations();
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

    parse_response_delay(
      "AXI_SRAM_B_DELAY",
      AXI_SRAM_B_DELAY_MIN_DEFAULT,
      AXI_SRAM_B_DELAY_MAX_DEFAULT,
      sram_b_delay_min, sram_b_delay_max);
    parse_response_delay(
      "AXI_SRAM_R_DELAY",
      AXI_SRAM_R_DELAY_MIN_DEFAULT,
      AXI_SRAM_R_DELAY_MAX_DEFAULT,
      sram_r_delay_min, sram_r_delay_max);
    parse_response_delay(
      "AXI_RECOVERY_R_DELAY",
      AXI_RECOVERY_R_DELAY_MIN_DEFAULT,
      AXI_RECOVERY_R_DELAY_MAX_DEFAULT,
      recovery_r_delay_min, recovery_r_delay_max);
    parse_response_delay(
      "AXI_RECOVERY_FIFO_REFILL_DELAY",
      AXI_RECOVERY_FIFO_REFILL_DELAY_MIN_DEFAULT,
      AXI_RECOVERY_FIFO_REFILL_DELAY_MAX_DEFAULT,
      recovery_refill_delay_min,
      recovery_refill_delay_max);
    recovery_fifo_depth_dwords =
      AXI_RECOVERY_FIFO_DEPTH_DWORDS_DEFAULT;
    void'($value$plusargs(
      "AXI_RECOVERY_FIFO_DEPTH_DWORDS=%d",
      recovery_fifo_depth_dwords));

    configuration.axi_sram_config.configure(
      AXI_SRAM_BASE_ADDR,
      AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES - 1,
      AXI_SRAM_WORD_BYTES,
      sram_b_delay_min, sram_b_delay_max,
      sram_r_delay_min, sram_r_delay_max);

    if (!uvm_config_db #(virtual soc_ifc_recovery_if)::get(
          null, UVMF_VIRTUAL_INTERFACES,
          soc_ifc_env_pkg::SOC_IFC_RECOVERY_VIF, recovery_vif))
      `uvm_fatal("RECOVERY_FIFO_CFG",
        "Unable to retrieve recovery FIFO virtual interface")
    configuration.recovery_fifo_config.configure(
      recovery_vif,
      AXI_RECOVERY_FIFO_ADDR,
      recovery_fifo_depth_dwords,
      recovery_r_delay_min,
      recovery_r_delay_max,
      recovery_refill_delay_min,
      recovery_refill_delay_max);
  endfunction

  // Describe topology and address ownership before the environment is built.
  // The fabric component later validates these windows against compile-time
  // Avery port counts and ID widths.
  virtual function void build_axi_fabric_configuration();
    string manager_vif_name[AXI_FABRIC_NUM_MANAGERS];
    string subordinate_vif_name[AXI_FABRIC_NUM_SUBORDINATES];

    manager_vif_name[AXI_FABRIC_SOC_MANAGER_IDX] =
      AXI_FABRIC_SOC_MANAGER_VIF;
    manager_vif_name[AXI_FABRIC_DMA_MANAGER_IDX] =
      AXI_FABRIC_DMA_MANAGER_VIF;
    subordinate_vif_name[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX] =
      AXI_FABRIC_CALIPTRA_SUBORDINATE_VIF;
    subordinate_vif_name[AXI_FABRIC_SRAM_SUBORDINATE_IDX] =
      AXI_FABRIC_SRAM_SUBORDINATE_VIF;
    subordinate_vif_name[AXI_FABRIC_RECOVERY_SUBORDINATE_IDX] =
      AXI_FABRIC_RECOVERY_SUBORDINATE_VIF;

    configuration.axi_fabric_config.configure(
      .manager_vif_name        (manager_vif_name),
      .subordinate_vif_name    (subordinate_vif_name),
      .interconnect_vif_name   (AXI_FABRIC_INTERCONNECT_VIF),
      .soc_manager_idx         (AXI_FABRIC_SOC_MANAGER_IDX),
      .dma_manager_idx         (AXI_FABRIC_DMA_MANAGER_IDX),
      .caliptra_subordinate_idx(AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX),
      .sram_subordinate_idx    (AXI_FABRIC_SRAM_SUBORDINATE_IDX),
      .recovery_subordinate_idx(AXI_FABRIC_RECOVERY_SUBORDINATE_IDX),
      .caliptra_base_addr      (64'h0),
      .caliptra_limit_addr     ((64'(1) << soc_ifc_pkg::SOC_IFC_ADDR_W) - 1),
      .sram_config             (configuration.axi_sram_config),
      .recovery_config         (configuration.recovery_fifo_config),
      .outstanding_depth       (AXI_FABRIC_OUTSTANDING_DEPTH));
  endfunction

  // pragma uvmf custom class_item_additional end

  // ****************************************************************************
  // FUNCTION: new()
  // This is the standard SystemVerilog constructor. All components are
  // constructed in the build_phase to allow factory overriding.
  //
  function new( string name = "", uvm_component parent = null );
     super.new( name ,parent );
  endfunction



  // ****************************************************************************
  // FUNCTION: build_phase()
  // The construction of the configuration and environment classes is done in
  // the build_phase of uvmf_test_base. Once the configuration and environment
  // classes are built then the initialize call is made to perform the
  // following: 
  //     Monitor and driver BFM virtual interface handle passing into agents
  //     Set the active/passive state for each agent
  // Once this build_phase completes, the build_phase of the environment is
  // executed which builds the agents.
  //
  virtual function void build_phase(uvm_phase phase);
// pragma uvmf custom build_phase_pre_super begin
// pragma uvmf custom build_phase_pre_super end
    super.build_phase(phase);
    // pragma uvmf custom configuration_settings_post_randomize begin
    build_endpoint_configurations();
    build_axi_fabric_configuration();
    `uvm_info("SOC_IFC_TEST_CFG",
      $sformatf(
        "Configured AXI SRAM [0x%0h:0x%0h], recovery FIFO address 0x%0h depth %0d DWORDs, fabric outstanding depth %0d",
        configuration.axi_sram_config.base_addr,
        configuration.axi_sram_config.limit_addr,
        configuration.recovery_fifo_config.fifo_data_addr,
        configuration.recovery_fifo_config.depth_dwords,
        configuration.axi_fabric_config.outstanding_depth), UVM_LOW)
    // pragma uvmf custom configuration_settings_post_randomize end
    configuration.initialize(NA, "uvm_test_top.environment", interface_names, null, interface_activities);
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
