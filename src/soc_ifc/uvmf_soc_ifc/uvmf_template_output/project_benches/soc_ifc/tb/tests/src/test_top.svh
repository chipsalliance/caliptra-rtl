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

class test_top extends uvmf_test_base #(.CONFIG_T(soc_ifc_env_configuration_t), 
                                        .ENV_T(soc_ifc_environment_t), 
                                        .TOP_LEVEL_SEQ_T(soc_ifc_bench_sequence_base));

  `uvm_component_utils( test_top );

// This message handler can be used to redirect QVIP Memeory Model messages through
// the UVM messaging mecahanism.  How to enable and use it is described in 
//      $UVMF_HOME/common/utility_packages/qvip_utils_pkg/src/qvip_report_catcher.svh
qvip_memory_message_handler message_handler;


  string interface_names[] = {
    uvm_test_top_environment_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0 /* ahb_lite_slave_0     [0] */ , 
    soc_ifc_ctrl_agent_BFM /* soc_ifc_ctrl_agent     [1] */ , 
    cptra_ctrl_agent_BFM /* cptra_ctrl_agent     [2] */ , 
    ss_mode_ctrl_agent_BFM /* ss_mode_ctrl_agent     [3] */ , 
    soc_ifc_status_agent_BFM /* soc_ifc_status_agent     [4] */ , 
    cptra_status_agent_BFM /* cptra_status_agent     [5] */ , 
    ss_mode_status_agent_BFM /* ss_mode_status_agent     [6] */ , 
    mbox_sram_agent_BFM /* mbox_sram_agent     [7] */ 
};

uvmf_active_passive_t interface_activities[] = { 
    ACTIVE /* ahb_lite_slave_0     [0] */ , 
    ACTIVE /* soc_ifc_ctrl_agent     [1] */ , 
    ACTIVE /* cptra_ctrl_agent     [2] */ , 
    ACTIVE /* ss_mode_ctrl_agent     [3] */ , 
    ACTIVE /* soc_ifc_status_agent     [4] */ , 
    ACTIVE /* cptra_status_agent     [5] */ , 
    ACTIVE /* ss_mode_status_agent     [6] */ , 
    ACTIVE /* mbox_sram_agent     [7] */   };

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  // ****************************************************************************
  // FUNCTION: new()
  // This is the standard systemVerilog constructor.  All components are 
  // constructed in the build_phase to allow factory overriding.
  //
  function new( string name = "", uvm_component parent = null );
     super.new( name ,parent );
  endfunction



  // ****************************************************************************
  // FUNCTION: build_phase()
  // The construction of the configuration and environment classes is done in
  // the build_phase of uvmf_test_base.  Once the configuraton and environment
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
    configuration.configure_axi_endpoints(
      .soc_ifc_base_addr(AXI_SOC_IFC_BASE_ADDR),
      .soc_ifc_limit_addr(AXI_SOC_IFC_LIMIT_ADDR),
      .sram_base_addr(AXI_SRAM_BASE_ADDR),
      .sram_size_bytes(AXI_SRAM_SIZE_BYTES),
      .sram_word_bytes(AXI_SRAM_WORD_BYTES),
      .recovery_fifo_addr(AXI_RECOVERY_FIFO_ADDR),
      .recovery_fifo_depth_dwords_default(AXI_RECOVERY_FIFO_DEPTH_DWORDS_DEFAULT),
      .outstanding_depth(AXI_FABRIC_OUTSTANDING_DEPTH),
      .sram_b_delay_min_default(AXI_SRAM_B_DELAY_MIN_DEFAULT),
      .sram_b_delay_max_default(AXI_SRAM_B_DELAY_MAX_DEFAULT),
      .sram_r_delay_min_default(AXI_SRAM_R_DELAY_MIN_DEFAULT),
      .sram_r_delay_max_default(AXI_SRAM_R_DELAY_MAX_DEFAULT),
      .recovery_r_delay_min_default(AXI_RECOVERY_R_DELAY_MIN_DEFAULT),
      .recovery_r_delay_max_default(AXI_RECOVERY_R_DELAY_MAX_DEFAULT),
      .recovery_refill_delay_min_default(AXI_RECOVERY_FIFO_REFILL_DELAY_MIN_DEFAULT),
      .recovery_refill_delay_max_default(AXI_RECOVERY_FIFO_REFILL_DELAY_MAX_DEFAULT));
    // pragma uvmf custom configuration_settings_post_randomize end
    configuration.initialize(NA, "uvm_test_top.environment", interface_names, null, interface_activities);
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

