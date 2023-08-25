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

typedef caliptra_top_env_configuration caliptra_top_env_configuration_t;
typedef caliptra_top_environment caliptra_top_environment_t;

class test_top extends uvmf_test_base #(.CONFIG_T(caliptra_top_env_configuration_t), 
                                        .ENV_T(caliptra_top_environment_t), 
                                        .TOP_LEVEL_SEQ_T(caliptra_top_bench_sequence_base));

  `uvm_component_utils( test_top );

// This message handler can be used to redirect QVIP Memeory Model messages through
// the UVM messaging mecahanism.  How to enable and use it is described in 
//      $UVMF_HOME/common/utility_packages/qvip_utils_pkg/src/qvip_report_catcher.svh
qvip_memory_message_handler message_handler;


  string interface_names[] = {
    uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0 /* ahb_lite_slave_0     [0] */ , 
    uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_apb5_master_0 /* apb5_master_0     [1] */ , 
    soc_ifc_subenv_soc_ifc_ctrl_agent_BFM /* soc_ifc_subenv_soc_ifc_ctrl_agent     [2] */ , 
    soc_ifc_subenv_cptra_ctrl_agent_BFM /* soc_ifc_subenv_cptra_ctrl_agent     [3] */ , 
    soc_ifc_subenv_soc_ifc_status_agent_BFM /* soc_ifc_subenv_soc_ifc_status_agent     [4] */ , 
    soc_ifc_subenv_cptra_status_agent_BFM /* soc_ifc_subenv_cptra_status_agent     [5] */ , 
    soc_ifc_subenv_mbox_sram_agent_BFM /* soc_ifc_subenv_mbox_sram_agent     [6] */ 
};

uvmf_active_passive_t interface_activities[] = { 
    PASSIVE /* ahb_lite_slave_0     [0] */ , 
    ACTIVE /* apb5_master_0     [1] */ , 
    ACTIVE /* soc_ifc_subenv_soc_ifc_ctrl_agent     [2] */ , 
    PASSIVE /* soc_ifc_subenv_cptra_ctrl_agent     [3] */ , 
    ACTIVE /* soc_ifc_subenv_soc_ifc_status_agent     [4] */ , 
    PASSIVE /* soc_ifc_subenv_cptra_status_agent     [5] */ ,
    ACTIVE /* soc_ifc_subenv_mbox_sram_agent     [6] */   };

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
    // pragma uvmf custom configuration_settings_post_randomize end
    configuration.initialize(NA, "uvm_test_top.environment", interface_names, null, interface_activities);
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

