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

typedef kv_env_configuration kv_env_configuration_t;
typedef kv_environment kv_environment_t;

class test_top extends uvmf_test_base #(.CONFIG_T(kv_env_configuration_t), 
                                        .ENV_T(kv_environment_t), 
                                        .TOP_LEVEL_SEQ_T(kv_bench_sequence_base));

  `uvm_component_utils( test_top );

// This message handler can be used to redirect QVIP Memeory Model messages through
// the UVM messaging mecahanism.  How to enable and use it is described in 
//      $UVMF_HOME/common/utility_packages/qvip_utils_pkg/src/qvip_report_catcher.svh
qvip_memory_message_handler message_handler;


  string interface_names[] = {
    uvm_test_top_environment_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0 /* ahb_lite_slave_0     [0] */ , 
    kv_rst_agent_BFM /* kv_rst_agent     [1] */ , 
    kv_hmac_write_agent_BFM /* kv_hmac_write_agent     [2] */ , 
    kv_sha512_write_agent_BFM /* kv_sha512_write_agent     [3] */ , 
    kv_ecc_write_agent_BFM /* kv_ecc_write_agent     [4] */ , 
    kv_doe_write_agent_BFM /* kv_doe_write_agent     [5] */ , 
    kv_hmac_key_read_agent_BFM /* kv_hmac_key_read_agent     [6] */ , 
    kv_hmac_block_read_agent_BFM /* kv_hmac_block_read_agent     [7] */ , 
    kv_sha512_block_read_agent_BFM /* kv_sha512_block_read_agent     [8] */ , 
    kv_ecc_privkey_read_agent_BFM /* kv_ecc_privkey_read_agent     [9] */ , 
    kv_ecc_seed_read_agent_BFM /* kv_ecc_seed_read_agent     [10] */ 
};

uvmf_active_passive_t interface_activities[] = { 
    ACTIVE /* ahb_lite_slave_0     [0] */ , 
    ACTIVE /* kv_rst_agent     [1] */ , 
    ACTIVE /* kv_hmac_write_agent     [2] */ , 
    ACTIVE /* kv_sha512_write_agent     [3] */ , 
    ACTIVE /* kv_ecc_write_agent     [4] */ , 
    ACTIVE /* kv_doe_write_agent     [5] */ , 
    ACTIVE /* kv_hmac_key_read_agent     [6] */ , 
    ACTIVE /* kv_hmac_block_read_agent     [7] */ , 
    ACTIVE /* kv_sha512_block_read_agent     [8] */ , 
    ACTIVE /* kv_ecc_privkey_read_agent     [9] */ , 
    ACTIVE /* kv_ecc_seed_read_agent     [10] */
};

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

