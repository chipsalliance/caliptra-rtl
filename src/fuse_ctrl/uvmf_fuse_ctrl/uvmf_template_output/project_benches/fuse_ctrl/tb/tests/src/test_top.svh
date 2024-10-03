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

typedef fuse_ctrl_env_configuration fuse_ctrl_env_configuration_t;
typedef fuse_ctrl_environment fuse_ctrl_environment_t;

class test_top extends uvmf_test_base #(.CONFIG_T(fuse_ctrl_env_configuration_t), 
                                        .ENV_T(fuse_ctrl_environment_t), 
                                        .TOP_LEVEL_SEQ_T(fuse_ctrl_bench_sequence_base));

  `uvm_component_utils( test_top );



  string interface_names[] = {
    fuse_ctrl_rst_in_agent_BFM /* fuse_ctrl_rst_in_agent     [0] */ , 
    fuse_ctrl_rst_out_agent_BFM /* fuse_ctrl_rst_out_agent     [1] */ , 
    fuse_ctrl_core_axi_write_in_if_agent_BFM /* fuse_ctrl_core_axi_write_in_if_agent     [2] */ , 
    fuse_ctrl_core_axi_write_out_if_agent_BFM /* fuse_ctrl_core_axi_write_out_if_agent     [3] */ , 
    fuse_ctrl_prim_axi_write_in_if_agent_BFM /* fuse_ctrl_prim_axi_write_in_if_agent     [4] */ , 
    fuse_ctrl_prim_axi_write_out_if_agent_BFM /* fuse_ctrl_prim_axi_write_out_if_agent     [5] */ , 
    fuse_ctrl_core_axi_read_in_if_agent_BFM /* fuse_ctrl_core_axi_read_in_if_agent     [6] */ , 
    fuse_ctrl_core_axi_read_out_if_agent_BFM /* fuse_ctrl_core_axi_read_out_if_agent     [7] */ , 
    fuse_ctrl_prim_axi_read_in_if_agent_BFM /* fuse_ctrl_prim_axi_read_in_if_agent     [8] */ , 
    fuse_ctrl_prim_axi_read_out_if_agent_BFM /* fuse_ctrl_prim_axi_read_out_if_agent     [9] */ , 
    fuse_ctrl_secreg_axi_read_in_if_agent_BFM /* fuse_ctrl_secreg_axi_read_in_if_agent     [10] */ , 
    fuse_ctrl_secreg_axi_read_out_if_agent_BFM /* fuse_ctrl_secreg_axi_read_out_if_agent     [11] */ , 
    fuse_ctrl_lc_otp_in_if_agent_BFM /* fuse_ctrl_lc_otp_in_if_agent     [12] */ , 
    fuse_ctrl_lc_otp_out_if_agent_BFM /* fuse_ctrl_lc_otp_out_if_agent     [13] */ , 
    fuse_ctrl_in_if_agent_BFM /* fuse_ctrl_in_if_agent     [14] */ , 
    fuse_ctrl_out_if_agent_BFM /* fuse_ctrl_out_if_agent     [15] */ 
};

uvmf_active_passive_t interface_activities[] = { 
    ACTIVE /* fuse_ctrl_rst_in_agent     [0] */ , 
    PASSIVE /* fuse_ctrl_rst_out_agent     [1] */ , 
    ACTIVE /* fuse_ctrl_core_axi_write_in_if_agent     [2] */ , 
    PASSIVE /* fuse_ctrl_core_axi_write_out_if_agent     [3] */ , 
    ACTIVE /* fuse_ctrl_prim_axi_write_in_if_agent     [4] */ , 
    PASSIVE /* fuse_ctrl_prim_axi_write_out_if_agent     [5] */ , 
    ACTIVE /* fuse_ctrl_core_axi_read_in_if_agent     [6] */ , 
    PASSIVE /* fuse_ctrl_core_axi_read_out_if_agent     [7] */ , 
    ACTIVE /* fuse_ctrl_prim_axi_read_in_if_agent     [8] */ , 
    PASSIVE /* fuse_ctrl_prim_axi_read_out_if_agent     [9] */ , 
    ACTIVE /* fuse_ctrl_secreg_axi_read_in_if_agent     [10] */ , 
    PASSIVE /* fuse_ctrl_secreg_axi_read_out_if_agent     [11] */ , 
    ACTIVE /* fuse_ctrl_lc_otp_in_if_agent     [12] */ , 
    PASSIVE /* fuse_ctrl_lc_otp_out_if_agent     [13] */ , 
    ACTIVE /* fuse_ctrl_in_if_agent     [14] */ , 
    PASSIVE /* fuse_ctrl_out_if_agent     [15] */   };

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

