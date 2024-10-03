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
// DESCRIPTION: This environment contains all agents, predictors and
// scoreboards required for the block level design.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class fuse_ctrl_environment  extends uvmf_environment_base #(
    .CONFIG_T( fuse_ctrl_env_configuration 
  ));
  `uvm_component_utils( fuse_ctrl_environment )





  typedef fuse_ctrl_rst_agent  fuse_ctrl_rst_agent_t;
  fuse_ctrl_rst_agent_t fuse_ctrl_rst_agent;

  typedef fuse_ctrl_core_axi_write_if_agent  fuse_ctrl_core_axi_write_agent_t;
  fuse_ctrl_core_axi_write_agent_t fuse_ctrl_core_axi_write_agent;

  typedef fuse_ctrl_prim_axi_write_if_agent  fuse_ctrl_prim_axi_write_agent_t;
  fuse_ctrl_prim_axi_write_agent_t fuse_ctrl_prim_axi_write_agent;

  typedef fuse_ctrl_core_axi_read_if_agent  fuse_ctrl_core_axi_read_agent_t;
  fuse_ctrl_core_axi_read_agent_t fuse_ctrl_core_axi_read_agent;

  typedef fuse_ctrl_prim_axi_read_if_agent  fuse_ctrl_prim_axi_read_agent_t;
  fuse_ctrl_prim_axi_read_agent_t fuse_ctrl_prim_axi_read_agent;

  typedef fuse_ctrl_secreg_axi_read_if_agent  fuse_ctrl_secreg_axi_read_agent_t;
  fuse_ctrl_secreg_axi_read_agent_t fuse_ctrl_secreg_axi_read_agent;

  typedef fuse_ctrl_lc_otp_if_agent  fuse_ctrl_lc_otp_if_agent_t;
  fuse_ctrl_lc_otp_if_agent_t fuse_ctrl_lc_otp_if_agent;




  typedef fuse_ctrl_predictor #(
                .CONFIG_T(CONFIG_T)
                )
 fuse_ctrl_pred_t;
  fuse_ctrl_pred_t fuse_ctrl_pred;
  typedef fuse_ctrl_scoreboard #(
                .CONFIG_T(CONFIG_T)
                )
 fuse_ctrl_sb_t;
  fuse_ctrl_sb_t fuse_ctrl_sb;




  typedef uvmf_virtual_sequencer_base #(.CONFIG_T(fuse_ctrl_env_configuration)) fuse_ctrl_vsqr_t;
  fuse_ctrl_vsqr_t vsqr;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
 
// ****************************************************************************
// FUNCTION : new()
// This function is the standard SystemVerilog constructor.
//
  function new( string name = "", uvm_component parent = null );
    super.new( name, parent );
  endfunction

// ****************************************************************************
// FUNCTION: build_phase()
// This function builds all components within this environment.
//
  virtual function void build_phase(uvm_phase phase);
// pragma uvmf custom build_phase_pre_super begin
// pragma uvmf custom build_phase_pre_super end
    super.build_phase(phase);
    fuse_ctrl_rst_agent = fuse_ctrl_rst_agent_t::type_id::create("fuse_ctrl_rst_agent",this);
    fuse_ctrl_rst_agent.set_config(configuration.fuse_ctrl_rst_agent_config);
    fuse_ctrl_core_axi_write_agent = fuse_ctrl_core_axi_write_agent_t::type_id::create("fuse_ctrl_core_axi_write_agent",this);
    fuse_ctrl_core_axi_write_agent.set_config(configuration.fuse_ctrl_core_axi_write_agent_config);
    fuse_ctrl_prim_axi_write_agent = fuse_ctrl_prim_axi_write_agent_t::type_id::create("fuse_ctrl_prim_axi_write_agent",this);
    fuse_ctrl_prim_axi_write_agent.set_config(configuration.fuse_ctrl_prim_axi_write_agent_config);
    fuse_ctrl_core_axi_read_agent = fuse_ctrl_core_axi_read_agent_t::type_id::create("fuse_ctrl_core_axi_read_agent",this);
    fuse_ctrl_core_axi_read_agent.set_config(configuration.fuse_ctrl_core_axi_read_agent_config);
    fuse_ctrl_prim_axi_read_agent = fuse_ctrl_prim_axi_read_agent_t::type_id::create("fuse_ctrl_prim_axi_read_agent",this);
    fuse_ctrl_prim_axi_read_agent.set_config(configuration.fuse_ctrl_prim_axi_read_agent_config);
    fuse_ctrl_secreg_axi_read_agent = fuse_ctrl_secreg_axi_read_agent_t::type_id::create("fuse_ctrl_secreg_axi_read_agent",this);
    fuse_ctrl_secreg_axi_read_agent.set_config(configuration.fuse_ctrl_secreg_axi_read_agent_config);
    fuse_ctrl_lc_otp_if_agent = fuse_ctrl_lc_otp_if_agent_t::type_id::create("fuse_ctrl_lc_otp_if_agent",this);
    fuse_ctrl_lc_otp_if_agent.set_config(configuration.fuse_ctrl_lc_otp_if_agent_config);
    fuse_ctrl_pred = fuse_ctrl_pred_t::type_id::create("fuse_ctrl_pred",this);
    fuse_ctrl_pred.configuration = configuration;
    fuse_ctrl_sb = fuse_ctrl_sb_t::type_id::create("fuse_ctrl_sb",this);
    fuse_ctrl_sb.configuration = configuration;

    vsqr = fuse_ctrl_vsqr_t::type_id::create("vsqr", this);
    vsqr.set_config(configuration);
    configuration.set_vsqr(vsqr);

    // pragma uvmf custom build_phase begin
    // pragma uvmf custom build_phase end
  endfunction

// ****************************************************************************
// FUNCTION: connect_phase()
// This function makes all connections within this environment.  Connections
// typically inclue agent to predictor, predictor to scoreboard and scoreboard
// to agent.
//
  virtual function void connect_phase(uvm_phase phase);
// pragma uvmf custom connect_phase_pre_super begin
// pragma uvmf custom connect_phase_pre_super end
    super.connect_phase(phase);
    fuse_ctrl_rst_agent.monitored_ap.connect(fuse_ctrl_pred.fuse_ctrl_rst_agent_ae);
    fuse_ctrl_pred.fuse_ctrl_sb_ap.connect(fuse_ctrl_sb.expected_analysis_export);
    fuse_ctrl_core_axi_read_agent.monitored_ap.connect(fuse_ctrl_sb.actual_analysis_export);
    fuse_ctrl_prim_axi_read_agent.monitored_ap.connect(fuse_ctrl_sb.actual_analysis_export);
    fuse_ctrl_secreg_axi_read_agent.monitored_ap.connect(fuse_ctrl_sb.actual_analysis_export);
    fuse_ctrl_lc_otp_if_agent.monitored_ap.connect(fuse_ctrl_sb.actual_analysis_export);
    // pragma uvmf custom reg_model_connect_phase begin
    // pragma uvmf custom reg_model_connect_phase end
  endfunction

// ****************************************************************************
// FUNCTION: end_of_simulation_phase()
// This function is executed just prior to executing run_phase.  This function
// was added to the environment to sample environment configuration settings
// just before the simulation exits time 0.  The configuration structure is 
// randomized in the build phase before the environment structure is constructed.
// Configuration variables can be customized after randomization in the build_phase
// of the extended test.
// If a sequence modifies values in the configuration structure then the sequence is
// responsible for sampling the covergroup in the configuration if required.
//
  virtual function void start_of_simulation_phase(uvm_phase phase);
     configuration.fuse_ctrl_configuration_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

