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

class caliptra_top_environment  extends uvmf_environment_base #(
    .CONFIG_T( caliptra_top_env_configuration 
  ));
  `uvm_component_utils( caliptra_top_environment )

  typedef soc_ifc_environment soc_ifc_subenv_t;
  soc_ifc_subenv_t soc_ifc_subenv;
   











  typedef uvmf_virtual_sequencer_base #(.CONFIG_T(caliptra_top_env_configuration)) caliptra_top_vsqr_t;
  caliptra_top_vsqr_t vsqr;

  // pragma uvmf custom class_item_additional begin
  bit can_handle_reset = 1'b1;
  extern task          detect_reset();
  extern function void set_can_handle_reset(bit en = 1'b1);
  extern task          handle_reset(string kind = "HARD");
  extern task          run_phase(uvm_phase phase);
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
    soc_ifc_subenv = soc_ifc_subenv_t::type_id::create("soc_ifc_subenv",this);
    soc_ifc_subenv.set_config(configuration.soc_ifc_subenv_config);
    soc_ifc_subenv.set_can_handle_reset(1'b0);

    vsqr = caliptra_top_vsqr_t::type_id::create("vsqr", this);
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
     configuration.caliptra_top_configuration_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
task caliptra_top_environment::detect_reset();
    string kind = "SOFT";

    // Detect reset assertion from soc_ifc_ctrl_agent
    this.configuration.soc_ifc_subenv_config.soc_ifc_ctrl_agent_config.wait_for_reset_assertion(kind);

    // Handle
    this.handle_reset(kind);
endtask

// Called by a super-environment, if present, to bubble reset responsibility up
function void caliptra_top_environment::set_can_handle_reset(bit en = 1'b1);
    this.can_handle_reset = en;
endfunction

task caliptra_top_environment::handle_reset(string kind = "HARD");
    // Reset soc_ifc_environment
    this.soc_ifc_subenv.handle_reset(kind);

    // Reset any other agents (needed to reset monitor transaction keys)
    // Reset scoreboard according to kind
    // Reset predictor according to kind
endtask

task caliptra_top_environment::run_phase(uvm_phase phase);
    if (this.can_handle_reset) begin
        fork
            forever detect_reset();
        join
    end
endtask
// pragma uvmf custom external end

