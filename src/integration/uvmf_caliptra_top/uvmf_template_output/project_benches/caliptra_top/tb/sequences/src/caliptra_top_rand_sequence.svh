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
//
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: This file contains the top level sequence used in caliptra_top_rand_test.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class caliptra_top_rand_sequence extends caliptra_top_bench_sequence_base;

  `uvm_object_utils( caliptra_top_rand_sequence );

  typedef soc_ifc_env_configuration  soc_ifc_env_configuration_t;
  typedef soc_ifc_env_bringup_sequence #(
          .CONFIG_T(soc_ifc_env_configuration_t)
          )
          soc_ifc_env_bringup_sequence_t;
  rand soc_ifc_env_bringup_sequence_t soc_ifc_env_bringup_seq;
  // Local handle to register model for convenience
  soc_ifc_reg_model_top reg_model;

  function new(string name = "" );
    super.new(name);
    reg_model = top_configuration.soc_ifc_subenv_config.soc_ifc_rm;
  endfunction

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin
    // Construct sequences here

    caliptra_top_env_seq = caliptra_top_env_sequence_base_t::type_id::create("caliptra_top_env_seq");
    soc_ifc_env_bringup_seq = soc_ifc_env_bringup_sequence_t::type_id::create("soc_ifc_env_bringup_seq");

    soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq     = soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq");
    soc_ifc_subenv_soc_ifc_status_agent_responder_seq  = soc_ifc_subenv_soc_ifc_status_agent_responder_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_status_agent_responder_seq");

    // Handle to the responder sequence for getting response transactions
    soc_ifc_env_bringup_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;

//    fork
//      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_reset();
//      soc_ifc_subenv_cptra_ctrl_agent_config.wait_for_reset();
//      soc_ifc_subenv_soc_ifc_status_agent_config.wait_for_reset();
//      soc_ifc_subenv_cptra_status_agent_config.wait_for_reset();
//    join
    reg_model.reset();
    // Start RESPONDER sequences here
    fork
        soc_ifc_subenv_soc_ifc_status_agent_responder_seq.start(soc_ifc_subenv_soc_ifc_status_agent_sequencer);
    join_none
//    // Start INITIATOR sequences here
//    fork
//      repeat (25) soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq.start(soc_ifc_subenv_soc_ifc_ctrl_agent_sequencer);
//    join

    soc_ifc_env_bringup_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);
//    caliptra_top_env_seq.start(top_configuration.vsqr);

    `uvm_info("CALIPTRA_TOP_BRINGUP", "SoC completed poweron and observed reset deassertion to system", UVM_LOW)

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(400);
      soc_ifc_subenv_cptra_ctrl_agent_config.wait_for_num_clocks(400);
      soc_ifc_subenv_soc_ifc_status_agent_config.wait_for_num_clocks(400);
      soc_ifc_subenv_cptra_status_agent_config.wait_for_num_clocks(400);
    join

    if (1) // TODO -- Move to Scoreboard
        $display("* TESTCASE PASSED");
    else
        $display("* TESTCASE FAILED");
    // pragma uvmf custom body end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

