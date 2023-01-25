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
// DESCRIPTION: This file contains the top level sequence used in  soc_ifc_rand_test.
// It is derived from the example_derived_test_sequence
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class soc_ifc_rand_test_sequence extends soc_ifc_bench_sequence_base;

  `uvm_object_utils( soc_ifc_rand_test_sequence );

    typedef soc_ifc_env_bringup_sequence #(
            .CONFIG_T(soc_ifc_env_configuration_t)
            )
            soc_ifc_env_bringup_sequence_t;
    rand soc_ifc_env_bringup_sequence_t soc_ifc_env_bringup_seq;
    typedef soc_ifc_env_cptra_rst_wait_sequence #(
            .CONFIG_T(soc_ifc_env_configuration_t)
            )
            soc_ifc_env_cptra_rst_wait_sequence_t;
    rand soc_ifc_env_cptra_rst_wait_sequence_t soc_ifc_env_cptra_rst_wait_seq;

  function new(string name = "" );
    super.new(name);
  endfunction

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin
    // Construct sequences here

    soc_ifc_env_bringup_seq        = soc_ifc_env_bringup_sequence_t::type_id::create("soc_ifc_env_bringup_seq");
    soc_ifc_env_cptra_rst_wait_seq = soc_ifc_env_cptra_rst_wait_sequence_t::type_id::create("soc_ifc_env_cptra_rst_wait_seq");

    soc_ifc_ctrl_agent_random_seq      = soc_ifc_ctrl_agent_random_seq_t::type_id::create("soc_ifc_ctrl_agent_random_seq");
    cptra_ctrl_agent_random_seq        = cptra_ctrl_agent_random_seq_t::type_id::create("cptra_ctrl_agent_random_seq");
    soc_ifc_status_agent_responder_seq = soc_ifc_status_agent_responder_seq_t::type_id::create("soc_ifc_status_agent_responder_seq");
    cptra_status_agent_responder_seq   = cptra_status_agent_responder_seq_t::type_id::create("cptra_status_agent_responder_seq");

    // Handle to the responder sequence for getting response transactions
    soc_ifc_env_bringup_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_status_agent_responder_seq;
    soc_ifc_env_cptra_rst_wait_seq.cptra_status_agent_rsp_seq = cptra_status_agent_responder_seq;

//    fork
//      soc_ifc_ctrl_agent_config.wait_for_reset();
//      cptra_ctrl_agent_config.wait_for_reset();
//      soc_ifc_status_agent_config.wait_for_reset();
//      cptra_status_agent_config.wait_for_reset();
//    join
    reg_model.reset();
    // Start RESPONDER sequences here
    fork
        soc_ifc_status_agent_responder_seq.start(soc_ifc_status_agent_sequencer);
        cptra_status_agent_responder_seq.start(cptra_status_agent_sequencer);
    join_none
//    // Start INITIATOR sequences here
//    fork
//      repeat (25) soc_ifc_ctrl_agent_random_seq.start(soc_ifc_ctrl_agent_sequencer);
//      repeat (25) cptra_ctrl_agent_random_seq.start(cptra_ctrl_agent_sequencer);
//    join

    if (!soc_ifc_env_bringup_seq.randomize()) `uvm_fatal("SEQ", "soc_ifc_rand_test_sequence::body() - soc_ifc_env_bringup_seq randomization failed");
    soc_ifc_env_bringup_seq.start(top_configuration.vsqr);

    // Wait for Caliptra system reset to be deasserted by SOC_IFC
    soc_ifc_env_cptra_rst_wait_seq.start(top_configuration.vsqr);
    `uvm_info("SOC_IFC_RAND_TEST", "Mailbox completed poweron and observed reset deassertion to system", UVM_LOW)

    // TODO watch for UC reset to deassert? Requires fw reset deassertion...

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      soc_ifc_ctrl_agent_config.wait_for_num_clocks(400);
      cptra_ctrl_agent_config.wait_for_num_clocks(400);
      soc_ifc_status_agent_config.wait_for_num_clocks(400);
      cptra_status_agent_config.wait_for_num_clocks(400);
    join

    if (1) // TODO -- how to properly choose which to print?
        $display("* TESTCASE PASSED");
    else
        $display("* TESTCASE FAILED");
    // pragma uvmf custom body end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

