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
// DESCRIPTION: This file contains the top level sequence used in
//              soc_ifc_cmdline_test to bringup the system then run
//              cmdline-provided sequences.
//              It is derived from the example_derived_test_sequence.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class soc_ifc_cmdline_test_sequence extends soc_ifc_bench_sequence_base;

  `uvm_object_utils( soc_ifc_cmdline_test_sequence );

  rand soc_ifc_env_bringup_sequence_t soc_ifc_env_bringup_seq;
  rand soc_ifc_env_cptra_rst_wait_sequence_t soc_ifc_env_cptra_rst_wait_seq;

  function new(string name = "" );
    super.new(name);
  endfunction

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin
    // Construct sequences here
    uvm_object obj;
    uvm_cmdline_processor clp;
    string seq_names[$];
    int ii;

    soc_ifc_env_bringup_seq        = soc_ifc_env_bringup_sequence_t::type_id::create("soc_ifc_env_bringup_seq");
    soc_ifc_env_cptra_rst_wait_seq = soc_ifc_env_cptra_rst_wait_sequence_t::type_id::create("soc_ifc_env_cptra_rst_wait_seq");

    soc_ifc_ctrl_agent_random_seq      = soc_ifc_ctrl_agent_random_seq_t::type_id::create("soc_ifc_ctrl_agent_random_seq");
    cptra_ctrl_agent_random_seq        = cptra_ctrl_agent_random_seq_t::type_id::create("cptra_ctrl_agent_random_seq");
    soc_ifc_status_agent_responder_seq = soc_ifc_status_agent_responder_seq_t::type_id::create("soc_ifc_status_agent_responder_seq");
    cptra_status_agent_responder_seq   = cptra_status_agent_responder_seq_t::type_id::create("cptra_status_agent_responder_seq");

    // Handle to the responder sequence for getting response transactions
    soc_ifc_env_bringup_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_status_agent_responder_seq;
    soc_ifc_env_cptra_rst_wait_seq.cptra_status_agent_rsp_seq = cptra_status_agent_responder_seq;

    reg_model.reset();
    // Start RESPONDER sequences here
    fork
        soc_ifc_status_agent_responder_seq.start(soc_ifc_status_agent_sequencer);
        cptra_status_agent_responder_seq.start(cptra_status_agent_sequencer);
    join_none

    // Start INITIATOR sequences here
    fork
    begin
        // Bringup (set pwrgood, deassert cptra_rst_b, write fuses)
        if(!soc_ifc_env_bringup_seq.randomize())
            `uvm_fatal("SOC_IFC_CMDLINE_TEST", "soc_ifc_cmdline_test_sequence::body() - soc_ifc_env_bringup_seq randomization failed");
        soc_ifc_env_bringup_seq.start(top_configuration.vsqr);
    end
    begin
        // Wait for Caliptra system reset to be deasserted by SOC_IFC
        soc_ifc_env_cptra_rst_wait_seq.start(top_configuration.vsqr);
        `uvm_info("SOC_IFC_CMDLINE_TEST", "Mailbox completed poweron and observed reset deassertion to system", UVM_LOW)
    end
    join

    // Run cmdline provided env sequences
    clp = uvm_cmdline_processor::get_inst();
    if (!clp.get_arg_values("+CLP_SEQ=", seq_names))
        `uvm_fatal("SOC_IFC_CMDLINE_TEST", "No cmdline sequence name arguments provided to cmdline test!")

    for (ii = 0; ii < seq_names.size(); ii++) begin: CMDLINE_LOOP

        // Create a new sequence instance of the provided type
        obj = factory.create_object_by_name(seq_names[ii], this.get_full_name(), $sformatf("%s[%0d]",seq_names[ii], ii));
        if (obj == null)
            `uvm_fatal("SOC_IFC_CMDLINE_TEST", $sformatf("soc_ifc_cmdline_test_sequence::body() - factory.create_object_by_name(%s) returned null", seq_names[ii]))

        // Randomize and run the sequence
        if(!$cast(soc_ifc_env_seq,obj))
            `uvm_fatal("SOC_IFC_CMDLINE_TEST", $sformatf("soc_ifc_cmdline_test_sequence::body() - factory.create_object_by_name(%s) returned invalid object", seq_names[ii]))
        `uvm_info("SOC_IFC_CMDLINE_TEST", $sformatf("running seq: %s", soc_ifc_env_seq.get_type_name()), UVM_MEDIUM)
        if(!soc_ifc_env_seq.randomize())
            `uvm_fatal("SOC_IFC_CMDLINE_TEST", $sformatf("soc_ifc_cmdline_test_sequence::body() - %s randomization failed", soc_ifc_env_seq.get_type_name()));
        soc_ifc_env_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_status_agent_responder_seq;
        soc_ifc_env_seq.cptra_status_agent_rsp_seq   = cptra_status_agent_responder_seq;
        soc_ifc_env_seq.start(top_configuration.vsqr);
    end

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      soc_ifc_ctrl_agent_config.wait_for_num_clocks(400);
      cptra_ctrl_agent_config.wait_for_num_clocks(400);
      soc_ifc_status_agent_config.wait_for_num_clocks(400);
      cptra_status_agent_config.wait_for_num_clocks(400);
    join

    // pragma uvmf custom body end
  endtask

endclass
