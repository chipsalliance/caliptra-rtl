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

class soc_ifc_trng_test_sequence extends soc_ifc_bench_sequence_base;

    `uvm_object_utils( soc_ifc_trng_test_sequence );

    rand soc_ifc_env_bringup_sequence_t soc_ifc_env_bringup_seq;
    rand soc_ifc_env_cptra_rst_wait_sequence_t soc_ifc_env_cptra_rst_wait_seq; 
    rand soc_ifc_env_top_trng_sequence_t trng_top_test_seq;
    rand soc_ifc_env_sequence_base_t soc_ifc_env_seq_ii[];

    rand enum int {
        IDX_SOC_IFC_ENV_TRNG_TOP = 0,
        IDX_SOC_IFC_ENV_TRNG_TOP_RESET = 1
    } rand_seq_idx;

    rand int iteration_count;

    constraint avail_env_seqs_c {
        rand_seq_idx dist {
            IDX_SOC_IFC_ENV_TRNG_TOP       :/ 100
            //IDX_SOC_IFC_ENV_TRNG_TOP_RESET :/ 50
        };
    }

    // FIXME we're also running multiple iterations of this testcase in the regression.
    //       What is the criteria for iteration count WITHIN the sequence?
    constraint iter_count_c {
        iteration_count inside {[1:10]};
    }

  function new(string name = "");
    super.new(name);
    if ($value$plusargs("SOC_IFC_TRNG_ITER=%d", iteration_count)) begin
        `uvm_info("SOC_IFC_TRNG_TEST", $sformatf("Received Command Line Iteration Count Argument of %d", iteration_count), UVM_LOW);
        iteration_count.rand_mode(0);
        this.iter_count_c.constraint_mode(0);
    end
    else begin
        if (!this.randomize(iteration_count))
            `uvm_fatal("SOC_IFC_TRNG_TEST", "Failed to randomize iteration_count after receiving no command line override")
        else
            `uvm_info("SOC_IFC_TRNG_TEST", $sformatf("Did not receive Command Line Iteration Count Argument, defaulting to %d", iteration_count), UVM_LOW);
    end
    soc_ifc_env_seq_ii = new[iteration_count];
  endfunction

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin
    // Construct sequences here
    uvm_object obj;
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
            `uvm_fatal("SOC_IFC_TRNG_TEST", "soc_ifc_trng_test_sequence::body() - soc_ifc_env_bringup_seq randomization failed");
        soc_ifc_env_bringup_seq.start(top_configuration.vsqr);
    end
    begin
        // Wait for Caliptra system reset to be deasserted by SOC_IFC
        soc_ifc_env_cptra_rst_wait_seq.start(top_configuration.vsqr);
        `uvm_info("SOC_IFC_TRNG_TEST", "Mailbox completed poweron and observed reset deassertion to system", UVM_LOW)
    end
    join

    // Start randome TRNG test sequence

    for (ii = 0; ii < iteration_count; ii++) begin: RAND_LOOP
        if(!this.randomize(rand_seq_idx)) `uvm_fatal("SOC_IFC_TRNG_TEST", "Failed to randomize rand_seq_idx");

        // Create a new sequence instance of the randomized type
        case (rand_seq_idx) inside
            IDX_SOC_IFC_ENV_TRNG_TOP:
                obj = soc_ifc_env_top_trng_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%d]",ii));
            //IDX_SOC_IFC_ENV_TRNG_TOP_RESET:
            //    obj = soc_ifc_env_top_trng_reset_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%d]",ii));
            default:
                `uvm_error("SOC_IFC_TRNG_TEST", $sformatf("rand_seq_idx randomized to illegal value: %p", rand_seq_idx))
        endcase 

        if(!$cast(soc_ifc_env_seq_ii[ii],obj))
            `uvm_fatal("SOC_IFC_TRNG_TEST", "soc_ifc_trng_test_sequence::body() - <seq_type>.create_object() failed");
        soc_ifc_env_seq_ii[ii].soc_ifc_status_agent_rsp_seq = soc_ifc_status_agent_responder_seq;
        soc_ifc_env_seq_ii[ii].cptra_status_agent_rsp_seq = cptra_status_agent_responder_seq;
        soc_ifc_env_seq_ii[ii].start(top_configuration.vsqr);
    end

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
  
  endtask

endclass

    