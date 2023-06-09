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

//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: This file contains the top level sequence used in caliptra_top_cmdline_test.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class caliptra_top_cmdline_sequence extends caliptra_top_bench_sequence_base;

  `uvm_object_utils( caliptra_top_cmdline_sequence );

  rand soc_ifc_env_bringup_sequence_t soc_ifc_env_bringup_seq;
  rand soc_ifc_env_mbox_real_fw_sequence_t soc_ifc_env_mbox_fmc_seq;
  rand soc_ifc_env_mbox_real_fw_sequence_t soc_ifc_env_mbox_rt_seq;
  rand soc_ifc_env_sequence_base_t soc_ifc_env_seq_ii[];
  // Local handle to register model for convenience
  soc_ifc_reg_model_top reg_model;

  int sts_rsp_count = 0;

  function new(string name = "" );
    super.new(name);
    reg_model = top_configuration.soc_ifc_subenv_config.soc_ifc_rm;
  endfunction

  // ****************************************************************************
  virtual task run_firmware_init(soc_ifc_env_mbox_real_fw_sequence_t fmc_seq, soc_ifc_env_mbox_real_fw_sequence_t rt_seq);
    bit ready_for_fw = 0;
    bit ready_for_rt = 0;
    while (!ready_for_fw) begin
        while(!sts_rsp_count)soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(1); // Wait for new status updates
        `uvm_info("CALIPTRA_TOP_CMDLINE_TEST", "Observed status response, checking contents", UVM_DEBUG)
        sts_rsp_count = 0; // We only care about the latest rsp, so even if count > 1, reset back to 0
        ready_for_fw = soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.ready_for_fw_push;
    end
    if (!fmc_seq.randomize() with { fmc_seq.mbox_op_rand.cmd == mbox_cmd_e'(MBOX_CMD_FMC_UPDATE); })
        `uvm_fatal("CALIPTRA_TOP_CMDLINE_TEST", "caliptra_top_rand_sequence::body() - fmc_seq randomization failed")
    fmc_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);
    if (!rt_seq.randomize() with { rt_seq.mbox_op_rand.cmd == mbox_cmd_e'(MBOX_CMD_RT_UPDATE); })
        `uvm_fatal("CALIPTRA_TOP_CMDLINE_TEST", "caliptra_top_rand_sequence::body() - rt_seq randomization failed")
    rt_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

    // Wait for RT image to set the ready_for_rt bit
    while (!ready_for_rt) begin
        while(!sts_rsp_count)soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(1); // Wait for new status updates
        `uvm_info("CALIPTRA_TOP_CMDLINE_TEST", "Observed status response, checking contents", UVM_DEBUG)
        sts_rsp_count = 0; // We only care about the latest rsp, so even if count > 1, reset back to 0
        ready_for_rt = soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.ready_for_runtime;
    end
  endtask

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin
    // Construct sequences here
    uvm_object obj;
    uvm_cmdline_processor clp;
    string seq_names[$];
    int ii;

    caliptra_top_env_seq = caliptra_top_env_sequence_base_t::type_id::create("caliptra_top_env_seq");
    soc_ifc_env_bringup_seq = soc_ifc_env_bringup_sequence_t::type_id::create("soc_ifc_env_bringup_seq");
    soc_ifc_env_mbox_fmc_seq = soc_ifc_env_mbox_real_fw_sequence_t::type_id::create("soc_ifc_env_mbox_fmc_seq");
    soc_ifc_env_mbox_rt_seq = soc_ifc_env_mbox_real_fw_sequence_t::type_id::create("soc_ifc_env_mbox_rt_seq");

    soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq     = soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq");
    soc_ifc_subenv_soc_ifc_status_agent_responder_seq  = soc_ifc_subenv_soc_ifc_status_agent_responder_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_status_agent_responder_seq");

    // Handle to the responder sequence for getting response transactions
    soc_ifc_env_bringup_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_mbox_fmc_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_mbox_rt_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;

    reg_model.reset();
    // Start RESPONDER sequences here
    fork
        soc_ifc_subenv_soc_ifc_status_agent_responder_seq.start(soc_ifc_subenv_soc_ifc_status_agent_sequencer);
    join_none

    fork
        forever @(soc_ifc_subenv_soc_ifc_status_agent_responder_seq.new_rsp) sts_rsp_count++;
    join_none

    // Start INITIATOR sequences here
    if(!soc_ifc_env_bringup_seq.randomize())
        `uvm_fatal("CALIPTRA_TOP_CMDLINE_TEST", "caliptra_top_rand_sequence::body() - soc_ifc_env_bringup_seq randomization failed")
    soc_ifc_env_bringup_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

    `uvm_info("CALIPTRA_TOP_BRINGUP", "SoC completed poweron and observed reset deassertion to system", UVM_LOW)

    run_firmware_init(soc_ifc_env_mbox_fmc_seq,soc_ifc_env_mbox_rt_seq);

    // Run cmdline provided env sequences
    clp = uvm_cmdline_processor::get_inst();
    if (!clp.get_arg_values("+CLP_SEQ=", seq_names))
        `uvm_fatal("CALIPTRA_TOP_CMDLINE_TEST", "No cmdline sequence name arguments provided to cmdline test!")
    else
        soc_ifc_env_seq_ii = new[seq_names.size()];

    for (ii = 0; ii < seq_names.size(); ii++) begin: CMDLINE_LOOP

        if (seq_names[ii] == "CLP_RERUN_FW_INIT") begin
            soc_ifc_env_mbox_fmc_seq = soc_ifc_env_mbox_real_fw_sequence_t::type_id::create($sformatf("soc_ifc_env_mbox_fmc_seq[%0d]",ii));
            soc_ifc_env_mbox_rt_seq = soc_ifc_env_mbox_real_fw_sequence_t::type_id::create($sformatf("soc_ifc_env_mbox_rt_seq[%0d]",ii));
            soc_ifc_env_mbox_fmc_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
            soc_ifc_env_mbox_rt_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
            run_firmware_init(soc_ifc_env_mbox_fmc_seq,soc_ifc_env_mbox_rt_seq);
        end
        else begin
            // Create a new sequence instance of the provided type
            obj = factory.create_object_by_name(seq_names[ii], this.get_full_name(), $sformatf("%s[%0d]",seq_names[ii], ii));
            if (obj == null)
                `uvm_fatal("CALIPTRA_TOP_CMDLINE_TEST", $sformatf("caliptra_top_cmdline_sequence::body() - factory.create_object_by_name(%s) returned null", seq_names[ii]))

            // Randomize and run the sequence
            if(!$cast(soc_ifc_env_seq_ii[ii],obj))
                `uvm_fatal("CALIPTRA_TOP_CMDLINE_TEST", $sformatf("caliptra_top_cmdline_sequence::body() - factory.create_object_by_name(%s) returned invalid object", seq_names[ii]))
            `uvm_info("CALIPTRA_TOP_CMDLINE_TEST", $sformatf("running seq: %s", soc_ifc_env_seq_ii[ii].get_type_name()), UVM_MEDIUM)
            if(!soc_ifc_env_seq_ii[ii].randomize())
                `uvm_fatal("CALIPTRA_TOP_CMDLINE_TEST", $sformatf("caliptra_top_cmdline_sequence::body() - %s randomization failed", soc_ifc_env_seq_ii[ii].get_type_name()));
            soc_ifc_env_seq_ii[ii].soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
            soc_ifc_env_seq_ii[ii].start(top_configuration.soc_ifc_subenv_config.vsqr);
        end
    end

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(400);
      soc_ifc_subenv_cptra_ctrl_agent_config.wait_for_num_clocks(400);
      soc_ifc_subenv_soc_ifc_status_agent_config.wait_for_num_clocks(400);
      soc_ifc_subenv_cptra_status_agent_config.wait_for_num_clocks(400);
    join

    // pragma uvmf custom body end
  endtask

endclass
