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

  rand soc_ifc_env_bringup_sequence_t soc_ifc_env_bringup_seq;
  rand soc_ifc_env_pauser_init_sequence_t soc_ifc_env_pauser_init_seq;
  rand soc_ifc_env_mbox_real_fw_sequence_t soc_ifc_env_mbox_fmc_seq;
  rand soc_ifc_env_mbox_real_fw_sequence_t soc_ifc_env_mbox_rt_seq;
  rand soc_ifc_env_sequence_base_t soc_ifc_env_seq_ii[];
  rand soc_ifc_env_mbox_real_fw_sequence_t soc_ifc_env_mbox_fw_seq_ii[string];
  // Local handle to register model for convenience
  soc_ifc_reg_model_top reg_model;

  // TODO: To add new sequences to the randomized portion of this test:
  //        - Update rand_seq_idx enum definition
  //        - Update avail_env_seqs_c definition
  //        - Add instantiation logic in the RAND_LOOP below
  rand enum int {
      //IDX_SOC_IFC_ENV_MBOX_RAND_FW,
      IDX_SOC_IFC_ENV_MBOX_RAND_SMALL,
      IDX_SOC_IFC_ENV_MBOX_RAND_MEDIUM,
      IDX_SOC_IFC_ENV_MBOX_RAND_LARGE,
      IDX_SOC_IFC_ENV_MBOX_MIN,
      IDX_SOC_IFC_ENV_MBOX_MAX,
      IDX_SOC_IFC_ENV_MBOX_RAND_PAUSER_SMALL,
      IDX_SOC_IFC_ENV_MBOX_RAND_PAUSER_MEDIUM,
      IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_SMALL,
      IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_MEDIUM,
      IDX_SOC_IFC_ENV_MBOX_MULTI_AGENT,
      IDX_SOC_IFC_ENV_RST_WARM,
      IDX_SOC_IFC_ENV_RST_COLD,
      IDX_SOC_IFC_ENV_MBOX_RST_WARM_RAND_MEDIUM,
      IDX_SOC_IFC_ENV_MBOX_RST_COLD_RAND_MEDIUM,
      IDX_SOC_IFC_ENV_MBOX_SHA_ACCEL,
      IDX_SOC_IFC_ENV_SHA_ACCEL,
      IDX_SOC_IFC_ENV_FW_UPD,
      IDX_SOC_IFC_ENV_MBOX_UC_REG_ACCESS
  } rand_seq_idx;

  rand int iteration_count;
  int sts_rsp_count = 0;

  // Choose rand weights for each sequence to determine run frequency
  constraint avail_env_seqs_c {
      rand_seq_idx dist {
          //IDX_SOC_IFC_ENV_MBOX_RAND_FW            := 0,
          IDX_SOC_IFC_ENV_MBOX_RAND_SMALL           := 125,
          IDX_SOC_IFC_ENV_MBOX_RAND_MEDIUM          := 100,
          IDX_SOC_IFC_ENV_MBOX_RAND_LARGE           := 1,
          IDX_SOC_IFC_ENV_MBOX_MIN                  := 100,
          IDX_SOC_IFC_ENV_MBOX_MAX                  := 10,
          IDX_SOC_IFC_ENV_MBOX_RAND_PAUSER_SMALL    := 125,
          IDX_SOC_IFC_ENV_MBOX_RAND_PAUSER_MEDIUM   := 100,
          IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_SMALL     := 100,
          IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_MEDIUM    := 100,
          IDX_SOC_IFC_ENV_MBOX_MULTI_AGENT          := 100,
          IDX_SOC_IFC_ENV_RST_WARM                  := 100,
          IDX_SOC_IFC_ENV_RST_COLD                  := 100,
          IDX_SOC_IFC_ENV_MBOX_RST_WARM_RAND_MEDIUM := 100,
          IDX_SOC_IFC_ENV_MBOX_RST_COLD_RAND_MEDIUM := 100,
          IDX_SOC_IFC_ENV_MBOX_SHA_ACCEL            := 100,
          IDX_SOC_IFC_ENV_SHA_ACCEL                 := 100,
          IDX_SOC_IFC_ENV_FW_UPD                    := 10,
          IDX_SOC_IFC_ENV_MBOX_UC_REG_ACCESS        := 100
      };
  }
  constraint iter_count_c {
      iteration_count inside {[1:10]};
  }

  function new(string name = "" );
    super.new(name);
    reg_model = top_configuration.soc_ifc_subenv_config.soc_ifc_rm;
    if ($value$plusargs("CALIPTRA_TOP_RAND_ITER=%0d", iteration_count)) begin
        `uvm_info("CALIPTRA_TOP_RAND_TEST", $sformatf("Received Command Line Iteration Count Argument of %0d", iteration_count), UVM_LOW);
        iteration_count.rand_mode(0);
        this.iter_count_c.constraint_mode(0);
    end
    else begin
        if (!this.randomize(iteration_count))
            `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "Failed to randomize iteration_count after receiving no command line override")
        else
            `uvm_info("CALIPTRA_TOP_RAND_TEST", $sformatf("Did not receive Command Line Iteration Count Argument with +CALIPTRA_TOP_RAND_ITER, defaulting to %0d", iteration_count), UVM_LOW);
    end
    soc_ifc_env_seq_ii = new[iteration_count];
  endfunction

  // ****************************************************************************
  virtual task run_firmware_init(soc_ifc_env_mbox_real_fw_sequence_t fmc_seq, soc_ifc_env_mbox_real_fw_sequence_t rt_seq);
    bit ready_for_fw = 0;
    bit ready_for_rt = 0;
    while (!ready_for_fw) begin
        while(!sts_rsp_count)soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(1); // Wait for new status updates
        `uvm_info("CALIPTRA_TOP_RAND_TEST", "Observed status response, checking contents", UVM_DEBUG)
        sts_rsp_count = 0; // We only care about the latest rsp, so even if count > 1, reset back to 0
        ready_for_fw = soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.ready_for_fw_push;
    end
    if (!fmc_seq.randomize() with { fmc_seq.mbox_op_rand.cmd == mbox_cmd_e'(MBOX_CMD_FMC_UPDATE); })
        `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "caliptra_top_rand_sequence::body() - fmc_seq randomization failed")
    fmc_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);
    if (!rt_seq.randomize() with { rt_seq.mbox_op_rand.cmd == mbox_cmd_e'(MBOX_CMD_RT_UPDATE); })
        `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "caliptra_top_rand_sequence::body() - rt_seq randomization failed")
    rt_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

    // Wait for RT image to set the ready_for_rt bit
    while (!ready_for_rt) begin
        while(!sts_rsp_count)soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(1); // Wait for new status updates
        `uvm_info("CALIPTRA_TOP_RAND_TEST", "Observed status response, checking contents", UVM_DEBUG)
        sts_rsp_count = 0; // We only care about the latest rsp, so even if count > 1, reset back to 0
        ready_for_rt = soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.ready_for_runtime;
    end
  endtask

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin
    // Construct sequences here
    bit pauser_valid_initialized = 1'b0;
    uvm_object obj;
    int ii;

    caliptra_top_env_seq = caliptra_top_env_sequence_base_t::type_id::create("caliptra_top_env_seq");
    soc_ifc_env_bringup_seq = soc_ifc_env_bringup_sequence_t::type_id::create("soc_ifc_env_bringup_seq");
    soc_ifc_env_pauser_init_seq = soc_ifc_env_pauser_init_sequence_t::type_id::create("soc_ifc_env_pauser_init_seq");
    soc_ifc_env_mbox_fmc_seq = soc_ifc_env_mbox_real_fw_sequence_t::type_id::create("soc_ifc_env_mbox_fmc_seq");
    soc_ifc_env_mbox_rt_seq = soc_ifc_env_mbox_real_fw_sequence_t::type_id::create("soc_ifc_env_mbox_rt_seq");

    soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq     = soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq");
    soc_ifc_subenv_soc_ifc_status_agent_responder_seq  = soc_ifc_subenv_soc_ifc_status_agent_responder_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_status_agent_responder_seq");

    // Handle to the responder sequence for getting response transactions
    soc_ifc_env_bringup_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_pauser_init_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_mbox_fmc_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_mbox_rt_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;

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
    fork
        forever @(soc_ifc_subenv_soc_ifc_status_agent_responder_seq.new_rsp) sts_rsp_count++;
    join_none

    if(!soc_ifc_env_bringup_seq.randomize())
        `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "caliptra_top_rand_sequence::body() - soc_ifc_env_bringup_seq randomization failed")
    soc_ifc_env_bringup_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

    `uvm_info("CALIPTRA_TOP_BRINGUP", "SoC completed poweron and observed reset deassertion to system", UVM_LOW)

    run_firmware_init(soc_ifc_env_mbox_fmc_seq,soc_ifc_env_mbox_rt_seq);

    // In this loop, randomly select a sequence to run (from the list of available
    // ENV level sequences), randomize the sequence object, and kick it off
    for (ii = 0; ii < iteration_count; ii++) begin: RAND_LOOP
        if(!this.randomize(rand_seq_idx)) `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "Failed to randomize rand_seq_idx");

        // Create a new sequence instance of the randomized type
        case (rand_seq_idx) inside
            //IDX_SOC_IFC_ENV_MBOX_RAND_FW:
                //obj = soc_ifc_env_mbox_rand_fw_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_RAND_SMALL:
                obj = soc_ifc_env_mbox_rand_small_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_RAND_MEDIUM:
                obj = soc_ifc_env_mbox_rand_medium_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_RAND_LARGE:
                obj = soc_ifc_env_mbox_rand_large_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_MIN:
                obj = soc_ifc_env_mbox_min_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_MAX:
                obj = soc_ifc_env_mbox_max_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_RAND_PAUSER_SMALL: begin
                if (!pauser_valid_initialized) begin
                    if(!soc_ifc_env_pauser_init_seq.randomize())
                        `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "caliptra_top_rand_sequence::body() - soc_ifc_env_pauser_init_seq randomization failed")
                    soc_ifc_env_pauser_init_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

                    `uvm_info("CALIPTRA_TOP_RAND_TEST", "SoC completed PAUSER VALID initialization", UVM_LOW)
                    pauser_valid_initialized = 1'b1;
                end
                obj = soc_ifc_env_mbox_rand_pauser_small_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            end
            IDX_SOC_IFC_ENV_MBOX_RAND_PAUSER_MEDIUM: begin
                if (!pauser_valid_initialized) begin
                    if(!soc_ifc_env_pauser_init_seq.randomize())
                        `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "caliptra_top_rand_sequence::body() - soc_ifc_env_pauser_init_seq randomization failed")
                    soc_ifc_env_pauser_init_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

                    `uvm_info("CALIPTRA_TOP_RAND_TEST", "SoC completed PAUSER VALID initialization", UVM_LOW)
                    pauser_valid_initialized = 1'b1;
                end
                obj = soc_ifc_env_mbox_rand_pauser_medium_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            end
            IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_SMALL: begin
                obj = soc_ifc_env_mbox_rand_delay_small_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            end
            IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_MEDIUM: begin
                obj = soc_ifc_env_mbox_rand_delay_medium_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            end
            IDX_SOC_IFC_ENV_MBOX_MULTI_AGENT:
                // TODO PAUSER init first?
                obj = soc_ifc_env_mbox_rand_multi_agent_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_RST_WARM:
                obj = soc_ifc_env_reset_warm_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_RST_COLD:
                obj = soc_ifc_env_reset_cold_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_RST_WARM_RAND_MEDIUM:
                obj = soc_ifc_env_mbox_rst_warm_rand_medium_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_RST_COLD_RAND_MEDIUM:
                obj = soc_ifc_env_mbox_rst_cold_rand_medium_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_SHA_ACCEL:
                obj = soc_ifc_env_mbox_sha_accel_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_SHA_ACCEL:
                obj = soc_ifc_env_sha_accel_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_FW_UPD:
                obj = soc_ifc_env_mbox_fw_upd_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_UC_REG_ACCESS:
                obj = soc_ifc_env_mbox_uc_reg_access_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            default:
                `uvm_error("CALIPTRA_TOP_RAND_TEST", $sformatf("rand_seq_idx randomized to illegal value: %p", rand_seq_idx))
        endcase

        // Randomize and run the sequence
        if(!$cast(soc_ifc_env_seq_ii[ii],obj)) `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "caliptra_top_rand_sequence::body() - <seq_type>.create_object() failed")
        `uvm_info("CALIPTRA_TOP_RAND_TEST", $sformatf("rand_seq randomized to: %s", soc_ifc_env_seq_ii[ii].get_type_name()), UVM_LOW)
        if(!soc_ifc_env_seq_ii[ii].randomize())
            `uvm_fatal("CALIPTRA_TOP_RAND_TEST", $sformatf("caliptra_top_rand_sequence::body() - %s randomization failed", soc_ifc_env_seq_ii[ii].get_type_name()));
        soc_ifc_env_seq_ii[ii].soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
        soc_ifc_env_seq_ii[ii].start(top_configuration.soc_ifc_subenv_config.vsqr);

        // If the sequence performed a cold reset or firmware update reset
        // we need to reload the firmware before proceeding to next sequence
        case (rand_seq_idx) inside
            IDX_SOC_IFC_ENV_RST_WARM,
            IDX_SOC_IFC_ENV_RST_COLD,
            IDX_SOC_IFC_ENV_MBOX_RST_WARM_RAND_MEDIUM,
            IDX_SOC_IFC_ENV_MBOX_RST_COLD_RAND_MEDIUM: begin
                `uvm_info("CALIPTRA_TOP_RAND_TEST", "Rerunning firmware initialization flow after reset occurrence", UVM_LOW)
                // Allocate new entries in the associative array based on iteration index
                soc_ifc_env_mbox_fw_seq_ii[$sformatf("fmc[%0d]", ii)] = soc_ifc_env_mbox_real_fw_sequence_t::type_id::create($sformatf("soc_ifc_env_mbox_fmc_seq[%0d]",ii));
                soc_ifc_env_mbox_fw_seq_ii[$sformatf("rt[%0d]" , ii)] = soc_ifc_env_mbox_real_fw_sequence_t::type_id::create($sformatf("soc_ifc_env_mbox_rt_seq[%0d]",ii));
                soc_ifc_env_mbox_fw_seq_ii[$sformatf("fmc[%0d]", ii)].soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
                soc_ifc_env_mbox_fw_seq_ii[$sformatf("rt[%0d]" , ii)].soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
                run_firmware_init(soc_ifc_env_mbox_fw_seq_ii[$sformatf("fmc[%0d]", ii)],
                                  soc_ifc_env_mbox_fw_seq_ii[$sformatf("rt[%0d]" , ii)]);
            end
            default: begin
            end
        endcase
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

// pragma uvmf custom external begin
// pragma uvmf custom external end

