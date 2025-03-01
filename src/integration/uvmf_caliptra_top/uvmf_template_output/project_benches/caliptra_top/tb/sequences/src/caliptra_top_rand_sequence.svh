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
  rand soc_ifc_env_axi_user_init_sequence_t soc_ifc_env_axi_user_init_seq;
  rand soc_ifc_env_mbox_rand_small_sequence_t soc_ifc_env_early_mbox_seq;
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
      IDX_SOC_IFC_ENV_MBOX_RAND_AXI_USER_SMALL,
      IDX_SOC_IFC_ENV_MBOX_RAND_AXI_USER_MEDIUM,
      IDX_SOC_IFC_ENV_MBOX_RAND_AXI_USER_LARGE,
      IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_SMALL,
      IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_MEDIUM,
      IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_LARGE,
      IDX_SOC_IFC_ENV_MBOX_RAND_MEDIUM_INTERFERENCE,
      IDX_SOC_IFC_ENV_MBOX_DLEN_INVALID,
      IDX_SOC_IFC_ENV_MBOX_DLEN_OVERFLOW_SMALL,
      IDX_SOC_IFC_ENV_MBOX_DLEN_OVERFLOW_MEDIUM,
      IDX_SOC_IFC_ENV_MBOX_DLEN_OVERFLOW_LARGE,
      IDX_SOC_IFC_ENV_MBOX_DLEN_UNDERFLOW_SMALL,
      IDX_SOC_IFC_ENV_MBOX_DLEN_UNDERFLOW_MEDIUM,
      IDX_SOC_IFC_ENV_MBOX_DLEN_UNDERFLOW_LARGE,
      IDX_SOC_IFC_ENV_MBOX_REG_AXS_INV_SMALL,
      IDX_SOC_IFC_ENV_MBOX_REG_AXS_INV_MEDIUM,
      IDX_SOC_IFC_ENV_MBOX_REG_AXS_INV_LARGE,
      IDX_SOC_IFC_ENV_MBOX_2BIT_FLIP_SMALL,
      IDX_SOC_IFC_ENV_MBOX_2BIT_FLIP_MEDIUM,
      IDX_SOC_IFC_ENV_MBOX_2BIT_FLIP_LARGE,
      IDX_SOC_IFC_ENV_MBOX_MULTI_AGENT,
      IDX_SOC_IFC_ENV_RST_WARM,
      IDX_SOC_IFC_ENV_RST_COLD,
      IDX_SOC_IFC_ENV_MBOX_RST_WARM_RAND_MEDIUM,
      IDX_SOC_IFC_ENV_MBOX_RST_COLD_RAND_MEDIUM,
      IDX_SOC_IFC_ENV_MBOX_SHA_ACCEL,
      IDX_SOC_IFC_ENV_SHA_ACCEL,
      IDX_SOC_IFC_ENV_FW_UPD,
      IDX_SOC_IFC_ENV_MBOX_UC_REG_ACCESS,
      IDX_SOC_IFC_ENV_MBOX_DIR_READ
  } rand_seq_idx;

  rand int iteration_count;
  rand bit do_early_mbox_seq;
  int sts_rsp_count = 0;

  // Choose rand weights for each sequence to determine run frequency
  constraint avail_env_seqs_c {
      rand_seq_idx dist {
          //IDX_SOC_IFC_ENV_MBOX_RAND_FW                := 0,
          IDX_SOC_IFC_ENV_MBOX_RAND_SMALL               := 20,
          IDX_SOC_IFC_ENV_MBOX_RAND_MEDIUM              := 20,
          IDX_SOC_IFC_ENV_MBOX_RAND_LARGE               := 2,
          IDX_SOC_IFC_ENV_MBOX_MIN                      := 100,
          IDX_SOC_IFC_ENV_MBOX_MAX                      := 10,
          IDX_SOC_IFC_ENV_MBOX_RAND_AXI_USER_SMALL      := 100,
          IDX_SOC_IFC_ENV_MBOX_RAND_AXI_USER_MEDIUM     := 100,
          IDX_SOC_IFC_ENV_MBOX_RAND_AXI_USER_LARGE      := 10,
          IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_SMALL         := 100,
          IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_MEDIUM        := 100,
          IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_LARGE         := 5,
          IDX_SOC_IFC_ENV_MBOX_RAND_MEDIUM_INTERFERENCE := 100,
          IDX_SOC_IFC_ENV_MBOX_DLEN_INVALID             := 10,
          IDX_SOC_IFC_ENV_MBOX_DLEN_OVERFLOW_SMALL      := 100,
          IDX_SOC_IFC_ENV_MBOX_DLEN_OVERFLOW_MEDIUM     := 100,
          IDX_SOC_IFC_ENV_MBOX_DLEN_OVERFLOW_LARGE      := 10,
          IDX_SOC_IFC_ENV_MBOX_DLEN_UNDERFLOW_SMALL     := 100,
          IDX_SOC_IFC_ENV_MBOX_DLEN_UNDERFLOW_MEDIUM    := 100,
          IDX_SOC_IFC_ENV_MBOX_DLEN_UNDERFLOW_LARGE     := 10,
          IDX_SOC_IFC_ENV_MBOX_REG_AXS_INV_SMALL        := 200,
          IDX_SOC_IFC_ENV_MBOX_REG_AXS_INV_MEDIUM       := 200,
          IDX_SOC_IFC_ENV_MBOX_REG_AXS_INV_LARGE        := 20,
          IDX_SOC_IFC_ENV_MBOX_2BIT_FLIP_SMALL          := 200,
          IDX_SOC_IFC_ENV_MBOX_2BIT_FLIP_MEDIUM         := 200,
          IDX_SOC_IFC_ENV_MBOX_2BIT_FLIP_LARGE          := 10,
          IDX_SOC_IFC_ENV_MBOX_MULTI_AGENT              := 200,
          IDX_SOC_IFC_ENV_RST_WARM                      := 100,
          IDX_SOC_IFC_ENV_RST_COLD                      := 100,
          IDX_SOC_IFC_ENV_MBOX_RST_WARM_RAND_MEDIUM     := 100,
          IDX_SOC_IFC_ENV_MBOX_RST_COLD_RAND_MEDIUM     := 100,
          IDX_SOC_IFC_ENV_MBOX_SHA_ACCEL                := 100,
          IDX_SOC_IFC_ENV_SHA_ACCEL                     := 100,
          IDX_SOC_IFC_ENV_FW_UPD                        := 10,
          IDX_SOC_IFC_ENV_MBOX_UC_REG_ACCESS            := 100,
          IDX_SOC_IFC_ENV_MBOX_DIR_READ                 := 100
      };
  }
  constraint disable_long_env_seqs_c {
      !(rand_seq_idx inside {IDX_SOC_IFC_ENV_MBOX_RAND_LARGE,
                             IDX_SOC_IFC_ENV_MBOX_MAX,
                             IDX_SOC_IFC_ENV_MBOX_RAND_AXI_USER_LARGE,
                             IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_MEDIUM,
                             IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_LARGE,
                             IDX_SOC_IFC_ENV_MBOX_DLEN_INVALID,
                             IDX_SOC_IFC_ENV_MBOX_DLEN_OVERFLOW_LARGE,
                             IDX_SOC_IFC_ENV_MBOX_DLEN_UNDERFLOW_LARGE,
                             IDX_SOC_IFC_ENV_MBOX_REG_AXS_INV_LARGE,
                             IDX_SOC_IFC_ENV_MBOX_2BIT_FLIP_LARGE,
                             IDX_SOC_IFC_ENV_MBOX_MULTI_AGENT});
  }
  constraint iter_count_c {
      iteration_count inside {[1:10]};
  }
  constraint iter_count_short_c {
      iteration_count < 5;
  }

  function new(string name = "" );
    super.new(name);
    reg_model = top_configuration.soc_ifc_subenv_config.soc_ifc_rm;
    // The short test suite is used in promote pipeline to quickly check for UVM issues
    if ($test$plusargs("CLP_SHORT_SUITE")) begin
        this.disable_long_env_seqs_c.constraint_mode(1);
        this.iter_count_short_c.constraint_mode(1);
    end
    else begin
        this.disable_long_env_seqs_c.constraint_mode(0);
        this.iter_count_short_c.constraint_mode(0);
    end
    // Users can manually override the number of random iterations to any desired value
    if ($value$plusargs("CALIPTRA_TOP_RAND_ITER=%0d", iteration_count)) begin
        `uvm_info("CALIPTRA_TOP_RAND_TEST", $sformatf("Received Command Line Iteration Count Argument of %0d", iteration_count), UVM_LOW);
        iteration_count.rand_mode(0);
        this.iter_count_c.constraint_mode(0);
        this.iter_count_short_c.constraint_mode(0);
    end
    else begin
        if (!this.randomize(iteration_count))
            `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "Failed to randomize iteration_count after receiving no command line override")
        else
            `uvm_info("CALIPTRA_TOP_RAND_TEST", $sformatf("Did not receive Command Line Iteration Count Argument with +CALIPTRA_TOP_RAND_ITER, defaulting to %0d", iteration_count), UVM_LOW);
    end
    // Users can manually override whether or not the early mailbox sequence is run prior to firmware load
    if ($test$plusargs("CALIPTRA_TOP_EARLY_MB_SEQ")) begin
        `uvm_info("CALIPTRA_TOP_RAND_TEST", $sformatf("Received command line argument specifying to run the early mailbox sequence before firmware initialization"), UVM_LOW);
        do_early_mbox_seq = 1;
        do_early_mbox_seq.rand_mode(0);
    end
    else begin
        if (!this.randomize(do_early_mbox_seq))
            `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "Failed to randomize do_early_mbox_seq after receiving no command line override")
        else
            `uvm_info("CALIPTRA_TOP_RAND_TEST", $sformatf("Did not receive Command Line Argument for early mailbox sequence with +CALIPTRA_TOP_EARLY_MB_SEQ, defaulting to %0d", do_early_mbox_seq), UVM_LOW);
    end
    soc_ifc_env_seq_ii = new[iteration_count];
  endfunction

  // ****************************************************************************
  virtual task run_firmware_init(soc_ifc_env_mbox_real_fw_sequence_t fmc_seq, soc_ifc_env_mbox_real_fw_sequence_t rt_seq);
    bit ready_for_mb_processing = 0;
    bit ready_for_rt = 0;
    while (!ready_for_mb_processing) begin
        while(!sts_rsp_count)soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(1); // Wait for new status updates
        `uvm_info("CALIPTRA_TOP_RAND_TEST", "Observed status response, checking contents", UVM_DEBUG)
        sts_rsp_count = 0; // We only care about the latest rsp, so even if count > 1, reset back to 0
        ready_for_mb_processing = soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.ready_for_mb_processing;
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
    bit axi_user_valid_initialized = 1'b0;
    bit override_mbox_sts_exp_error = 1'b0;
    mbox_sts_exp_error_type_e override_mbox_sts_exp_error_type = EXP_ERR_NONE;
    uvm_object obj;
    int ii;
    int unsigned mbox_ecc_single_error_burst;
    int unsigned mbox_ecc_single_error_delay_clocks;

    caliptra_top_env_seq = caliptra_top_env_sequence_base_t::type_id::create("caliptra_top_env_seq");
    soc_ifc_env_bringup_seq = soc_ifc_env_bringup_sequence_t::type_id::create("soc_ifc_env_bringup_seq");
    soc_ifc_env_axi_user_init_seq = soc_ifc_env_axi_user_init_sequence_t::type_id::create("soc_ifc_env_axi_user_init_seq");
    soc_ifc_env_early_mbox_seq = soc_ifc_env_mbox_rand_small_sequence_t::type_id::create("soc_ifc_env_early_mbox_seq");
    soc_ifc_env_mbox_fmc_seq = soc_ifc_env_mbox_real_fw_sequence_t::type_id::create("soc_ifc_env_mbox_fmc_seq");
    soc_ifc_env_mbox_rt_seq = soc_ifc_env_mbox_real_fw_sequence_t::type_id::create("soc_ifc_env_mbox_rt_seq");

    soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq     = soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq");
    soc_ifc_subenv_ss_mode_ctrl_agent_random_seq      = soc_ifc_subenv_ss_mode_ctrl_agent_random_seq_t::type_id::create("soc_ifc_subenv_ss_mode_ctrl_agent_random_seq");
    soc_ifc_subenv_soc_ifc_status_agent_responder_seq  = soc_ifc_subenv_soc_ifc_status_agent_responder_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_status_agent_responder_seq");
    soc_ifc_subenv_ss_mode_status_agent_responder_seq = soc_ifc_subenv_ss_mode_status_agent_responder_seq_t::type_id::create("soc_ifc_subenv_ss_mode_status_agent_responder_seq");
    soc_ifc_subenv_mbox_sram_agent_responder_seq      = soc_ifc_subenv_mbox_sram_agent_responder_seq_t::type_id::create("soc_ifc_subenv_mbox_sram_agent_responder_seq");

    // Handle to the responder sequence for getting response transactions
    soc_ifc_env_bringup_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_axi_user_init_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_early_mbox_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
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
        soc_ifc_subenv_ss_mode_status_agent_responder_seq.start(soc_ifc_subenv_ss_mode_status_agent_sequencer);
        soc_ifc_subenv_mbox_sram_agent_responder_seq.start(soc_ifc_subenv_mbox_sram_agent_sequencer);
    join_none
//    // Start INITIATOR sequences here
//    fork
//      repeat (25) soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq.start(soc_ifc_subenv_soc_ifc_ctrl_agent_sequencer);
//    join
    fork
        forever begin
            if (!std::randomize(mbox_ecc_single_error_burst,mbox_ecc_single_error_delay_clocks) with {mbox_ecc_single_error_burst        dist {1 :/ 10000, [2:5] :/ 2000, [6:31] :/ 200, [32:1023] :/ 10, [1024:131071] :/ 2, [131072:524288] :/ 1};
                                                                                                      mbox_ecc_single_error_delay_clocks dist {1 :/ 1, [2:31] :/ 3, [32:127] :/ 5, [128:1023] :/ 3, [1024:131072] :/ 1};    })
                `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "Failed to randomize mbox ecc bit flip injection parameters")
            else
                `uvm_info("CALIPTRA_TOP_RAND_TEST", $sformatf("Randomized mbox ecc bit flip injection parameters: burst [%0d] delay [%0d clocks]", mbox_ecc_single_error_burst, mbox_ecc_single_error_delay_clocks), UVM_FULL)
            soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(mbox_ecc_single_error_delay_clocks);
            `uvm_info("CALIPTRA_TOP_RAND_TEST", $sformatf("Injecting mbox ecc error with burst [%0d]", mbox_ecc_single_error_burst), UVM_DEBUG)
            repeat(mbox_ecc_single_error_burst) begin
                soc_ifc_subenv_mbox_sram_agent_config.inject_ecc_error |= 2'b01;
                @soc_ifc_subenv_mbox_sram_agent_responder_seq.new_rsp;
            end
        end
    join_none
    fork
        forever @(soc_ifc_subenv_soc_ifc_status_agent_responder_seq.new_rsp) sts_rsp_count++;
    join_none

    if(!soc_ifc_env_bringup_seq.randomize())
        `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "caliptra_top_rand_sequence::body() - soc_ifc_env_bringup_seq randomization failed")
    soc_ifc_env_bringup_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

    `uvm_info("CALIPTRA_TOP_BRINGUP", "SoC completed poweron and observed reset deassertion to system", UVM_LOW)

    if (do_early_mbox_seq) begin
        if (!soc_ifc_env_early_mbox_seq.randomize() with { mbox_op_rand.dlen <= 32'h0000_0020; !mbox_op_rand.cmd.cmd_s.resp_reqd; })
            `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "caliptra_top_rand_sequence::body() - soc_ifc_env_early_mbox_seq randomization failed")
        `uvm_info("CALIPTRA_TOP_RAND_TEST", "Running early mailbox sequence", UVM_MEDIUM)
        soc_ifc_env_early_mbox_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);
    end

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
            IDX_SOC_IFC_ENV_MBOX_RAND_AXI_USER_SMALL: begin
                if (!axi_user_valid_initialized) begin
                    if(!soc_ifc_env_axi_user_init_seq.randomize())
                        `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "caliptra_top_rand_sequence::body() - soc_ifc_env_axi_user_init_seq randomization failed")
                    soc_ifc_env_axi_user_init_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

                    `uvm_info("CALIPTRA_TOP_RAND_TEST", "SoC completed AXI_USER VALID initialization", UVM_LOW)
                    axi_user_valid_initialized = 1'b1;
                end
                obj = soc_ifc_env_mbox_rand_axi_user_small_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            end
            IDX_SOC_IFC_ENV_MBOX_RAND_AXI_USER_MEDIUM: begin
                if (!axi_user_valid_initialized) begin
                    if(!soc_ifc_env_axi_user_init_seq.randomize())
                        `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "caliptra_top_rand_sequence::body() - soc_ifc_env_axi_user_init_seq randomization failed")
                    soc_ifc_env_axi_user_init_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

                    `uvm_info("CALIPTRA_TOP_RAND_TEST", "SoC completed AXI_USER VALID initialization", UVM_LOW)
                    axi_user_valid_initialized = 1'b1;
                end
                obj = soc_ifc_env_mbox_rand_axi_user_medium_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            end
            IDX_SOC_IFC_ENV_MBOX_RAND_AXI_USER_LARGE: begin
                if (!axi_user_valid_initialized) begin
                    if(!soc_ifc_env_axi_user_init_seq.randomize())
                        `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "caliptra_top_rand_sequence::body() - soc_ifc_env_axi_user_init_seq randomization failed")
                    soc_ifc_env_axi_user_init_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

                    `uvm_info("CALIPTRA_TOP_RAND_TEST", "SoC completed AXI_USER VALID initialization", UVM_LOW)
                    axi_user_valid_initialized = 1'b1;
                end
                obj = soc_ifc_env_mbox_rand_axi_user_large_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            end
            IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_SMALL: begin
                obj = soc_ifc_env_mbox_rand_delay_small_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            end
            IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_MEDIUM: begin
                obj = soc_ifc_env_mbox_rand_delay_medium_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            end
            IDX_SOC_IFC_ENV_MBOX_RAND_DELAY_LARGE: begin
                obj = soc_ifc_env_mbox_rand_delay_large_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            end
            IDX_SOC_IFC_ENV_MBOX_RAND_MEDIUM_INTERFERENCE:
                obj = soc_ifc_env_mbox_rand_medium_interference_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_DLEN_INVALID:
                obj = soc_ifc_env_mbox_dlen_invalid_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_DLEN_OVERFLOW_SMALL:
                obj = soc_ifc_env_mbox_dlen_overflow_small_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_DLEN_OVERFLOW_MEDIUM:
                obj = soc_ifc_env_mbox_dlen_overflow_medium_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_DLEN_OVERFLOW_LARGE:
                obj = soc_ifc_env_mbox_dlen_overflow_large_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_DLEN_UNDERFLOW_SMALL:
                obj = soc_ifc_env_mbox_dlen_underflow_small_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_DLEN_UNDERFLOW_MEDIUM:
                obj = soc_ifc_env_mbox_dlen_underflow_medium_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_DLEN_UNDERFLOW_LARGE:
                obj = soc_ifc_env_mbox_dlen_underflow_large_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_REG_AXS_INV_SMALL:
                obj = soc_ifc_env_mbox_reg_axs_invalid_small_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_REG_AXS_INV_MEDIUM:
                obj = soc_ifc_env_mbox_reg_axs_invalid_medium_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_REG_AXS_INV_LARGE:
                obj = soc_ifc_env_mbox_reg_axs_invalid_large_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_2BIT_FLIP_SMALL:
                obj = soc_ifc_env_mbox_sram_double_bit_flip_small_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_2BIT_FLIP_MEDIUM:
                obj = soc_ifc_env_mbox_sram_double_bit_flip_medium_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_2BIT_FLIP_LARGE:
                obj = soc_ifc_env_mbox_sram_double_bit_flip_large_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            IDX_SOC_IFC_ENV_MBOX_MULTI_AGENT:
                // TODO AXI_USER init first?
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
            IDX_SOC_IFC_ENV_MBOX_DIR_READ:
                obj = soc_ifc_env_mbox_dir_read_sequence_t::get_type().create_object($sformatf("soc_ifc_env_seq_ii[%0d]",ii));
            default:
                `uvm_error("CALIPTRA_TOP_RAND_TEST", $sformatf("rand_seq_idx randomized to illegal value: %p", rand_seq_idx))
        endcase

        // Randomize and run the sequence
        if(!$cast(soc_ifc_env_seq_ii[ii],obj)) `uvm_fatal("CALIPTRA_TOP_RAND_TEST", "caliptra_top_rand_sequence::body() - <seq_type>.create_object() failed")
        `uvm_info("CALIPTRA_TOP_RAND_TEST", $sformatf("rand_seq randomized to: %s", soc_ifc_env_seq_ii[ii].get_type_name()), UVM_LOW)
        if(!soc_ifc_env_seq_ii[ii].randomize())
            `uvm_fatal("CALIPTRA_TOP_RAND_TEST", $sformatf("caliptra_top_rand_sequence::body() - %s randomization failed", soc_ifc_env_seq_ii[ii].get_type_name()));
        if (override_mbox_sts_exp_error) begin
            soc_ifc_env_mbox_sequence_base_t mbox_seq;
            soc_ifc_env_mbox_rand_multi_agent_sequence_t mbox_mult_agent_seq;
            if ($cast(mbox_seq,soc_ifc_env_seq_ii[ii])) begin
                mbox_seq.mbox_sts_exp_error      = 1'b1;
                mbox_seq.mbox_sts_exp_error_type = override_mbox_sts_exp_error_type;
            end
            else if ($cast(mbox_mult_agent_seq,soc_ifc_env_seq_ii[ii])) begin
                // Multi-agent sequences are complicated to add 'expected' error logic.
                // Just wait for uC to start the sanitize operation and then kick off the sequence.
                while(reg_model.mbox_csr_rm.mbox_lock.lock.get_mirrored_value() == 0)
                    soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(1);
            end
            // Non-mbox sequences (i.e. reset) also clear the error override condition
            else begin
                override_mbox_sts_exp_error = 1'b0;
            end
        end
        soc_ifc_env_seq_ii[ii].soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
        soc_ifc_env_seq_ii[ii].ss_mode_status_agent_rsp_seq = soc_ifc_subenv_ss_mode_status_agent_responder_seq;
        soc_ifc_env_seq_ii[ii].start(top_configuration.soc_ifc_subenv_config.vsqr);

        // After the sequence ends, if it injected a double-bit error and the
        // mailbox was not sanitized, expect an error on a subsequence sequence when firmware
        // forcibly unlocks the mailbox to sanitize it
        // FIXME get rid of this ugly workaround after GitHub issue #340 has been fixed
        //       and the firmware workaround to sanitize mbox is removed
        begin
            soc_ifc_env_mbox_sram_double_bit_flip_sequence_t mbox_2bit_seq;
            // At the end of the sequence, Caliptra is not sanitizing the mailbox, so
            // expect the next sequence to be interrupted with an unlock
            if($cast(mbox_2bit_seq,soc_ifc_env_seq_ii[ii]) && mbox_2bit_seq.mbox_sts_exp_error) begin
                override_mbox_sts_exp_error = 1'b1;
                override_mbox_sts_exp_error_type = EXP_ERR_PROT;
            end
            else begin
                override_mbox_sts_exp_error = 1'b0;
            end
        end

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
                soc_ifc_env_mbox_fw_seq_ii[$sformatf("fmc[%0d]", ii)].ss_mode_status_agent_rsp_seq = soc_ifc_subenv_ss_mode_status_agent_responder_seq;
                soc_ifc_env_mbox_fw_seq_ii[$sformatf("rt[%0d]" , ii)].ss_mode_status_agent_rsp_seq = soc_ifc_subenv_ss_mode_status_agent_responder_seq;
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
      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_cptra_ctrl_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_ss_mode_ctrl_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_soc_ifc_status_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_cptra_status_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_ss_mode_status_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_mbox_sram_agent_config.wait_for_num_clocks(4000);
    join

    // pragma uvmf custom body end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

