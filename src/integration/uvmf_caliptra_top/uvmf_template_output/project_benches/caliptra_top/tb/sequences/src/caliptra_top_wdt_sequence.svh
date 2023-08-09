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
// DESCRIPTION: This file contains the top level sequence used in caliptra_top_wdt_test.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class caliptra_top_wdt_sequence extends caliptra_top_bench_sequence_base;

  `uvm_object_utils( caliptra_top_wdt_sequence );

  rand soc_ifc_env_bringup_sequence_t soc_ifc_env_bringup_seq;
  rand soc_ifc_env_pauser_init_sequence_t soc_ifc_env_pauser_init_seq;
  rand soc_ifc_env_mbox_real_fw_sequence_t soc_ifc_env_mbox_fmc_seq;
  rand soc_ifc_env_mbox_real_fw_sequence_t soc_ifc_env_mbox_rt_seq;
  rand soc_ifc_env_reset_warm_sequence_t soc_ifc_env_reset_warm_seq;
  rand soc_ifc_env_reset_cold_sequence_t soc_ifc_env_reset_cold_seq;
  // Local handle to register model for convenience
  soc_ifc_reg_model_top reg_model;


  rand int iteration_count;
  int sts_rsp_count = 0;
  int rsp_count = 0;


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
        `uvm_info("CALIPTRA_TOP_WDT_TEST", "Observed status response, checking contents", UVM_DEBUG)
        sts_rsp_count = 0; // We only care about the latest rsp, so even if count > 1, reset back to 0
        ready_for_fw = soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.ready_for_fw_push;
    end
    if (!fmc_seq.randomize() with { fmc_seq.mbox_op_rand.cmd == mbox_cmd_e'(MBOX_CMD_FMC_UPDATE); })
        `uvm_fatal("CALIPTRA_TOP_WDT_TEST", "caliptra_top_wdt_sequence::body() - fmc_seq randomization failed")
    fmc_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);
    if (!rt_seq.randomize() with { rt_seq.mbox_op_rand.cmd == mbox_cmd_e'(MBOX_CMD_RT_UPDATE); })
        `uvm_fatal("CALIPTRA_TOP_WDT_TEST", "caliptra_top_wdt_sequence::body() - rt_seq randomization failed")
    rt_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

    // Wait for RT image to set the ready_for_rt bit
    while (!ready_for_rt) begin
        while(!sts_rsp_count)soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(1); // Wait for new status updates
        `uvm_info("CALIPTRA_TOP_WDT_TEST", "Observed status response, checking contents", UVM_DEBUG)
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
    bit nmi_intr;
    bit hw_error_fatal;
    uvm_status_e reg_sts;
    uvm_reg_data_t wdt_status_data;

    caliptra_top_env_seq = caliptra_top_env_sequence_base_t::type_id::create("caliptra_top_env_seq");
    soc_ifc_env_bringup_seq = soc_ifc_env_bringup_sequence_t::type_id::create("soc_ifc_env_bringup_seq");
    soc_ifc_env_pauser_init_seq = soc_ifc_env_pauser_init_sequence_t::type_id::create("soc_ifc_env_pauser_init_seq");
    soc_ifc_env_mbox_fmc_seq = soc_ifc_env_mbox_real_fw_sequence_t::type_id::create("soc_ifc_env_mbox_fmc_seq");
    soc_ifc_env_mbox_rt_seq = soc_ifc_env_mbox_real_fw_sequence_t::type_id::create("soc_ifc_env_mbox_rt_seq");
    soc_ifc_env_reset_warm_seq = soc_ifc_env_reset_warm_sequence_t::type_id::create("soc_ifc_env_reset_warm_seq");
    soc_ifc_env_reset_cold_seq = soc_ifc_env_reset_cold_sequence_t::type_id::create("soc_ifc_env_reset_cold_seq");

    soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq     = soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq");
    soc_ifc_subenv_soc_ifc_status_agent_responder_seq  = soc_ifc_subenv_soc_ifc_status_agent_responder_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_status_agent_responder_seq");
    soc_ifc_subenv_mbox_sram_agent_responder_seq      = soc_ifc_subenv_mbox_sram_agent_responder_seq_t::type_id::create("soc_ifc_subenv_mbox_sram_agent_responder_seq");

    // Handle to the responder sequence for getting response transactions
    soc_ifc_env_bringup_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_pauser_init_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_mbox_fmc_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_mbox_rt_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_reset_warm_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_reset_cold_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;

    reg_model.reset();
    // Start RESPONDER sequences here
    fork
        soc_ifc_subenv_soc_ifc_status_agent_responder_seq.start(soc_ifc_subenv_soc_ifc_status_agent_sequencer);
        soc_ifc_subenv_mbox_sram_agent_responder_seq.start(soc_ifc_subenv_mbox_sram_agent_sequencer);
    join_none

    fork
        forever @(soc_ifc_subenv_soc_ifc_status_agent_responder_seq.new_rsp) begin 
          sts_rsp_count++;
          rsp_count++;
        end
    join_none

    if(!soc_ifc_env_bringup_seq.randomize())
        `uvm_fatal("CALIPTRA_TOP_WDT_TEST", "caliptra_top_wdt_sequence::body() - soc_ifc_env_bringup_seq randomization failed")
    soc_ifc_env_bringup_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

    `uvm_info("CALIPTRA_TOP_BRINGUP", "SoC completed poweron and observed reset deassertion to system", UVM_LOW)

    run_firmware_init(soc_ifc_env_mbox_fmc_seq,soc_ifc_env_mbox_rt_seq);

    // //--------------------------------
    // //Wait for NMI to occur - TODO
    // `uvm_info("KNU", $sformatf("FW init done, hw_error_fatal = %0d", hw_error_fatal),UVM_MEDIUM);
    // while (!hw_error_fatal) begin
    //   `uvm_info("KNU", "Inside while loop",UVM_MEDIUM);
    //   while(!rsp_count)soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(1); // Wait for new status updates
    //   `uvm_info("CALIPTRA_TOP_WDT_TEST", "Observed status response, checking contents", UVM_MEDIUM)
    //   `uvm_info("CALIPTRA_TOP_WDT_TEST", soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.convert2string(), UVM_MEDIUM)
    //   // `uvm_info("CALIPTRA_TOP_WDT_TEST",  $sformatf("response error fatal = %0d",soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.cptra_error_fatal_intr_pending), UVM_MEDIUM)
    //   rsp_count = 0; // We only care about the latest rsp, so even if count > 1, reset back to 0
    //   hw_error_fatal = soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.cptra_error_fatal_intr_pending;
    // end
    // `uvm_info("KNU", $sformatf("Outside while loop, hw_error_fatal = %h", hw_error_fatal),UVM_MEDIUM);
      
    // // //TODO: add APB seq to read hw_error_fatal reg to see if it's NMI or not
    // `uvm_info("CALIPTRA_TOP_WDT_TEST", "Encountered NMI, issuing reset", UVM_MEDIUM);
    // //soc_ifc_env_bringup_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);
    // reg_model.reset(); //TODO needed?
    // // if (!soc_ifc_env_reset_cold_seq.randomize())
    // //   `uvm_fatal("CALIPTRA_TOP_WDT_TEST", "caliptra_top_wdt_sequence::body() - soc_ifc_env_bringup_seq randomization failed")
    // // soc_ifc_env_reset_cold_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);
    // // reg_model.reset(); //TODO needed?
    // if(!soc_ifc_env_bringup_seq.randomize())
    //     `uvm_fatal("CALIPTRA_TOP_WDT_TEST", "caliptra_top_wdt_sequence::body() - soc_ifc_env_bringup_seq randomization failed")
    // soc_ifc_env_bringup_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);
    //--------------------------------
    
    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(10000);
      soc_ifc_subenv_cptra_ctrl_agent_config.wait_for_num_clocks(10000);
      soc_ifc_subenv_soc_ifc_status_agent_config.wait_for_num_clocks(10000);
      soc_ifc_subenv_cptra_status_agent_config.wait_for_num_clocks(10000);
      soc_ifc_subenv_mbox_sram_agent_config.wait_for_num_clocks(10000);
    join

    // pragma uvmf custom body end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

