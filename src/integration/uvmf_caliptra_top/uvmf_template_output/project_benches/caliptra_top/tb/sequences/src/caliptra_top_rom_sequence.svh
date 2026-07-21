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
// DESCRIPTION: This file contains the top level sequence used in caliptra_top_rom_test.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class caliptra_top_rom_sequence extends caliptra_top_bench_sequence_base;

  `uvm_object_utils( caliptra_top_rom_sequence );

  rand soc_ifc_env_rom_bringup_sequence_t soc_ifc_env_bringup_seq;
  rand soc_ifc_env_trng_write_data_sequence_t soc_ifc_env_trng_write_data_seq;
  rand soc_ifc_env_mbox_rom_fw_sequence_t soc_ifc_env_mbox_rom_seq;
  rand soc_ifc_env_sequence_base_t soc_ifc_env_seq_ii[];
  rand soc_ifc_env_axi_user_init_sequence_t soc_ifc_env_axi_user_init_seq;
  // Local handle to register model for convenience
  soc_ifc_reg_model_top reg_model;
  caliptra_axi_user axi_user_obj;

  int sts_rsp_count = 0;

  function new(string name = "" );
    super.new(name);
    reg_model = top_configuration.soc_ifc_subenv_config.soc_ifc_rm;
    axi_user_obj = new();
  endfunction

  // ****************************************************************************
  virtual task monitor_fatal_error(ref bit body_done, ref bit monitor_ready,
                                   ref bit monitor_done);
    uvm_status_e fw_sts, hw_sts;
    uvm_reg_data_t fw_fatal, hw_fatal;
    bit fatal_handled = 1'b0;

    monitor_ready = 1'b1;
    `uvm_info("CALIPTRA_TOP_ROM_TEST", "Entering poll for cptra_error_fatal", UVM_HIGH)
    forever begin
      bit rsp_seen = 1'b0;
      fork : wait_for_rsp_or_done
        begin
          @(soc_ifc_subenv_soc_ifc_status_agent_responder_seq.new_rsp);
          rsp_seen = 1'b1;
        end
        wait(body_done);
      join_any
      #0;
      disable wait_for_rsp_or_done;

      `uvm_info("CALIPTRA_TOP_ROM_TEST", "wait_for_rsp_or_done hit a condition", UVM_DEBUG)
      if (body_done && !rsp_seen) begin
        `uvm_info("CALIPTRA_TOP_ROM_TEST", "monitor_fatal_error returning due to body_done && !rsp_seen", UVM_HIGH)
        monitor_done = 1'b1;
        return;
      end
      `uvm_info("CALIPTRA_TOP_ROM_TEST", "wait_for_rsp_or_done observed new_rsp", UVM_DEBUG)

      if (soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.cptra_error_fatal_intr_pending && !fatal_handled) begin
        fatal_handled = 1'b1;
        reg_model.soc_ifc_reg_rm.CPTRA_FW_ERROR_FATAL.read(fw_sts, fw_fatal, UVM_FRONTDOOR,
                                                          reg_model.soc_ifc_AXI_map, this,
                                                          .extension(axi_user_obj));
        reg_model.soc_ifc_reg_rm.CPTRA_HW_ERROR_FATAL.read(hw_sts, hw_fatal, UVM_FRONTDOOR,
                                                          reg_model.soc_ifc_AXI_map, this,
                                                          .extension(axi_user_obj));

        if ((fw_sts != UVM_IS_OK) || (hw_sts != UVM_IS_OK))
          `uvm_fatal("CALIPTRA_TOP_ROM_TEST",
                     $sformatf("Fatal error pin asserted but fatal register attribution is unavailable: CPTRA_FW_ERROR_FATAL read status=%s value(if valid)=0x%0x, CPTRA_HW_ERROR_FATAL read status=%s value(if valid)=0x%0x",
                               fw_sts.name(), fw_fatal, hw_sts.name(), hw_fatal))
        else if ((|fw_fatal) && (|hw_fatal))
          `uvm_fatal("CALIPTRA_TOP_ROM_TEST",
                     $sformatf("Fatal error pin asserted by both FW_ERROR_FATAL and HW_ERROR_FATAL: CPTRA_FW_ERROR_FATAL=0x%0x, CPTRA_HW_ERROR_FATAL=0x%0x",
                               fw_fatal, hw_fatal))
        else if (|fw_fatal)
          `uvm_fatal("CALIPTRA_TOP_ROM_TEST",
                     $sformatf("Fatal error pin asserted by FW_ERROR_FATAL: CPTRA_FW_ERROR_FATAL=0x%0x, CPTRA_HW_ERROR_FATAL=0x%0x",
                               fw_fatal, hw_fatal))
        else if (|hw_fatal)
          `uvm_fatal("CALIPTRA_TOP_ROM_TEST",
                     $sformatf("Fatal error pin asserted by HW_ERROR_FATAL: CPTRA_FW_ERROR_FATAL=0x%0x, CPTRA_HW_ERROR_FATAL=0x%0x",
                               fw_fatal, hw_fatal))
        else
          `uvm_fatal("CALIPTRA_TOP_ROM_TEST",
                     $sformatf("Fatal error pin/register mismatch: pin asserted while CPTRA_FW_ERROR_FATAL=0x%0x and CPTRA_HW_ERROR_FATAL=0x%0x",
                               fw_fatal, hw_fatal))
      end
      `uvm_info("CALIPTRA_TOP_ROM_TEST", $sformatf("skipped reading ERROR_FATAL regs due to %s", soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.convert2string()), UVM_DEBUG)
    end
  endtask

  // ****************************************************************************
  virtual task run_firmware_init(soc_ifc_env_mbox_rom_fw_sequence_t rom_seq);
    bit ready_for_mb_processing = 0;
    bit ready_for_rt = 0;
    while (!ready_for_mb_processing) begin
        while(!sts_rsp_count)soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(1); // Wait for new status updates
        `uvm_info("CALIPTRA_TOP_ROM_TEST", "Observed status response, checking contents", UVM_DEBUG)
        sts_rsp_count = 0; // We only care about the latest rsp, so even if count > 1, reset back to 0
        ready_for_mb_processing = soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.ready_for_mb_processing;
    end
    if (!rom_seq.randomize())
        `uvm_fatal("CALIPTRA_TOP_ROM_TEST", "caliptra_top_rom_sequence::body() - rom_seq randomization failed")
    rom_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

  endtask

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin
    // Construct sequences here
    uvm_object obj;
    bit body_done = 1'b0;
    bit monitor_ready = 1'b0;
    bit monitor_done = 1'b0;

    caliptra_top_env_seq = caliptra_top_env_sequence_base_t::type_id::create("caliptra_top_env_seq");
    soc_ifc_env_bringup_seq = soc_ifc_env_rom_bringup_sequence_t::type_id::create("soc_ifc_env_bringup_seq");
    soc_ifc_env_mbox_rom_seq = soc_ifc_env_mbox_rom_fw_sequence_t::type_id::create("soc_ifc_env_mbox_rom_seq");
    soc_ifc_env_axi_user_init_seq = soc_ifc_env_axi_user_init_sequence_t::type_id::create("soc_ifc_env_axi_user_init_seq");

    soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq     = soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq");
    soc_ifc_subenv_soc_ifc_status_agent_responder_seq  = soc_ifc_subenv_soc_ifc_status_agent_responder_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_status_agent_responder_seq");
    soc_ifc_subenv_ss_mode_ctrl_agent_random_seq      = soc_ifc_subenv_ss_mode_ctrl_agent_random_seq_t::type_id::create("soc_ifc_subenv_ss_mode_ctrl_agent_random_seq");
    soc_ifc_subenv_ss_mode_status_agent_responder_seq = soc_ifc_subenv_ss_mode_status_agent_responder_seq_t::type_id::create("soc_ifc_subenv_ss_mode_status_agent_responder_seq");
    soc_ifc_subenv_mbox_sram_agent_responder_seq      = soc_ifc_subenv_mbox_sram_agent_responder_seq_t::type_id::create("soc_ifc_subenv_mbox_sram_agent_responder_seq");

    // Handle to the responder sequence for getting response transactions
    soc_ifc_env_bringup_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_bringup_seq.ss_mode_status_agent_rsp_seq = soc_ifc_subenv_ss_mode_status_agent_responder_seq;
    soc_ifc_env_mbox_rom_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_mbox_rom_seq.ss_mode_status_agent_rsp_seq = soc_ifc_subenv_ss_mode_status_agent_responder_seq;
    soc_ifc_env_axi_user_init_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;

    reg_model.reset();
    axi_user_obj.set_addr_user(reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_AXI_USER[0].AXI_USER.get_reset("HARD"));
    fork
        monitor_fatal_error(body_done, monitor_ready, monitor_done);
    join_none
    wait(monitor_ready);
    #0;

    // Start RESPONDER sequences here
    fork
        soc_ifc_subenv_soc_ifc_status_agent_responder_seq.start(soc_ifc_subenv_soc_ifc_status_agent_sequencer);
        soc_ifc_subenv_mbox_sram_agent_responder_seq.start(soc_ifc_subenv_mbox_sram_agent_sequencer);
        soc_ifc_subenv_ss_mode_status_agent_responder_seq.start(soc_ifc_subenv_ss_mode_status_agent_sequencer);
    join_none

    fork
        forever @(soc_ifc_subenv_soc_ifc_status_agent_responder_seq.new_rsp) sts_rsp_count++;
    join_none

    // Start INITIATOR sequences here
    if(!soc_ifc_env_bringup_seq.randomize())
        `uvm_fatal("CALIPTRA_TOP_ROM_TEST", "caliptra_top_rom_sequence::body() - soc_ifc_env_bringup_seq randomization failed")
    soc_ifc_env_bringup_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

    `uvm_info("CALIPTRA_TOP_BRINGUP", "SoC completed poweron and observed reset deassertion to system", UVM_LOW)

`ifndef CALIPTRA_INTERNAL_TRNG
    `uvm_info("CALIPTRA_TOP_ROM_TEST", "Initiating TRNG responder sequence in an infinite loop to handle ROM TRNG requests", UVM_LOW)
    fork
        forever begin
            soc_ifc_env_trng_write_data_seq = soc_ifc_env_trng_write_data_sequence_t::type_id::create("soc_ifc_env_trng_write_data_seq");
            soc_ifc_env_trng_write_data_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
            soc_ifc_env_trng_write_data_seq.ss_mode_status_agent_rsp_seq = soc_ifc_subenv_ss_mode_status_agent_responder_seq;
            if (!soc_ifc_env_trng_write_data_seq.randomize())
              `uvm_fatal("CALIPTRA_TOP_ROM_TEST", $sformatf("caliptra_top_rom_sequence::body() - %s randomization failed", soc_ifc_env_trng_write_data_seq.get_type_name()));
            soc_ifc_env_trng_write_data_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);
        end
    join_none
`else
    `uvm_info("CALIPTRA_TOP_ROM_TEST", "Not initiating TRNG responder sequence to handle ROM TRNG requests because INTERNAL TRNG is enabled", UVM_LOW)
`endif

    if(!soc_ifc_env_axi_user_init_seq.randomize())
        `uvm_fatal("CALIPTRA_TOP_ROM_TEST", "caliptra_top_rom_sequence::body() - soc_ifc_env_axi_user_init_seq randomization failed");
    soc_ifc_env_axi_user_init_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);

    run_firmware_init(soc_ifc_env_mbox_rom_seq);

    // After firmware init, wait for ICCM_LOCK to be set, indicating transition from ROM to FMC
    while (reg_model.soc_ifc_reg_rm.internal_iccm_lock.lock.get_mirrored_value() != 1)
        soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(10);

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(400000);
      soc_ifc_subenv_cptra_ctrl_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_ss_mode_ctrl_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_soc_ifc_status_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_cptra_status_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_ss_mode_status_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_mbox_sram_agent_config.wait_for_num_clocks(4000);
    join

    body_done = 1'b1;
    wait(monitor_done);

    // pragma uvmf custom body end
  endtask

endclass
