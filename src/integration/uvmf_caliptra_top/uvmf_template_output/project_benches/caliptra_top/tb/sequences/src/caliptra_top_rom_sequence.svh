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
  // Local handle to register model for convenience
  soc_ifc_reg_model_top reg_model;

  int sts_rsp_count = 0;

  function new(string name = "" );
    super.new(name);
    reg_model = top_configuration.soc_ifc_subenv_config.soc_ifc_rm;
  endfunction

  // ****************************************************************************
  virtual task run_firmware_init(soc_ifc_env_mbox_rom_fw_sequence_t rom_seq);
    bit ready_for_fw = 0;
    bit ready_for_rt = 0;
    while (!ready_for_fw) begin
        while(!sts_rsp_count)soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(1); // Wait for new status updates
        `uvm_info("CALIPTRA_TOP_ROM_TEST", "Observed status response, checking contents", UVM_DEBUG)
        sts_rsp_count = 0; // We only care about the latest rsp, so even if count > 1, reset back to 0
        ready_for_fw = soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.ready_for_fw_push;
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

    caliptra_top_env_seq = caliptra_top_env_sequence_base_t::type_id::create("caliptra_top_env_seq");
    soc_ifc_env_bringup_seq = soc_ifc_env_rom_bringup_sequence_t::type_id::create("soc_ifc_env_bringup_seq");
    soc_ifc_env_mbox_rom_seq = soc_ifc_env_mbox_rom_fw_sequence_t::type_id::create("soc_ifc_env_mbox_rom_seq");

    soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq     = soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_ctrl_agent_random_seq");
    soc_ifc_subenv_soc_ifc_status_agent_responder_seq  = soc_ifc_subenv_soc_ifc_status_agent_responder_seq_t::type_id::create("soc_ifc_subenv_soc_ifc_status_agent_responder_seq");
    soc_ifc_subenv_mbox_sram_agent_responder_seq      = soc_ifc_subenv_mbox_sram_agent_responder_seq_t::type_id::create("soc_ifc_subenv_mbox_sram_agent_responder_seq");

    // Handle to the responder sequence for getting response transactions
    soc_ifc_env_bringup_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;
    soc_ifc_env_mbox_rom_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_subenv_soc_ifc_status_agent_responder_seq;

    reg_model.reset();
    // Start RESPONDER sequences here
    fork
        soc_ifc_subenv_soc_ifc_status_agent_responder_seq.start(soc_ifc_subenv_soc_ifc_status_agent_sequencer);
        soc_ifc_subenv_mbox_sram_agent_responder_seq.start(soc_ifc_subenv_mbox_sram_agent_sequencer);
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
            if (!soc_ifc_env_trng_write_data_seq.randomize())
              `uvm_fatal("CALIPTRA_TOP_ROM_TEST", $sformatf("caliptra_top_rom_sequence::body() - %s randomization failed", soc_ifc_env_trng_write_data_seq.get_type_name()));
            soc_ifc_env_trng_write_data_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);
        end
    join_none
`else
    `uvm_info("CALIPTRA_TOP_ROM_TEST", "Not initiating TRNG responder sequence to handle ROM TRNG requests because INTERNAL TRNG is enabled", UVM_LOW)
`endif

    run_firmware_init(soc_ifc_env_mbox_rom_seq);

    // After firmware init, wait for ICCM_LOCK to be set, indicating transition from ROM to FMC
    while (reg_model.soc_ifc_reg_rm.internal_iccm_lock.lock.get_mirrored_value() != 1)
        soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(10);

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_cptra_ctrl_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_soc_ifc_status_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_cptra_status_agent_config.wait_for_num_clocks(4000);
      soc_ifc_subenv_mbox_sram_agent_config.wait_for_num_clocks(4000);
    join

    // pragma uvmf custom body end
  endtask

endclass
