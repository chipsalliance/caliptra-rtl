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

class caliptra_top_fw_update_sequence extends caliptra_top_bench_sequence_base;

  `uvm_object_utils( caliptra_top_fw_update_sequence );

  typedef soc_ifc_env_bringup_sequence soc_ifc_env_bringup_sequence_t;
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
    int sts_rsp_count = 0;
    bit mailbox_locked = 1'b1;
    bit ready_for_fw = 1'b0;
    bit ready_for_rt = 1'b0;
    bit [7:0] rt_fw [32768][3:0];
    int firmware_iccm_length;
    int firmware_dccm_length;
    int firmware_iccm_end;
    int firmware_end;
    int fw_rd_ptr;
    uvm_status_e sts;
    uvm_reg_data_t rdata;
    uvm_reg_data_t wdata;
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

    if (soc_ifc_subenv_soc_ifc_status_agent_responder_seq == null)
    `uvm_error("FW_UPD_SEQ", "SOC_IFC ENV bringup sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")
    fork
      forever begin
          @(soc_ifc_subenv_soc_ifc_status_agent_responder_seq.new_rsp) sts_rsp_count++;
      end
    join_none

    `uvm_info("FW_UPD_SEQ", "Starting soc_ifc_env_bringup_seq", UVM_LOW)

    soc_ifc_env_bringup_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);
//    caliptra_top_env_seq.start(top_configuration.vsqr);

    `uvm_info("FW_UPD_SEQ", "SoC completed poweron and observed reset deassertion to system", UVM_LOW)

    `uvm_info("FW_UPD_SEQ", "Waiting for ready for fw to assert", UVM_MEDIUM)

    //Wait for ready for fw to be asserted
    while(!ready_for_fw) begin
        wait (sts_rsp_count > 0);
        `uvm_info("FW_UPD_SEQ", "Received response from status agent", UVM_MEDIUM)
        ready_for_fw = soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.ready_for_fw_push;
        `uvm_info("FW_UPD_SEQ", $sformatf("Ready for FW bit set to: %h", ready_for_fw), UVM_MEDIUM)
        sts_rsp_count--;
    end
    `uvm_info("FW_UPD_SEQ", "Ready for FW asserted, begin FW push", UVM_LOW)

    //Step through the mailbox state machine to trigger interrupt
    //Acquire the mailbox lock
    while(mailbox_locked) begin
      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(50);
      reg_model.mbox_csr_rm.mbox_lock.read(sts, rdata, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
      mailbox_locked = rdata[0];
    end
    //Mark the mailbox locked now that we acquired it
    mailbox_locked = 1'b1;
    reg_model.mbox_csr_rm.mbox_cmd.write(sts, `UVM_REG_DATA_WIDTH'(32'hba5eba11), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    reg_model.mbox_csr_rm.mbox_dlen.write(sts, `UVM_REG_DATA_WIDTH'(32'hFFFF), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    reg_model.mbox_csr_rm.mbox_execute.write(sts, `UVM_REG_DATA_WIDTH'(1), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    //This only works because FW is pre-loaded. Otherwise we need to actually read the .hex and write it to mailbox

    //read FW from file and write to mailbox
    $readmemh("caliptra_rt.hex", rt_fw);
    //Read the first dword, that's the length of ICCM location
    firmware_iccm_length = int'(rt_fw[0][3:0]);
    firmware_iccm_end = firmware_iccm_length + 32'd16;
    //DCCM length is printed at end of ICCM
    firmware_dccm_length = int'(rt_fw[firmware_iccm_end>>2][3:0]);
    //firmware end is after ICCM, DCCM and the two lines (16 bytes) of length encodings
    firmware_end = firmware_iccm_end + firmware_dccm_length + 32'd16;

    `uvm_info("FW_UPD_SEQ", $sformatf("Firmware ICCM length: %h", int'(firmware_iccm_length)), UVM_MEDIUM);
    `uvm_info("FW_UPD_SEQ", $sformatf("Firmware ICCM end: %h", firmware_iccm_end), UVM_MEDIUM);
    `uvm_info("FW_UPD_SEQ", $sformatf("Firmware DCCM length: %h", int'(firmware_dccm_length)), UVM_MEDIUM);
    `uvm_info("FW_UPD_SEQ", $sformatf("Firmware end: %h", firmware_end), UVM_MEDIUM);

    //Mailbox API to send RT FW
    //Acquire the mailbox lock
    while(mailbox_locked) begin
      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(50);
      reg_model.mbox_csr_rm.mbox_lock.read(sts, rdata, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
      mailbox_locked = rdata[0];
    end
    //Mark the mailbox locked now that we acquired it
    mailbox_locked = 1'b1;
    reg_model.mbox_csr_rm.mbox_cmd.write(sts, `UVM_REG_DATA_WIDTH'(32'hbabecafe), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    reg_model.mbox_csr_rm.mbox_dlen.write(sts, `UVM_REG_DATA_WIDTH'(firmware_end), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    
    for (fw_rd_ptr = 0; fw_rd_ptr < firmware_end; fw_rd_ptr++) begin
      wdata = uvm_reg_data_t'({rt_fw[fw_rd_ptr][3],rt_fw[fw_rd_ptr][2],rt_fw[fw_rd_ptr][1],rt_fw[fw_rd_ptr][0]});
      reg_model.mbox_csr_rm.mbox_datain.write(sts, wdata, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    end
    reg_model.mbox_csr_rm.mbox_execute.write(sts, `UVM_REG_DATA_WIDTH'(1), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);

    //Wait for ready for rt to be asserted
    while(!ready_for_rt) begin
      wait (sts_rsp_count > 0);
      `uvm_info("FW_UPD_SEQ", "Received response from status agent", UVM_MEDIUM)
      ready_for_rt = soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.ready_for_runtime;
      `uvm_info("FW_UPD_SEQ", $sformatf("Ready for RT bit set to: %h", ready_for_rt), UVM_MEDIUM)
      sts_rsp_count--;
    end   

    //Sending RT firmware again to trigger the firmware update reset

    //Mailbox API to send RT FW
    //Acquire the mailbox lock
    while(mailbox_locked) begin
      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(50);
      reg_model.mbox_csr_rm.mbox_lock.read(sts, rdata, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
      mailbox_locked = rdata[0];
    end
    //Mark the mailbox locked now that we acquired it
    mailbox_locked = 1'b1;
    reg_model.mbox_csr_rm.mbox_cmd.write(sts, `UVM_REG_DATA_WIDTH'(32'hbabecafe), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    reg_model.mbox_csr_rm.mbox_dlen.write(sts, `UVM_REG_DATA_WIDTH'(firmware_end), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    
    for (fw_rd_ptr = 0; fw_rd_ptr < firmware_end; fw_rd_ptr++) begin
      wdata = uvm_reg_data_t'({rt_fw[fw_rd_ptr][3],rt_fw[fw_rd_ptr][2],rt_fw[fw_rd_ptr][1],rt_fw[fw_rd_ptr][0]});
      reg_model.mbox_csr_rm.mbox_datain.write(sts, wdata, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    end
    reg_model.mbox_csr_rm.mbox_execute.write(sts, `UVM_REG_DATA_WIDTH'(1), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(80000);
      soc_ifc_subenv_cptra_ctrl_agent_config.wait_for_num_clocks(80000);
      soc_ifc_subenv_soc_ifc_status_agent_config.wait_for_num_clocks(80000);
      soc_ifc_subenv_cptra_status_agent_config.wait_for_num_clocks(80000);
    join

    // pragma uvmf custom body end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

