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

  typedef soc_ifc_env_configuration  soc_ifc_env_configuration_t;
  typedef soc_ifc_env_bringup_sequence #(
          .CONFIG_T(soc_ifc_env_configuration_t)
          )
          soc_ifc_env_bringup_sequence_t;
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
    bit ready_for_fw = 1'b0;
    bit ready_for_rt = 1'b0;
    bit [7:0] caliptra_rt [32768][3:0]; //FIXME
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
    `uvm_error("SOC_IFC_BRINGUP", "SOC_IFC ENV bringup sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")
    fork
      forever begin
          @(soc_ifc_subenv_soc_ifc_status_agent_responder_seq.new_rsp) sts_rsp_count++;
      end
    join_none

    `uvm_info("CALIPTRA_TOP_BRINGUP", "Starting soc_ifc_env_bringup_seq", UVM_LOW)

    soc_ifc_env_bringup_seq.start(top_configuration.soc_ifc_subenv_config.vsqr);
//    caliptra_top_env_seq.start(top_configuration.vsqr);

    `uvm_info("CALIPTRA_TOP_BRINGUP", "SoC completed poweron and observed reset deassertion to system", UVM_LOW)

    `uvm_info("SOC_IFC_BRINGUP", "Waiting for ready for fw to assert", UVM_MEDIUM)

    //Wait for ready for fw to be asserted
    while(!ready_for_fw) begin
        wait (sts_rsp_count > 0);
        `uvm_info("SOC_IFC_BRINGUP", "Received response from status agent", UVM_MEDIUM)
        ready_for_fw = soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.ready_for_fw_push;
        `uvm_info("SOC_IFC_BRINGUP", $sformatf("Ready for FW bit set to: %h", ready_for_fw), UVM_MEDIUM)
        sts_rsp_count--;
    end
    `uvm_info("SOC_IFC_BRINGUP", "Ready for FW asserted, begin FW push", UVM_LOW)

    //Step through the mailbox state machine
    //Acquire the mailbox lock - this really should poll - FIXME
    reg_model.mbox_csr_rm.mbox_lock.lock.read(sts, rdata, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    reg_model.mbox_csr_rm.mbox_cmd.write(sts, `UVM_REG_DATA_WIDTH'(32'hba5eba11), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    reg_model.mbox_csr_rm.mbox_dlen.write(sts, `UVM_REG_DATA_WIDTH'(32'hFFFF), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    reg_model.mbox_csr_rm.mbox_execute.write(sts, `UVM_REG_DATA_WIDTH'(1), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    //This only works because FW is pre-loaded. Otherwise we need to actually read the .hex and write it to mailbox

    //Wait for ready for fw to be asserted
    while(!ready_for_rt) begin
        wait (sts_rsp_count > 0);
        `uvm_info("SOC_IFC_BRINGUP", "Received response from status agent", UVM_MEDIUM)
        ready_for_rt = soc_ifc_subenv_soc_ifc_status_agent_responder_seq.rsp.ready_for_runtime;
        `uvm_info("SOC_IFC_BRINGUP", $sformatf("Ready for RT bit set to: %h", ready_for_rt), UVM_MEDIUM)
        sts_rsp_count--;
    end    
    
    //Step through the mailbox state machine
    //Acquire the mailbox lock - this really should poll - FIXME
    reg_model.mbox_csr_rm.mbox_lock.lock.read(sts, rdata, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    reg_model.mbox_csr_rm.mbox_cmd.write(sts, `UVM_REG_DATA_WIDTH'(32'hbabecafe), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    reg_model.mbox_csr_rm.mbox_dlen.write(sts, `UVM_REG_DATA_WIDTH'(32'hFFFF), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    //read FW from file and write to mailbox
    $readmemh("caliptra_rt.hex",  caliptra_rt,0,32'h00007FFF);
    for (int rt_fw_ptr = 0; rt_fw_ptr < 32'h00001FFF; rt_fw_ptr++) begin
      wdata = uvm_reg_data_t'({caliptra_rt[rt_fw_ptr][3],caliptra_rt[rt_fw_ptr][2],caliptra_rt[rt_fw_ptr][1],caliptra_rt[rt_fw_ptr][0]});
      reg_model.mbox_csr_rm.mbox_datain.write(sts, wdata, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    end
    reg_model.mbox_csr_rm.mbox_execute.write(sts, `UVM_REG_DATA_WIDTH'(1), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    //This only works because FW is pre-loaded. Otherwise we need to actually read the .hex and write it to mailbox

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      soc_ifc_subenv_soc_ifc_ctrl_agent_config.wait_for_num_clocks(400000);
      soc_ifc_subenv_cptra_ctrl_agent_config.wait_for_num_clocks(400000);
      soc_ifc_subenv_soc_ifc_status_agent_config.wait_for_num_clocks(400000);
      soc_ifc_subenv_cptra_status_agent_config.wait_for_num_clocks(400000);
    join

    if (1) // TODO -- Move to Scoreboard
        $display("* TESTCASE PASSED");
    else
        $display("* TESTCASE FAILED");
    // pragma uvmf custom body end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

