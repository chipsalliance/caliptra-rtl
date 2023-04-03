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
//----------------------------------------------------------------------
//
// DESCRIPTION: Sequence to wait for Mailbox commands (from SoC) and
//              respond/handle the command
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_cptra_mbox_handler_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


  `uvm_object_utils( soc_ifc_env_cptra_mbox_handler_sequence )

    cptra_status_agent_responder_seq_t cptra_status_agent_rsp_seq;

  mbox_op_s op;
  int mbox_resp_expected_dlen = 0; // Number of response data bytes to provide
  uvm_status_e reg_sts;

  extern virtual task mbox_wait_for_command(output op_sts_e op_sts);
  extern virtual task mbox_get_command();
  extern virtual task mbox_pop_dataout();
  extern virtual task mbox_push_datain();
  extern virtual task mbox_set_status();
  extern virtual task mbox_check_fsm();


  function new(string name = "" );
    super.new(name);
  endfunction

  virtual function void do_kill();
    // FIXME gracefully terminate any AHB requests pending?
    reg_model.soc_ifc_AHB_map.get_sequencer().stop_sequences(); // Kill any pending AHB transfers
  endfunction

  virtual task body();

    int sts_rsp_count = 0;
    op_sts_e op_sts;
    reg_model = configuration.soc_ifc_rm;

    if (cptra_status_agent_rsp_seq == null)
        `uvm_fatal("CPTRA_MBOX_HANDLER", "SOC_IFC ENV caliptra mailbox handler sequence expected a handle to the cptra status agent responder sequence (from bench-level sequence) but got null!")
    fork
        forever begin
            @(cptra_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    // Wait for a mailbox command to be received
    mbox_wait_for_command(op_sts);
    if (op_sts != CPTRA_SUCCESS) begin
        `uvm_error("MBOX_SEQ", "Unsuccessful return code from wait_for_command_avail()")
    end

    // Get COMMAND
    mbox_get_command();

    // Get DATAOUT
    mbox_pop_dataout();

    // If resp data is required, set DATAIN
    if (op.cmd.cmd_s.resp_reqd) begin
        mbox_push_datain();
    end

    // Set STATUS
    mbox_set_status();

    // Check FSM status
    configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(2); // Takes a few cycles for FSM update to propagate into register
    mbox_check_fsm();

    // Check new responses (might be an interrupt? Nothing else expected)
    if (sts_rsp_count) `uvm_warning("CPTRA_MBOX_HANDLER", "Unexpected cptra_status response!")

  endtask

endclass

task soc_ifc_env_cptra_mbox_handler_sequence::mbox_wait_for_command(output op_sts_e op_sts);
    uvm_reg_data_t data;
    op_sts = CPTRA_TIMEOUT;
    reg_model.mbox_csr_rm.mbox_execute.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    while (!data[reg_model.mbox_csr_rm.mbox_execute.execute.get_lsb_pos()]) begin
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(200);
        reg_model.mbox_csr_rm.mbox_execute.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    end
    op_sts = CPTRA_SUCCESS;
endtask

task soc_ifc_env_cptra_mbox_handler_sequence::mbox_get_command();
    uvm_reg_data_t data;
    reg_model.mbox_csr_rm.mbox_cmd.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("MBOX_SEQ", "Register access failed (mbox_cmd)")
    op.cmd = data;
    reg_model.mbox_csr_rm.mbox_dlen.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("MBOX_SEQ", "Register access failed (mbox_dlen)")
    op.dlen = data;
endtask

task soc_ifc_env_cptra_mbox_handler_sequence::mbox_pop_dataout();
    int ii;
    uvm_reg_data_t data;
    for (ii=0; ii < op.dlen; ii+=4) begin
        reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        if (reg_sts != UVM_IS_OK)
            `uvm_error("MBOX_SEQ", "Register access failed (mbox_dataout)")
        if (ii == 4) begin
            // dword 1 of data indicates number of response bytes requested
            mbox_resp_expected_dlen = data;
        end
    end
endtask

task soc_ifc_env_cptra_mbox_handler_sequence::mbox_push_datain();
    uvm_reg_data_t data;
    int ii;
    if (mbox_resp_expected_dlen == 0) begin
        `uvm_error("MBOX_SEQ", "Command received with response data requested, but size of expected response data is 0!")
    end
    for (ii=0; ii < mbox_resp_expected_dlen; ii+=4) begin
        if (!std::randomize(data)) `uvm_error("MBOX_SEQ", "Failed to randomize data")
        reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        if (reg_sts != UVM_IS_OK)
            `uvm_error("MBOX_SEQ", "Register access failed (mbox_datain)")
    end
endtask

task soc_ifc_env_cptra_mbox_handler_sequence::mbox_set_status();
    mbox_status_e status;
    uvm_reg_data_t data;
    status = op.cmd.cmd_s.resp_reqd ? DATA_READY : CMD_COMPLETE;
    data = uvm_reg_data_t'(status) << reg_model.mbox_csr_rm.mbox_status.status.get_lsb_pos();
    reg_model.mbox_csr_rm.mbox_status.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("MBOX_SEQ", "Register access failed (mbox_status)")
endtask

task soc_ifc_env_cptra_mbox_handler_sequence::mbox_check_fsm();
    uvm_reg_data_t data;
    mbox_fsm_state_e fsm_state;

    reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("MBOX_SEQ", "Register access failed (mbox_status)")

    fsm_state = mbox_fsm_state_e'(data >> reg_model.mbox_csr_rm.mbox_status.mbox_fsm_ps.get_lsb_pos());
    if (op.cmd.cmd_s.resp_reqd && fsm_state != MBOX_EXECUTE_SOC) begin
        `uvm_error("MBOX_SEQ", $sformatf("Unexpected mailbox FSM state: %p", fsm_state))
    end
endtask
