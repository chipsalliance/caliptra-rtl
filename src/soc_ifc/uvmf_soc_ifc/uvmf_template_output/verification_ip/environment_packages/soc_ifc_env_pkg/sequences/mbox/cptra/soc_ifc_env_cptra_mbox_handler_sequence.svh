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

  mbox_op_s op;
  int mbox_resp_expected_dlen = 0; // Number of response data bytes to provide
  uvm_status_e reg_sts;
  rand bit inject_force_unlock;
  rand longint unsigned force_unlock_delay_cycles;

  bit unlock_proc_active = 1'b0;
  event in_report_reg_sts;

  extern virtual task mbox_wait_for_command(output op_sts_e op_sts);
  extern virtual task mbox_get_command();
  extern virtual task mbox_pop_dataout();
  extern virtual task mbox_push_datain();
  extern virtual task mbox_set_status();
  extern virtual task mbox_check_fsm();
  extern virtual task mbox_wait_and_force_unlock();
  extern virtual function void report_reg_sts(uvm_status_e reg_sts, string name);

  // Constrain force_unlock to be a rare event, but it might occur at any time
  constraint mbox_force_unlock_dist_c { inject_force_unlock dist {1:/1, 0:/500}; }
  // Choose a nice bell-ish curve for delay amount
  constraint force_unlock_delay_c { force_unlock_delay_cycles dist {
                                        [64'h1      :64'hF                  ] :/ 10,
                                        [64'h10     :64'h1FF                ] :/ 100,
                                        [64'h200    :64'h3FF                ] :/ 125,
                                        [64'h400    :64'hFFF                ] :/ 50,
                                        [64'h1000   :64'hFFFF               ] :/ 10,
                                        [64'h10000  :64'hF_FFFF             ] :/ 5,
                                        [64'h10_0000:64'hFFFF_FFFF_FFFF_FFFF] :/ 1
                                    }; };

  //==========================================
  // Function:    new
  // Description: Constructor
  //==========================================
  function new(string name = "" );
    super.new(name);
  endfunction

  //==========================================
  // Function:    do_kill
  // Description: Called as part of sequencer.stop_sequences
  //              when invoked on the sequencer that is running
  //              this sequence.
  //==========================================
  virtual function void do_kill();
    // FIXME gracefully terminate any AHB requests pending?
    reg_model.soc_ifc_AHB_map.get_sequencer().stop_sequences(); // Kill any pending AHB transfers
  endfunction

  //==========================================
  // Task:        body
  // Description: Implement main functionality for
  //              Caliptra-side handling of received
  //              mailbox request.
  //==========================================
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

    fork
        begin: ALL_TIME_CONSUMING_TASKS
            // Wait for a mailbox command to be received
            mbox_wait_for_command(op_sts);
            if (op_sts != CPTRA_SUCCESS) begin
                `uvm_error("CPTRA_MBOX_HANDLER", "Unsuccessful return code from wait_for_command_avail()")
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

            // Wait for the command to complete.
            // Either we clear the lock, or the SOC requestor does.
            while (reg_model.mbox_csr_rm.mbox_lock.lock.get_mirrored_value()) begin
                configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(1);
            end
        end: ALL_TIME_CONSUMING_TASKS
        begin: DO_FORCE_UNLOCK
            mbox_wait_and_force_unlock();
            // After forcibly unlocking mailbox, kill any remaining activity.
            // If force unlock is randomized to "off" for this run
            // of the sequence, this won't ever run.
            disable ALL_TIME_CONSUMING_TASKS;
        end: DO_FORCE_UNLOCK
    join_any
    if (unlock_proc_active) wait(in_report_reg_sts.triggered); /* Wait for pending bus transfers to finish to avoid deadlock */
    disable DO_FORCE_UNLOCK;

    // Check new responses (might be an interrupt? Nothing else expected)
    if (sts_rsp_count) `uvm_warning("CPTRA_MBOX_HANDLER", "Unexpected cptra_status response!")

    // Ending message
    `uvm_info("CPTRA_MBOX_HANDLER", "Mailbox flow complete. Caliptra mbox handler is exiting", UVM_MEDIUM)

  endtask

endclass

//==========================================
// Task:        mbox_wait_for_command
// Description: Poll for availability of new
//              mailbox request, indicated by:
//                - mbox_execute = 1
//                - intr status = 1
//==========================================
task soc_ifc_env_cptra_mbox_handler_sequence::mbox_wait_for_command(output op_sts_e op_sts);
    uvm_reg_data_t data;
    op_sts = CPTRA_TIMEOUT;
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "notif_internal_intr_r");
    while (!data[reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_cmd_avail_sts.get_lsb_pos()]) begin
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(200);
        reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        report_reg_sts(reg_sts, "notif_internal_intr_r");
    end
    data &= uvm_reg_data_t'(1) << reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_cmd_avail_sts.get_lsb_pos();
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "notif_internal_intr_r");
    op_sts = CPTRA_SUCCESS;
endtask

//==========================================
// Task:        mbox_get_command
// Description: Read the mbox_cmd and mbox_dlen registers
//==========================================
task soc_ifc_env_cptra_mbox_handler_sequence::mbox_get_command();
    uvm_reg_data_t data;
    reg_model.mbox_csr_rm.mbox_cmd.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_cmd");
    op.cmd = data;
    reg_model.mbox_csr_rm.mbox_dlen.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_dlen");
    op.dlen = data;
endtask

//==========================================
// Task:        mbox_pop_dataout
// Description: Read the mbox_dataout register
//              in a loop until all data is received
//==========================================
task soc_ifc_env_cptra_mbox_handler_sequence::mbox_pop_dataout();
    int ii;
    uvm_reg_data_t data;
    for (ii=0; ii < op.dlen; ii+=4) begin
        reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        report_reg_sts(reg_sts, "mbox_dataout");
        if (ii == 4) begin
            // dword 1 of data indicates number of response bytes requested
            mbox_resp_expected_dlen = data;
        end
    end
endtask

//==========================================
// Task:        mbox_push_datain
// Description: Write data to mbox_datain register
//              to provide any requested response data for
//              the mailbox flow
//==========================================
task soc_ifc_env_cptra_mbox_handler_sequence::mbox_push_datain();
    uvm_reg_data_t data;
    int ii;
    if (mbox_resp_expected_dlen == 0) begin
        `uvm_error("CPTRA_MBOX_HANDLER", "Command received with response data requested, but size of expected response data is 0!")
    end
    // Write random datain
    for (ii=0; ii < mbox_resp_expected_dlen; ii+=4) begin
        if (!std::randomize(data)) `uvm_error("CPTRA_MBOX_HANDLER", "Failed to randomize data")
        reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        report_reg_sts(reg_sts, "mbox_datain");
    end
endtask

//==========================================
// Task:        mbox_set_status
// Description: Write a new value to mbox_status.status
//              to transfer control back to SOC to finalize operation.
//==========================================
task soc_ifc_env_cptra_mbox_handler_sequence::mbox_set_status();
    mbox_status_e status;
    uvm_reg_data_t data;
    // Set mbox_dlen to resp size
    reg_model.mbox_csr_rm.mbox_dlen.write(reg_sts, mbox_resp_expected_dlen, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_dlen");
    // Determine which status to set and perform the write
    status = op.cmd.cmd_s.resp_reqd ? DATA_READY : CMD_COMPLETE;
    data = uvm_reg_data_t'(status) << reg_model.mbox_csr_rm.mbox_status.status.get_lsb_pos();
    reg_model.mbox_csr_rm.mbox_status.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_status");
endtask

//==========================================
// Task:        mbox_check_fsm
// Description: Read mbox_status.mbox_fsm_ps to confirm
//              state changed as expected.
//==========================================
task soc_ifc_env_cptra_mbox_handler_sequence::mbox_check_fsm();
    uvm_reg_data_t data;
    mbox_fsm_state_e fsm_state;

    reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_status");

    fsm_state = mbox_fsm_state_e'(data >> reg_model.mbox_csr_rm.mbox_status.mbox_fsm_ps.get_lsb_pos());
    if (op.cmd.cmd_s.resp_reqd && fsm_state != MBOX_EXECUTE_SOC) begin
        `uvm_error("CPTRA_MBOX_HANDLER", $sformatf("Unexpected mailbox FSM state: %p", fsm_state))
    end
endtask

//==========================================
// Task:        mbox_wait_and_force_unlock
// Description: If enabled, wait for some random amount of time and
//              then do a write to mbox_unlock to forcibly end
//              the current mailbox flow.
//==========================================
task soc_ifc_env_cptra_mbox_handler_sequence::mbox_wait_and_force_unlock();
    uvm_reg_data_t data;
    if (!inject_force_unlock) begin
        // This task never exits if force unlock is disabled
        forever configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(1000);
    end
    configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(force_unlock_delay_cycles);
    unlock_proc_active = 1'b1;
    // After waiting the requisite number of cycles, check mbox_status.
    // If SOC doesn't currently have the lock, doing a force-unlock has no
    // effect. Poll until soc_has_lock is set.
    // NOTE: Making this check the reg-model mirror instead of actual polling
    //       might be beneficial?
    reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_status");
    while (!data[reg_model.mbox_csr_rm.mbox_status.soc_has_lock.get_lsb_pos()]) begin
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(50); /* short 500ns between reads */
        reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        report_reg_sts(reg_sts, "mbox_status");
    end
    `uvm_info("CPTRA_MBOX_HANDLER","Executing force unlock of mailbox. CPTRA mbox flow handler will exit after unlock.", UVM_MEDIUM)
    reg_model.mbox_csr_rm.mbox_unlock.write(reg_sts, uvm_reg_data_t'(1) << reg_model.mbox_csr_rm.mbox_unlock.unlock.get_lsb_pos(), UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_unlock");
    // Clear any interrupts as well, if they weren't cleared before unlock
    data = uvm_reg_data_t'(1) << reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_cmd_avail_sts.get_lsb_pos();
    `uvm_info("CPTRA_MBOX_HANDLER", "Doing clear notif intr", UVM_LOW)
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "notif_internal_intr_r");
    unlock_proc_active = 1'b0;
    `uvm_info("CPTRA_MBOX_HANDLER", "Done clearing notif intr", UVM_LOW)
endtask

//==========================================
// Function:    report_reg_sts
// Description: Generate informative messages about the result
//              of the most recent AHB transfer.
//              Since this is called after every reg access, it is
//              used to indicate the end of a reg access and trigger
//              mbox force unlock (if enabled)
//==========================================
function void soc_ifc_env_cptra_mbox_handler_sequence::report_reg_sts(uvm_status_e reg_sts, string name);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("CPTRA_MBOX_HANDLER", $sformatf("Register access failed (%s)", name))
    else
        `uvm_info("CPTRA_MBOX_HANDLER",
                  $sformatf("Register access to (%s), reg_sts: %p", name, reg_sts),
                  UVM_HIGH)
    -> in_report_reg_sts;
endfunction
