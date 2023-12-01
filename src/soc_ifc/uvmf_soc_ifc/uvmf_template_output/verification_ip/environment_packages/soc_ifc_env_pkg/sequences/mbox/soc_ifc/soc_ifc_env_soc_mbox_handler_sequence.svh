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
// DESCRIPTION: Sequence to wait for Mailbox commands (from uC) and
//              respond/handle the command
// TODO: How to properly exercise PAUSER on receiving a command?
// TODO: Use JTAG i/f to handle uC initiated mbox flow?
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_soc_mbox_handler_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


  `uvm_object_utils( soc_ifc_env_soc_mbox_handler_sequence )

  mbox_op_s op;
  uvm_status_e reg_sts;
  int sts_rsp_count = 0;
  uvm_event in_report_reg_sts;

  // PAUSER tracking/override
  bit [apb5_master_0_params::PAUSER_WIDTH-1:0] mbox_valid_users [6];
  bit mbox_valid_users_initialized = 1'b0;
  caliptra_apb_user apb_user_obj;

  extern virtual task mbox_setup();
  extern virtual task mbox_wait_for_command(output op_sts_e op_sts);
  extern virtual task mbox_get_command();
  extern virtual task mbox_pop_dataout();
  extern virtual task mbox_set_status();
  extern virtual task mbox_check_fsm();
  extern virtual task mbox_wait_done();
  extern virtual task mbox_teardown();

  extern virtual task report_reg_sts(uvm_status_e sts, string name, caliptra_apb_user user_handle = null);


  //==========================================
  // Function:    new
  // Description: Constructor
  //==========================================
  function new(string name = "" );
    super.new(name);

    // Setup a User object to override PAUSER
    apb_user_obj = new();

    // Event
    in_report_reg_sts = new();

  endfunction

  //==========================================
  // Function:    do_kill
  // Description: Called as part of sequencer.stop_sequences
  //              when invoked on the sequencer that is running
  //              this sequence.
  //==========================================
  virtual function void do_kill();
    // FIXME gracefully terminate any APB requests pending?
    reg_model.soc_ifc_APB_map.get_sequencer().stop_sequences(); // Kill any pending APB transfers
  endfunction

  //==========================================
  // Task:        body
  // Description: Implement main functionality for
  //              Caliptra-side handling of received
  //              mailbox request.
  //==========================================
  virtual task body();

    op_sts_e op_sts;
    reg_model = configuration.soc_ifc_rm;

    if (soc_ifc_status_agent_rsp_seq == null)
        `uvm_fatal("SOC_MBOX_HANDLER", "SOC_IFC ENV SOC mailbox handler sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")
    fork
        forever begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    // Setup
    mbox_setup();

    // Wait for a mailbox command to be received
    mbox_wait_for_command(op_sts);
    if (op_sts != CPTRA_SUCCESS) begin
        `uvm_error("SOC_MBOX_HANDLER", "Unsuccessful return code from wait_for_command_avail()")
    end

    // Get COMMAND
    mbox_get_command();
    mbox_pop_dataout();

    // Return control to uC
    mbox_set_status();
    configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(2); // Takes a few cycles for FSM update to propagate into register
    mbox_check_fsm();
    mbox_wait_done();

    // End of Sequence
    mbox_teardown();

  endtask

endclass

//==========================================
// Task:        mbox_setup
// Description: Setup tasks to:
//               - Grab configured mbox_valid_users from reg model
//               - Any other functionality implemented in derived classes
//==========================================
task soc_ifc_env_soc_mbox_handler_sequence::mbox_setup();
    byte ii;

    // Read the valid PAUSER fields from register mirrored value if the local array
    // has not already been overridden from default values
    if (!mbox_valid_users_initialized) begin
        for (ii=0; ii < $size(reg_model.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK); ii++) begin: VALID_USER_LOOP
            if (reg_model.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[ii].LOCK.get_mirrored_value())
                mbox_valid_users[ii] = reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[ii].get_mirrored_value();
            else
                mbox_valid_users[ii] = reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[ii].get_reset("HARD");
        end
        mbox_valid_users[5] = 32'hFFFF_FFFF; /*FIXME hardcoded */
        mbox_valid_users_initialized = 1'b1;
    end
    else begin
        for (ii=0; ii < $size(reg_model.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK); ii++) begin: VALID_USER_CHECK_LOOP
            if (reg_model.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[ii].LOCK.get_mirrored_value() &&
                mbox_valid_users[ii] != reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[ii].get_mirrored_value())
                `uvm_warning("SOC_MBOX_HANDLER", "mbox_valid_users initialized with a value that does not match mirrored value in register model!")
        end
    end

    // Pick a user and use throughout sequence
    if (!apb_user_obj.randomize() with {addr_user inside {mbox_valid_users};})
        `uvm_error("SOC_MBOX_HANDLER", "Failed to randomize APB PAUSER override value")
    else
        `uvm_info("SOC_MBOX_HANDLER", $sformatf("Randomized APB PAUSER override value to 0x%x", apb_user_obj.addr_user), UVM_HIGH)

endtask

//==========================================
// Task:        mbox_wait_for_command
// Description: Poll for availability of new
//              mailbox request, indicated by:
//                - mbox_execute = 1
//                - intr status = 1
//==========================================
task soc_ifc_env_soc_mbox_handler_sequence::mbox_wait_for_command(output op_sts_e op_sts);
    uvm_reg_data_t data;
    bit cmd_avail = 1'b0;
    op_sts = CPTRA_TIMEOUT;

    // Wait for mbox_data_avail to indicate command availability
    while (!cmd_avail) begin
        wait(sts_rsp_count > 0);
        cmd_avail = soc_ifc_status_agent_rsp_seq.rsp.mailbox_data_avail;
        if (!cmd_avail) begin
            `uvm_info("SOC_MBOX_HANDLER", $sformatf("While waiting for mailbox_data_avail, observed an unexpected response on soc_ifc_status_responder_sequence. Contents: %s",soc_ifc_status_agent_rsp_seq.rsp.convert2string()), UVM_HIGH)
        end
        sts_rsp_count--;
    end
    op_sts = CPTRA_SUCCESS;

    if (1) begin
        // Check register values to confirm:
        //  - mbox_execute == 1
        //  - mbox_lock.lock == 1
        //  - mbox_status.soc_has_lock == 0
        reg_model.mbox_csr_rm.mbox_execute.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
        report_reg_sts(reg_sts,"mbox_execute");
        if (!data[reg_model.mbox_csr_rm.mbox_execute.execute.get_lsb_pos()]) begin
            `uvm_error("SOC_MBOX_HANDLER", "SOC observed mailbox_data_avail assertion, but mbox_execute is not set! Was a command submitted?")
            op_sts = CPTRA_FAIL;
        end
        reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
        report_reg_sts(reg_sts,"mbox_lock");
        if (!data[reg_model.mbox_csr_rm.mbox_lock.lock.get_lsb_pos()]) begin
            `uvm_error("SOC_MBOX_HANDLER", "SOC observed mailbox_data_avail assertion, but mbox_lock is not set! Was a command submitted?")
            // FIXME Also, we just now acquired lock, so.... expect catastrophe
            op_sts = CPTRA_FAIL;
        end
        reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
        report_reg_sts(reg_sts,"mbox_status");
//        data >>= reg_model.mbox_csr_rm.mbox_status.status.get_lsb_pos();
//        data &=  (uvm_reg_data_t'(1) << reg_model.mbox_csr_rm.mbox_status.status.get_n_bits()) - uvm_reg_data_t'(1);
//        if (mbox_status_e'(data) != DATA_READY) begin
        if (data[reg_model.mbox_csr_rm.mbox_status.soc_has_lock.get_lsb_pos()]) begin
//            `uvm_error("SOC_MBOX_HANDLER", $sformatf("SOC observed mailbox_data_avail assertion, but mbox_status is has unexpected value [%p]! Was a command submitted?", mbox_status_e'(data)))
            `uvm_error("SOC_MBOX_HANDLER", $sformatf("SOC observed mailbox_data_avail assertion with new command, but mbox_status.soc_has_lock is unexpectedly set!"))
            op_sts = CPTRA_FAIL;
        end
    end
endtask

//==========================================
// Task:        mbox_get_command
// Description: Read the mbox_cmd and mbox_dlen registers
//==========================================
task soc_ifc_env_soc_mbox_handler_sequence::mbox_get_command();
    uvm_reg_data_t data;
    reg_model.mbox_csr_rm.mbox_cmd.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
    report_reg_sts(reg_sts,"mbox_cmd");
    op.cmd = data;
    reg_model.mbox_csr_rm.mbox_dlen.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
    report_reg_sts(reg_sts,"mbox_dlen");
    op.dlen = data;
endtask

//==========================================
// Task:        mbox_pop_dataout
// Description: Read the mbox_dataout register
//              in a loop until all data is received
//==========================================
task soc_ifc_env_soc_mbox_handler_sequence::mbox_pop_dataout();
    int ii;
    uvm_reg_data_t data;
    for (ii=0; ii < op.dlen; ii+=4) begin
        reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
        report_reg_sts(reg_sts,"mbox_dataout");
    end
endtask

//==========================================
// Task:        mbox_set_status
// Description: Write a new value to mbox_status.status
//              to transfer control back to uC to finalize operation.
//==========================================
task soc_ifc_env_soc_mbox_handler_sequence::mbox_set_status();
    mbox_status_e status;
    uvm_reg_data_t data;
    // Determine which status to set and perform the write
    status = CMD_COMPLETE;
    data = uvm_reg_data_t'(status) << reg_model.mbox_csr_rm.mbox_status.status.get_lsb_pos();
    reg_model.mbox_csr_rm.mbox_status.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
    report_reg_sts(reg_sts,"mbox_status");
endtask

//==========================================
// Task:        mbox_check_fsm
// Description: Read mbox_status.mbox_fsm_ps to confirm
//              state changed as expected.
//==========================================
task soc_ifc_env_soc_mbox_handler_sequence::mbox_check_fsm();
    uvm_reg_data_t data;
    mbox_fsm_state_e fsm_state;

    reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
    report_reg_sts(reg_sts,"mbox_status");

    fsm_state = mbox_fsm_state_e'(data >> reg_model.mbox_csr_rm.mbox_status.mbox_fsm_ps.get_lsb_pos());
    if (fsm_state inside {MBOX_IDLE, MBOX_ERROR} && (sts_rsp_count > 0) && soc_ifc_status_agent_rsp_seq.rsp.cptra_error_non_fatal_intr_pending) begin
        `uvm_info("SOC_MBOX_HANDLER", $sformatf("Observed mailbox FSM state: %p, which is not a failure since it corresponds with non_fatal HW interrupt", fsm_state), UVM_MEDIUM)
    end
    else if (fsm_state != MBOX_EXECUTE_UC) begin
        `uvm_error("SOC_MBOX_HANDLER", $sformatf("Unexpected mailbox FSM state: %p", fsm_state))
    end
endtask

//==========================================
// Task:        mbox_wait_done
// Description: Wait for uC to end the mailbox flow as indicated
//              by mbox_lock being relinquished.
//              If necessary, service any cptra HW error (fatal or
//              non_fatal) that occurred.
//==========================================
task soc_ifc_env_soc_mbox_handler_sequence::mbox_wait_done();
    uvm_reg_data_t non_fatal, fatal;

    // Wait for lock to clear
    while(reg_model.mbox_csr_rm.mbox_lock.get_mirrored_value())
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(1);

    // Check for interrupts
    if (sts_rsp_count && (soc_ifc_status_agent_rsp_seq.rsp.cptra_error_non_fatal_intr_pending ||
                          soc_ifc_status_agent_rsp_seq.rsp.cptra_error_fatal_intr_pending)) begin
        // Read status
        reg_model.soc_ifc_reg_rm.CPTRA_HW_ERROR_NON_FATAL.read(reg_sts, non_fatal, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
        report_reg_sts(reg_sts, "CPTRA_HW_ERROR_NON_FATAL");
        reg_model.soc_ifc_reg_rm.CPTRA_HW_ERROR_FATAL.read(reg_sts, fatal, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
        report_reg_sts(reg_sts, "CPTRA_HW_ERROR_FATAL");

        if (~|fatal && ~|non_fatal)
            `uvm_error("SOC_MBOX_HANDLER", $sformatf("Received status response transaction with cptra error asserted [%s] but both fatal and non_fatal registers are 0!", soc_ifc_status_agent_rsp_seq.rsp.convert2string()))

        // Write 1 to clear
        reg_model.soc_ifc_reg_rm.CPTRA_HW_ERROR_NON_FATAL.write(reg_sts, non_fatal, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
        report_reg_sts(reg_sts, "CPTRA_HW_ERROR_NON_FATAL");
        reg_model.soc_ifc_reg_rm.CPTRA_HW_ERROR_FATAL.write(reg_sts, fatal, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
        report_reg_sts(reg_sts, "CPTRA_HW_ERROR_FATAL");
    end
endtask

//==========================================
// Task:        mbox_teardown
// Description: Placeholder task to allow derived classes
//              to add any end-of-sequence functionality.
//==========================================
task soc_ifc_env_soc_mbox_handler_sequence::mbox_teardown();
    // Summary at sequence end
    `uvm_info("SOC_MBOX_HANDLER", $sformatf("FIXME"), UVM_MEDIUM)
endtask

//==========================================
// Function:    report_reg_sts
// Description: Generate informative messages about the result
//              of the most recent APB transfer, accounting for
//              the PAUSER value that was used.
//==========================================
task soc_ifc_env_soc_mbox_handler_sequence::report_reg_sts(uvm_status_e sts, string name, caliptra_apb_user user_handle = null);
    caliptra_apb_user user;
    int waiters = in_report_reg_sts.get_num_waiters();
    in_report_reg_sts.trigger();
    if (user_handle == null) user = this.apb_user_obj;
    else                     user = user_handle;
    // APB error is flagged only for PAUSER that doesn't match the registered
    // values, it does not check that PAUSER matches the exact value in
    // mbox_user that was stored when lock was acquired (this results in a
    // silent error but a successful reg read).
    // Ergo, check against mbox_valid_users instead of pauser_locked.
    if (sts != UVM_IS_OK && user.get_addr_user() inside mbox_valid_users)
        `uvm_error("SOC_MBOX_HANDLER",
                   $sformatf("Register access failed unexpectedly with valid PAUSER! 0x%x (%s)", user.get_addr_user(), name))
    else if (sts == UVM_IS_OK && !(user.get_addr_user() inside mbox_valid_users))
        `uvm_error("SOC_MBOX_HANDLER",
                   $sformatf("Register access passed unexpectedly with invalid PAUSER! 0x%x (%s)", user.get_addr_user(), name))
    else
        `uvm_info("SOC_MBOX_HANDLER",
                  $sformatf("Register access to (%s) with pauser_used_is_valid: %b and sts: %p", name, 1/* this.pauser_used_is_valid()*/, sts),
                  UVM_HIGH)
    if (waiters)
        in_report_reg_sts.wait_off();
    else
        in_report_reg_sts.reset();
endtask
