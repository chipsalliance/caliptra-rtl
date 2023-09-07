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
//----------------------------------------------------------------------
//
// DESCRIPTION: Base sequence to perform a mailbox command within the
//              soc_ifc environment.
//              Initiates a Mailbox command from the uC-side to be handled
//              by SoC receiver.
//              Extended to provide additional functionality.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_cptra_mbox_req_sequence_base extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


  `uvm_object_utils( soc_ifc_env_cptra_mbox_req_sequence_base )





  rand mbox_op_s mbox_op_rand;
  int sts_rsp_count;
  uvm_status_e reg_sts;
  bit mbox_sts_is_error = 0;
  rand bit do_ahb_lock_check;
  rand bit retry_failed_reg_axs;
  // Certain random sequences force the command to be outside of the defined
  // options from mbox_cmd_e, such that truly random behavior does not violate
  // expected activity for the command opcode. To do this, we need to be able
  // to build a constraint to exclude the enum values, which requires this
  // array of all possible enumerated values.
  mbox_cmd_e defined_cmds[];

  struct packed {
      bit [31:0] mbox_user; /* Expected value of mbox_user reg when mbox lock acquired */
      bit        locked;
  } mbox_user_locked = '{mbox_user: '1, locked: 1'b0};

  extern virtual task mbox_setup();
  extern virtual task mbox_acquire_lock(output op_sts_e op_sts);
  extern virtual task mbox_set_cmd(input mbox_op_s op);
  extern virtual task mbox_push_datain();
  extern virtual task mbox_execute();
  extern virtual task mbox_check_status(output mbox_status_e data, output mbox_fsm_state_e state);
  extern virtual task mbox_poll_status();
  extern virtual task mbox_clr_execute();
  extern virtual task mbox_teardown();

  extern virtual function void report_reg_sts(uvm_status_e reg_sts, string name);

  // Constrain command to not be firmware, not request a response
  constraint mbox_cmd_c { mbox_op_rand.cmd.cmd_s.fw        == 1'b0;
                          mbox_op_rand.cmd.cmd_s.resp_reqd == 1'b0;
                          mbox_op_rand.cmd.cmd_s.uc_to_soc == 1'b1; }

  // Constrain size to less than 128KiB for now (mailbox size), but we will
  // recalculate this based on the command being sent
  constraint mbox_dlen_max_c { mbox_op_rand.dlen <= 32'h0002_0000; }

  // After acquiring the lock, it is informative to read from the mbox_status
  // and mbox_user registers to confirm that lock acquisition had the intended
  // side-effects. But doing register reads on AHB actually affects the
  // system - so we get more interesting coverage by skipping it sometimes
  constraint ahb_reg_check_c {do_ahb_lock_check dist {0:/1, 1:/1};}
  constraint retry_failed_reg_c {retry_failed_reg_axs == 1'b1;}

  //==========================================
  // Function:    new
  // Description: Constructor
  //==========================================
  function new(string name = "" );
    super.new(name);
    // Create an array of all defined mbox cmd values.
    // This can be used in constraints as appropriate
    defined_cmds = new[mbox_op_rand.cmd.cmd_e.num()];
    foreach (defined_cmds[idx]) begin
        if (idx == 0)
            defined_cmds[idx] = mbox_op_rand.cmd.cmd_e.first();
        else
            defined_cmds[idx] = defined_cmds[idx-1].next();
    end

  endfunction

  //==========================================
  // Function:    do_kill
  // Description: Called as part of sequencer.stop_sequences
  //              when invoked on the sequencer that is running
  //              this sequence.
  //==========================================
  virtual function void do_kill();
    // FIXME gracefully terminate any AHB requests pending?
    reg_model.soc_ifc_AHB_map.get_sequencer().stop_sequences(); // Kill any pending APB transfers
  endfunction

  //==========================================
  // Task:        pre_body
  // Description: Setup tasks to:
  //               - get a reg model handle
  //               - check for a valid responder handle
  //               - check valid dlen value
  //==========================================
  virtual task pre_body();
    super.pre_body();
    reg_model = configuration.soc_ifc_rm;

    if (cptra_status_agent_rsp_seq == null)
        `uvm_fatal("CPTRA_MBOX_SEQ", "Mailbox Sequence (uC->SOC) expected a handle to the cptra status agent responder sequence (from bench-level sequence) but got null!")

    // Randomization checker requires a valid handle to reg-model, which it gets
    // from the configuration object (which is not set until pre_body())
    assert(mbox_op_rand.dlen <= (reg_model.mbox_mem_rm.get_size() * reg_model.mbox_mem_rm.get_n_bytes())) else
        `uvm_error("CPTRA_MBOX_SEQ", $sformatf("Randomized SOC_IFC environment mailbox base sequence with bad dlen. Max: [0x%x] Got: [0x%x]. Cmd randomized to %p", (reg_model.mbox_mem_rm.get_size() * reg_model.mbox_mem_rm.get_n_bytes()), mbox_op_rand.dlen, mbox_op_rand.cmd.cmd_e))
  endtask

  //==========================================
  // Task:        body
  // Description: Implement main functionality for
  //              SOC-side transmission of mailbox request.
  //==========================================
  virtual task body();

    op_sts_e op_sts;

    sts_rsp_count = 0;

    fork
        forever begin
            @(cptra_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    `uvm_info("CPTRA_MBOX_SEQ", $sformatf("Initiating command sequence to mailbox with cmd: [%p] dlen: [%p]", mbox_op_rand.cmd.cmd_e, mbox_op_rand.dlen), UVM_MEDIUM)

    mbox_setup();
    mbox_acquire_lock(op_sts);
    mbox_set_cmd(mbox_op_rand);
    mbox_push_datain();
    mbox_execute();
    mbox_poll_status();
    mbox_clr_execute();
    mbox_teardown();

  endtask

endclass

// TODO these functions are all intended to be overridden by inheriting sequence
//      although some are simple and may not need any modification

//==========================================
// Task:        mbox_setup
// Description: Setup tasks to:
//               - Any functionality implemented in derived classes
//==========================================
task soc_ifc_env_cptra_mbox_req_sequence_base::mbox_setup();
    uvm_reg_data_t data;
    uvm_reg_field  flds[$];

    // Clear any interrupts already asserted at sequence start
    // Notifications
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "notif_internal_intr_r");
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "notif_internal_intr_r");
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.get_fields(flds);
    foreach (flds[ii]) begin
        if (data[flds[ii].get_lsb_pos()])
            `uvm_info("CPTRA_MBOX_SEQ", {"At sequence start, observed notification_interrupt for bit: ", flds[ii].get_name()}, UVM_HIGH)
    end

    // Errors
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "error_internal_intr_r");
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "error_internal_intr_r");
    flds.delete();
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.get_fields(flds);
    foreach (flds[ii]) begin
        if (data[flds[ii].get_lsb_pos()])
            `uvm_info("CPTRA_MBOX_SEQ", {"At sequence start, observed error_interrupt for bit: ", flds[ii].get_name()}, UVM_HIGH)
    end
endtask

//==========================================
// Task:        mbox_acquire_lock
// Description: Poll mbox_lock to gain control over mailbox
//==========================================
task soc_ifc_env_cptra_mbox_req_sequence_base::mbox_acquire_lock(output op_sts_e op_sts);
    uvm_reg_data_t data;
    bit uc_has_lock;

    op_sts = CPTRA_TIMEOUT;
    reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_lock");
    // Wait for read data to return with '0', indicating no other agent has lock
    while (data[reg_model.mbox_csr_rm.mbox_lock.lock.get_lsb_pos()]) begin
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(200); // FIXME add more randomization on delay
        reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        report_reg_sts(reg_sts, "mbox_lock");
    end

    if (do_ahb_lock_check || reg_sts != UVM_IS_OK) begin
        // Check if we actually got the lock and if we expected to or not
        reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        report_reg_sts(reg_sts, "mbox_status");
        uc_has_lock = ~data[reg_model.mbox_csr_rm.mbox_status.soc_has_lock.get_lsb_pos()] && reg_sts == UVM_IS_OK;
        if (!uc_has_lock) begin
            `uvm_error("CPTRA_MBOX_SEQ", "Mailbox Status unexpectedly indicates uC does not have lock!")
            op_sts = CPTRA_INVALID;
        end

        // Check latest value of mbox_user
        reg_model.mbox_csr_rm.mbox_user.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        report_reg_sts(reg_sts, "mbox_user");
        if (uc_has_lock && (data != 32'hFFFF_FFFF/*FIXME*/)) begin
            `uvm_error("CPTRA_MBOX_SEQ", "mbox_user does not match default user value for AHB after acquiring lock!")
            op_sts = CPTRA_INVALID;
        end
        else begin
            `uvm_info("CPTRA_MBOX_SEQ", $sformatf("mbox_user matches expected value [0x%x] based on result of attempt to acquire lock", 32'hFFFF_FFFF/*FIXME*/), UVM_HIGH)
        end

        // If we don't already have the lock, acquire it
        // TODO this logic copied from soc-mailbox flow. Is it applicable without
        //      PAUSER field to evaluate?
        if (!uc_has_lock && retry_failed_reg_axs) begin
            reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
            report_reg_sts(reg_sts, "mbox_lock");
            // Wait for read data to return with '0', indicating no other agent has lock
            while (data[reg_model.mbox_csr_rm.mbox_lock.lock.get_lsb_pos()]) begin
                configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(200);
                reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
                report_reg_sts(reg_sts, "mbox_lock");
            end
            this.mbox_user_locked.mbox_user = reg_model.mbox_csr_rm.mbox_user.get_mirrored_value();

            // Check if we actually got the lock
            reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
            report_reg_sts(reg_sts, "mbox_status");
            uc_has_lock = ~data[reg_model.mbox_csr_rm.mbox_status.soc_has_lock.get_lsb_pos()] && reg_sts == UVM_IS_OK;
            if (!uc_has_lock)
                `uvm_error("CPTRA_MBOX_SEQ", "Failed to acquire lock when expected to succeed!")
            else
                this.mbox_user_locked.locked = 1'b1;

            // Check latest value of mbox_user
            reg_model.mbox_csr_rm.mbox_user.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
            report_reg_sts(reg_sts, "mbox_user");
            if (uc_has_lock && (data != this.mbox_user_locked.mbox_user)) begin
                `uvm_error("CPTRA_MBOX_SEQ", "mbox_user does not match value predicted when lock was acquired!")
            end
            else if (!uc_has_lock && (data == this.mbox_user_locked.mbox_user)) begin
                `uvm_error("CPTRA_MBOX_SEQ", "mbox_user unexpectedly updated when attempt to acquire lock failed!")
            end
            else begin
                `uvm_info("CPTRA_MBOX_SEQ", $sformatf("mbox_user matches expected value [0x%x] based on result of attempt to acquire lock", this.mbox_user_locked.mbox_user), UVM_HIGH)
            end

        end
        else if (uc_has_lock) begin
            this.mbox_user_locked.mbox_user = reg_model.mbox_csr_rm.mbox_user.get_mirrored_value();
            this.mbox_user_locked.locked = 1'b1;
        end
    end
    else begin
        this.mbox_user_locked.mbox_user = reg_model.mbox_csr_rm.mbox_user.get_mirrored_value();
        this.mbox_user_locked.locked = 1'b1;
    end
    op_sts = CPTRA_SUCCESS;
endtask

//==========================================
// Task:        mbox_set_cmd
// Description: Submit randomized command and dlen to
//              mbox_cmd and mbox_dlen registers
//==========================================
task soc_ifc_env_cptra_mbox_req_sequence_base::mbox_set_cmd(input mbox_op_s op);
    uvm_reg_data_t data;

    reg_model.mbox_csr_rm.mbox_cmd.write(reg_sts, uvm_reg_data_t'(op.cmd), UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_cmd");

    reg_model.mbox_csr_rm.mbox_dlen.write(reg_sts, uvm_reg_data_t'(op.dlen), UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_dlen");
endtask

//==========================================
// Task:        mbox_set_cmd
// Description: Write data in a loop to mbox_datain register
// NOTE:        This should be overridden with real data to write
//==========================================
task soc_ifc_env_cptra_mbox_req_sequence_base::mbox_push_datain();
    int ii;
    uvm_reg_data_t data;
    for (ii=0; ii < this.mbox_op_rand.dlen; ii+=4) begin
        if (ii == 0) begin
            data = uvm_reg_data_t'(mbox_op_rand.dlen - 4);
        end
        else begin
            if (!std::randomize(data)) `uvm_error("CPTRA_MBOX_SEQ", "Failed to randomize data")
        end
        `uvm_info("CPTRA_MBOX_SEQ", $sformatf("[Iteration: %0d] Sending datain: 0x%x", ii/4, data), UVM_DEBUG)
        reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        report_reg_sts(reg_sts, "mbox_datain");
    end
endtask

//==========================================
// Task:        mbox_execute
// Description: Submit command to SoC by writing
//              1 to mbox_execute register
//==========================================
task soc_ifc_env_cptra_mbox_req_sequence_base::mbox_execute();
    uvm_reg_data_t data = uvm_reg_data_t'(1) << reg_model.mbox_csr_rm.mbox_execute.execute.get_lsb_pos();
    reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_execute");
endtask

//==========================================
// Task:        mbox_check_status
// Description: Read mbox_status
//==========================================
task soc_ifc_env_cptra_mbox_req_sequence_base::mbox_check_status(output mbox_status_e data, output mbox_fsm_state_e state);
    uvm_reg_data_t reg_data;
    reg_model.mbox_csr_rm.mbox_status.read(reg_sts, reg_data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_status");

    if (reg_sts != UVM_IS_OK) begin
        data = CMD_FAILURE;
    end
    else begin
        data = mbox_status_e'(reg_data >> reg_model.mbox_csr_rm.mbox_status.status.get_lsb_pos());
        state = mbox_fsm_state_e'(reg_data >> reg_model.mbox_csr_rm.mbox_status.mbox_fsm_ps.get_lsb_pos());
    end
endtask

//==========================================
// Task:        mbox_poll_status
// Description: Issue calls to mbox_check_status
//              until status change indicates control is
//              returned to uC.
//==========================================
task soc_ifc_env_cptra_mbox_req_sequence_base::mbox_poll_status();
    mbox_status_e data;
    mbox_fsm_state_e state;
    uvm_reg_data_t mask;

    // Poll mbox_status register
    do begin
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(200);
        mbox_check_status(data, state);
    end while (data == CMD_BUSY && !(state inside {MBOX_IDLE, MBOX_ERROR}));

    // We should have an error interrupt in response to the ERROR state, which
    // will be serviced at a later step.
    // We do not expect the cmd_avail_sts interrupt, and there is no point in
    // continuing this task (to report on the mbox_status field) when we've hit
    // a protocol error.
    if (state == MBOX_ERROR) begin
        mbox_sts_is_error = 1;
        return;
    end

    // Clear Interrupt Status, which is set on transfer SOC->uC
    mask = uvm_reg_data_t'(1) << reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_cmd_avail_sts.get_lsb_pos();
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.write(reg_sts, mask, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK) begin
        `uvm_error("CPTRA_MBOX_SEQ", "Write to clear notification interrupt notif_cmd_avail_sts failed!")
    end

    // Evaluate status field
    if (data == DATA_READY) begin
        `uvm_info("CPTRA_MBOX_SEQ", $sformatf("Received status %p when not expecting any bytes of response data!", data), UVM_LOW)
    end
    else if (data == CMD_FAILURE) begin
        `uvm_info("CPTRA_MBOX_SEQ", $sformatf("Received unexpected mailbox status %p", data), UVM_LOW)
    end
    else if (data == CMD_COMPLETE) begin
        `uvm_info("CPTRA_MBOX_SEQ", $sformatf("Received status %p from SOC in response to command", data), UVM_FULL)
    end
    else begin
        `uvm_info("CPTRA_MBOX_SEQ", $sformatf("Received unexpected mailbox status %p", data), UVM_LOW)
    end
endtask

//==========================================
// Task:        mbox_clr_execute
// Description: End the mailbox flow by writing
//              0 to mbox_execute register (or
//              by force-unlock if necessary)
//==========================================
task soc_ifc_env_cptra_mbox_req_sequence_base::mbox_clr_execute();
    uvm_reg_data_t data;
    // We have to stall a couple clocks to allow interrupts to assert in case
    // we read the MBOX_ERROR status, since there is a small delay as the signal
    // propagates through registers.
    configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(2);
    // Now, check for the expected error interrupt
    if (sts_rsp_count > 0 && cptra_status_agent_rsp_seq.rsp.soc_ifc_err_intr_pending) begin
        reg_model.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        report_reg_sts(reg_sts, "error_internal_intr_r");
        reg_model.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        report_reg_sts(reg_sts, "error_internal_intr_r");
        if (data[reg_model.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.error_cmd_fail_sts.get_lsb_pos()]) begin
            // Force unlock to recover from error and reset mailbox to IDLE state
            reg_model.mbox_csr_rm.mbox_unlock.write(reg_sts, uvm_reg_data_t'(1 << reg_model.mbox_csr_rm.mbox_unlock.unlock.get_lsb_pos()), UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
            report_reg_sts(reg_sts, "mbox_unlock");
            return; /* force unlock trumps the write to mbox_execute, so we're done at this point */
        end
        else if (mbox_sts_is_error) begin
            `uvm_error("CPTRA_MBOX_SEQ", "Error interrupt following cmd failure does not have cmd_fail bit set!")
        end
    end
    else if (mbox_sts_is_error) begin
        `uvm_error("CPTRA_MBOX_SEQ", "Error encountered but no interrupt received")
    end
    reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, uvm_reg_data_t'(0), UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_execute");
endtask

//==========================================
// Task:        mbox_teardown
// Description: Placeholder task to allow derived classes
//              to add any end-of-sequence functionality.
//==========================================
task soc_ifc_env_cptra_mbox_req_sequence_base::mbox_teardown();
    uvm_reg_data_t data, mask;

    // Clear any pending notification interrupts that made it through to the end of the sequence
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "notif_internal_intr_r");
    // Any unexpected interrupts should trigger a tb error
    mask = ~((1 << reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_mbox_ecc_cor_sts.get_lsb_pos()) |
             (1 << reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_debug_locked_sts.get_lsb_pos()) |
             (1 << reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_soc_req_lock_sts.get_lsb_pos()));
    if (data & mask) begin
        `uvm_error("CPTRA_MBOX_SEQ", $sformatf("Received notification interrupt for unexpected event: 0x%0x", data))
    end
    else begin
        reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        report_reg_sts(reg_sts, "notif_internal_intr_r");
        `uvm_info("CPTRA_MBOX_SEQ", $sformatf("Received and cleared notification interrupt for events: 0x%0x", data), UVM_HIGH)
    end

    // Summary at sequence end
    `uvm_info("CPTRA_MBOX_SEQ", $sformatf("uC initiated mailbox flow is completed. Ending status: %s", mbox_sts_is_error ? "hit protocol violation" : "no protocol violation"), UVM_LOW)
endtask

//==========================================
// Function:    report_reg_sts
// Description: Generate informative messages about the result
//              of the most recent AHB transfer.
//==========================================
function void soc_ifc_env_cptra_mbox_req_sequence_base::report_reg_sts(uvm_status_e reg_sts, string name);
    // AHB error is never expected.
    if (reg_sts != UVM_IS_OK)
        `uvm_error("CPTRA_MBOX_SEQ",
                   $sformatf("Register access failed unexpectedly! (%s)", name))
    else
        `uvm_info("CPTRA_MBOX_SEQ",
                  $sformatf("Register access to (%s) with reg_sts: %p", name, reg_sts),
                  UVM_HIGH)
endfunction
