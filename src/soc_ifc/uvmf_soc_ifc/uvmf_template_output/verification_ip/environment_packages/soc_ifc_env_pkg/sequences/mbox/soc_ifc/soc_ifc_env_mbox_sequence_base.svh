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
//              Extended to provide additional functionality.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_sequence_base extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


  `uvm_object_utils( soc_ifc_env_mbox_sequence_base )





  rand mbox_op_s mbox_op_rand;
  rand int mbox_resp_expected_dlen; // Number of response data bytes to expect
  int sts_rsp_count;
  uvm_status_e reg_sts;
  rand bit do_apb_lock_check;
  rand bit retry_failed_reg_axs;

  typedef enum byte {
    DLY_ZERO,
    DLY_SMALL,
    DLY_MEDIUM,
    DLY_LARGE
  } delay_scale_e;

  rand delay_scale_e poll_delay, step_delay, data_delay;
  rand bit rand_delay_en = 0;
  rand int unsigned rand_delay = 0;

  // Certain random sequences force the command to be outside of the defined
  // options from mbox_cmd_e, such that truly random behavior does not violate
  // expected activity for the command opcode. To do this, we need to be able
  // to build a constraint to exclude the enum values, which requires this
  // array of all possible enumerated values.
  mbox_cmd_e defined_cmds[];

  // PAUSER tracking/override
  bit [apb5_master_0_params::PAUSER_WIDTH-1:0] mbox_valid_users [6];
  bit mbox_valid_users_initialized = 1'b0;
  bit [apb5_master_0_params::PAUSER_WIDTH-1:0] mbox_user_override_val;
  bit override_mbox_user = 1'b0;
  caliptra_apb_user apb_user_obj; // Handle to the most recently generated user object
  struct packed {
      bit [apb5_master_0_params::PAUSER_WIDTH-1:0] pauser; /* Value of PAUSER when mbox lock acquired */
      bit                                          locked;
  } pauser_locked = '{pauser: '1, locked: 1'b0};
  int hit_invalid_pauser_count = '0;

  localparam FORCE_VALID_PAUSER = 0;
  int unsigned PAUSER_PROB_LOCK   ;
  int unsigned PAUSER_PROB_CMD    ;
  int unsigned PAUSER_PROB_DATAIN ;
  int unsigned PAUSER_PROB_EXECUTE;
  int unsigned PAUSER_PROB_STATUS ;
  int unsigned PAUSER_PROB_DATAOUT;

  extern virtual task mbox_setup();
  extern virtual task mbox_acquire_lock(output op_sts_e op_sts);
  extern virtual task mbox_set_cmd(input mbox_op_s op);
  extern virtual task mbox_push_datain();
  extern virtual task mbox_execute();
  extern virtual task mbox_check_status(output mbox_status_e data, output mbox_fsm_state_e state);
  extern virtual task mbox_read_resp_data();
  extern virtual task mbox_poll_status();
  extern virtual task mbox_clr_execute();
  extern virtual task mbox_teardown();

  extern virtual task                       do_rand_delay(input bit do_delay_randomize=1, input delay_scale_e scale=DLY_SMALL);
  extern virtual function void              set_pauser_prob_vals();
  extern virtual function bit               pauser_used_is_valid();
  extern virtual function caliptra_apb_user get_rand_user(int unsigned invalid_prob = FORCE_VALID_PAUSER);
  extern virtual function void              report_reg_sts(uvm_status_e reg_sts, string name);

  // Constrain command to not be firmware or uC-initiated
  constraint mbox_cmd_c { mbox_op_rand.cmd.cmd_s.fw        == 1'b0;
                          mbox_op_rand.cmd.cmd_s.uc_to_soc == 1'b0; }

  // Constrain size to less than 128KiB for now (mailbox size), but we will
  // recalculate this based on the command being sent
  constraint mbox_dlen_max_c { mbox_op_rand.dlen <= MBOX_SIZE_BYTES; }
  // Minimum 2 dwords to include dlen/mbox_resp_expected_dlen at the beginning
  // IFF the response data is required
  constraint mbox_dlen_min_c { mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_op_rand.dlen >= 32'h8; }
  // Response data is only non-zero if a response is requested, and also must
  // be small enough to fit in the mailbox
  constraint mbox_resp_dlen_c {                                      mbox_resp_expected_dlen <= MBOX_SIZE_BYTES;
                                !mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_resp_expected_dlen == 0;
                                 mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_resp_expected_dlen >  0; }

  // After acquiring the lock, it is informative to read from the mbox_status
  // and mbox_user registers to confirm that lock acquisition had the intended
  // side-effects. But doing register reads on APB actually affects the
  // system - so we get more interesting coverage by skipping it sometimes
  constraint apb_reg_check_c {do_apb_lock_check dist {0:/1, 1:/1};}
  constraint retry_failed_reg_c {retry_failed_reg_axs == 1'b1;}

  // Constraint on the random delays injected between each step of the flow.
  // By default, delays minimal to avoid protracting the test too much.
  // Targeted sequences may override this constraint.
  constraint delay_scale_c { poll_delay == DLY_MEDIUM;
                             step_delay == DLY_SMALL;
                             data_delay == DLY_ZERO; }
  // These constraints conflict with each other - only the one that is applicable
  // should be enabled; this is done in the definition of do_rand_delay
  constraint zero_delay_c  { rand_delay == 0;}
  constraint small_delay_c { rand_delay dist {   0  :/ 1000,
                                              [1:3] :/ 100,
                                              [4:7] :/ 25,
                                              [8:31]:/ 1};}
  constraint medium_delay_c { rand_delay dist {   0    :/ 10,
                                               [1:7]   :/ 25,
                                               [8:31]  :/ 100,
                                               [32:255]:/ 1000};}
  constraint large_delay_c { rand_delay dist {        15  :/ 1,
                                              [ 16 : 255] :/ 25,
                                              [ 256:1023] :/ 500,
                                              [1024:8191] :/ 300};}

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

    // Assign probabilties of generating invalid PAUSER at different stages
    set_pauser_prob_vals();

    // Default constraint mode is SMALL random delays, updated when doing
    // the delay
    this.zero_delay_c  .constraint_mode(0);
    this.small_delay_c .constraint_mode(1);
    this.medium_delay_c.constraint_mode(0);
    this.large_delay_c .constraint_mode(0);
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
  // Task:        pre_body
  // Description: Setup tasks to:
  //               - get a reg model handle
  //               - check for a valid responder handle
  //               - check valid dlen value
  //==========================================
  virtual task pre_body();
    super.pre_body();
    reg_model = configuration.soc_ifc_rm;

    if (soc_ifc_status_agent_rsp_seq == null)
        `uvm_fatal("MBOX_SEQ", "Mailbox Sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")

    // Randomization checker requires a valid handle to reg-model, which it gets
    // from the configuration object (which is not set until pre_body())
    // This is only an 'info' instead of an error because some tests do this
    // deliberately
    if (mbox_op_rand.dlen > (reg_model.mbox_mem_rm.get_size() * reg_model.mbox_mem_rm.get_n_bytes()))
        `uvm_info("MBOX_SEQ", $sformatf("Randomized SOC_IFC environment mailbox base sequence with invalid dlen. Max: [0x%x] Got: [0x%x]. Cmd randomized to %p", (reg_model.mbox_mem_rm.get_size() * reg_model.mbox_mem_rm.get_n_bytes()), mbox_op_rand.dlen, mbox_op_rand.cmd.cmd_e), UVM_LOW)
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
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    `uvm_info("MBOX_SEQ", $sformatf("Initiating command sequence to mailbox with cmd: [%p] dlen: [%p] resp_dlen: [%p]", mbox_op_rand.cmd.cmd_e, mbox_op_rand.dlen, mbox_resp_expected_dlen), UVM_MEDIUM)

    mbox_setup();               if (rand_delay_en) do_rand_delay(1, step_delay);
    mbox_acquire_lock(op_sts);  if (rand_delay_en) do_rand_delay(1, step_delay);
    mbox_set_cmd(mbox_op_rand); if (rand_delay_en) do_rand_delay(1, step_delay);
    mbox_push_datain();         if (rand_delay_en) do_rand_delay(1, step_delay);
    mbox_execute();             if (rand_delay_en) do_rand_delay(1, step_delay);
    mbox_poll_status();         if (rand_delay_en) do_rand_delay(1, step_delay);
    mbox_clr_execute();         if (rand_delay_en) do_rand_delay(1, step_delay);
    mbox_teardown();

  endtask

endclass

// TODO these functions are all intended to be overridden by inheriting sequence
//      although some are simple and may not need any modification
//==========================================
// Task:        mbox_setup
// Description: Setup tasks to:
//               - Grab configured mbox_valid_users from reg model
//               - Any other functionality implemented in derived classes
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_setup();
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
        // FIXME hardcoded default value of 32'hFFFF_FFFF
        mbox_valid_users[5] = '1;
        mbox_valid_users_initialized = 1'b1;
    end
    else begin
        for (ii=0; ii < $size(reg_model.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK); ii++) begin: VALID_USER_CHECK_LOOP
            if (reg_model.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[ii].LOCK.get_mirrored_value() &&
                mbox_valid_users[ii] != reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[ii].get_mirrored_value())
                `uvm_warning("MBOX_SEQ", "mbox_valid_users initialized with a value that does not match mirrored value in register model!")
        end
        if (~&mbox_valid_users[5]) begin
            `uvm_warning("MBOX_SEQ", $sformatf("mbox_valid_users initialized with a value that does not match the default valid user of 0x%x", 32'hFFFF_FFFF))
        end
    end
    if (override_mbox_user && !(mbox_user_override_val inside mbox_valid_users)) begin
        `uvm_info("MBOX_SEQ", $sformatf("mbox_user overridden to 0x%x which is not in mbox_valid_users [%p]!", mbox_user_override_val, mbox_valid_users), UVM_LOW)
    end
endtask

//==========================================
// Task:        mbox_acquire_lock
// Description: Poll mbox_lock to gain control over mailbox
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_acquire_lock(output op_sts_e op_sts);
    uvm_reg_data_t data;
    bit soc_has_lock;

    op_sts = CPTRA_TIMEOUT;
    reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_LOCK)));
    report_reg_sts(reg_sts, "mbox_lock");
    // Wait for read data to return with '0', indicating no other agent has lock
    while (data[reg_model.mbox_csr_rm.mbox_lock.lock.get_lsb_pos()]) begin
        do_rand_delay(1, poll_delay);
        reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_LOCK)));
        report_reg_sts(reg_sts, "mbox_lock");
    end

    if (do_apb_lock_check || reg_sts != UVM_IS_OK) begin
        // Check if we actually got the lock and if we expected to or not
        reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(this.apb_user_obj));
        report_reg_sts(reg_sts, "mbox_status");
        soc_has_lock = data[reg_model.mbox_csr_rm.mbox_status.soc_has_lock.get_lsb_pos()] && reg_sts == UVM_IS_OK;
        if (!soc_has_lock && pauser_used_is_valid()) begin
            `uvm_error("MBOX_SEQ", "Failed to acquire lock when using valid PAUSER!")
            op_sts = CPTRA_INVALID;
        end
        else if (soc_has_lock && !pauser_used_is_valid()) begin
            `uvm_error("MBOX_SEQ", "Acquired lock unexpectedly when using invalid PAUSER!")
        end

        // Check latest value of mbox_user
        reg_model.mbox_csr_rm.mbox_user.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(this.apb_user_obj));
        report_reg_sts(reg_sts, "mbox_user");
        if (soc_has_lock && (data != this.apb_user_obj.get_addr_user())) begin
            `uvm_error("MBOX_SEQ", "mbox_user does not match PAUSER used when lock was acquired!")
            op_sts = CPTRA_INVALID;
        end
        else if (!soc_has_lock && (data == this.apb_user_obj.get_addr_user())) begin
            `uvm_error("MBOX_SEQ", "mbox_user unexpectedly updated when lock was not acquired!")
            op_sts = CPTRA_INVALID;
        end
        else begin
            `uvm_info("MBOX_SEQ", $sformatf("mbox_user matches expected value [0x%x] based on result of attempt to acquire lock", this.apb_user_obj.get_addr_user()), UVM_HIGH)
        end

        // If we don't already have the lock, acquire it using a valid PAUSER
        if (!soc_has_lock && retry_failed_reg_axs) begin
            reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
            report_reg_sts(reg_sts, "mbox_lock");
            // Wait for read data to return with '0', indicating no other agent has lock
            while (data[reg_model.mbox_csr_rm.mbox_lock.lock.get_lsb_pos()]) begin
                do_rand_delay(1, poll_delay);
                reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(this.apb_user_obj));
                report_reg_sts(reg_sts, "mbox_lock");
            end
            this.pauser_locked.pauser = this.apb_user_obj.get_addr_user();

            // Check if we actually got the lock
            reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(this.apb_user_obj));
            report_reg_sts(reg_sts, "mbox_status");
            soc_has_lock = data[reg_model.mbox_csr_rm.mbox_status.soc_has_lock.get_lsb_pos()] && reg_sts == UVM_IS_OK;
            if (!pauser_used_is_valid())
                `uvm_error("MBOX_SEQ", "PAUSER value used is not valid even after attempt to force it to a valid value!")
            else if (!soc_has_lock)
                `uvm_error("MBOX_SEQ", "Failed to acquire lock when using valid PAUSER!")
            else
                this.pauser_locked.locked = 1'b1;

            // Check latest value of mbox_user
            reg_model.mbox_csr_rm.mbox_user.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(this.apb_user_obj));
            report_reg_sts(reg_sts, "mbox_user");
            if (soc_has_lock && (data != this.apb_user_obj.get_addr_user())) begin
                `uvm_error("MBOX_SEQ", "mbox_user does not match PAUSER used when lock was acquired!")
            end
            else if (!soc_has_lock && (data == this.apb_user_obj.get_addr_user())) begin
                `uvm_error("MBOX_SEQ", "mbox_user unexpectedly updated when using invalid PAUSER!")
            end
            else begin
                `uvm_info("MBOX_SEQ", $sformatf("mbox_user matches expected value [0x%x] based on result of attempt to acquire lock", this.apb_user_obj.get_addr_user()), UVM_HIGH)
            end

        end
        else if (soc_has_lock) begin
            this.pauser_locked.pauser = this.apb_user_obj.get_addr_user();
            this.pauser_locked.locked = 1'b1;
        end
    end
    else begin
        this.pauser_locked.pauser = this.apb_user_obj.get_addr_user();
        this.pauser_locked.locked = 1'b1;
    end
    op_sts = CPTRA_SUCCESS;
endtask

//==========================================
// Task:        mbox_set_cmd
// Description: Submit randomized command and dlen to
//              mbox_cmd and mbox_dlen registers
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_set_cmd(input mbox_op_s op);
    uvm_reg_data_t data, prev_data;

    prev_data = reg_model.mbox_csr_rm.mbox_cmd.get_mirrored_value();
    reg_model.mbox_csr_rm.mbox_cmd.write(reg_sts, uvm_reg_data_t'(op.cmd), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_CMD)));
    report_reg_sts(reg_sts, "mbox_cmd");
    if (!pauser_used_is_valid()) begin
        if (rand_delay_en) do_rand_delay(1, step_delay);
        reg_model.mbox_csr_rm.mbox_cmd.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
        report_reg_sts(reg_sts, "mbox_cmd");
        if (data != prev_data)
            `uvm_error("MBOX_SEQ", "Write to mbox_cmd succeeded unexpectedly with invalid PAUSER!")
        else if (retry_failed_reg_axs) begin
            reg_model.mbox_csr_rm.mbox_cmd.write(reg_sts, uvm_reg_data_t'(op.cmd), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
            report_reg_sts(reg_sts, "mbox_cmd");
        end
    end

    if (rand_delay_en) do_rand_delay(1, step_delay);

    prev_data = reg_model.mbox_csr_rm.mbox_dlen.get_mirrored_value();
    reg_model.mbox_csr_rm.mbox_dlen.write(reg_sts, uvm_reg_data_t'(op.dlen), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_CMD)));
    report_reg_sts(reg_sts, "mbox_dlen");
    if (!pauser_used_is_valid()) begin
        if (rand_delay_en) do_rand_delay(1, step_delay);
        reg_model.mbox_csr_rm.mbox_dlen.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
        report_reg_sts(reg_sts, "mbox_dlen");
        if (32'(data) != prev_data)
            `uvm_error("MBOX_SEQ", "Write to mbox_dlen succeeded unexpectedly with invalid PAUSER!")
        else if (retry_failed_reg_axs)  begin
            reg_model.mbox_csr_rm.mbox_dlen.write(reg_sts, uvm_reg_data_t'(op.dlen), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
            report_reg_sts(reg_sts, "mbox_dlen");
        end
    end
endtask

//==========================================
// Task:        mbox_push_datain
// Description: Write data in a loop to mbox_datain register
// NOTE:        This should be overridden with real data to write
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_push_datain();
    int ii;
    uvm_reg_data_t data;
    for (ii=0; ii < this.mbox_op_rand.dlen; ii+=4) begin
        if (ii == 0) begin
            data = uvm_reg_data_t'(mbox_op_rand.dlen - 8);
        end
        else if (ii == 4) begin
            data = uvm_reg_data_t'(mbox_resp_expected_dlen);
        end
        else begin
            if (!std::randomize(data)) `uvm_error("MBOX_SEQ", "Failed to randomize data")
        end
        `uvm_info("MBOX_SEQ", $sformatf("[Iteration: %0d] Sending datain: 0x%x", ii/4, data), UVM_DEBUG)
        reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_DATAIN)));
        report_reg_sts(reg_sts, "mbox_datain");
        if (!pauser_used_is_valid() && retry_failed_reg_axs) begin
            if (rand_delay_en) do_rand_delay(1, data_delay);
            `uvm_info("MBOX_SEQ", "Re-do datain write with valid PAUSER", UVM_HIGH)
            reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
            report_reg_sts(reg_sts, "mbox_datain");
        end
        if (rand_delay_en) do_rand_delay(1, data_delay);
    end
endtask

//==========================================
// Task:        mbox_execute
// Description: Submit command to Caliptra by writing
//              1 to mbox_execute register
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_execute();
    uvm_reg_data_t data = uvm_reg_data_t'(1) << reg_model.mbox_csr_rm.mbox_execute.execute.get_lsb_pos();
    reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_EXECUTE)));
    report_reg_sts(reg_sts, "mbox_execute");
    if (!pauser_used_is_valid() && retry_failed_reg_axs) begin
        if (rand_delay_en) do_rand_delay(1, step_delay);
        reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
        report_reg_sts(reg_sts, "mbox_execute");
    end
endtask

//==========================================
// Task:        mbox_check_status
// Description: Read mbox_status
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_check_status(output mbox_status_e data, output mbox_fsm_state_e state);
    uvm_reg_data_t reg_data;
    reg_model.mbox_csr_rm.mbox_status.read(reg_sts, reg_data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_STATUS)));
    report_reg_sts(reg_sts, "mbox_status");

    if (!pauser_used_is_valid() && retry_failed_reg_axs) begin
        reg_model.mbox_csr_rm.mbox_status.read(reg_sts, reg_data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
        report_reg_sts(reg_sts, "mbox_status");
    end

    if (reg_sts != UVM_IS_OK) begin
        data = CMD_FAILURE;
    end
    else begin
        data = mbox_status_e'(reg_data >> reg_model.mbox_csr_rm.mbox_status.status.get_lsb_pos());
        state = mbox_fsm_state_e'(reg_data >> reg_model.mbox_csr_rm.mbox_status.mbox_fsm_ps.get_lsb_pos());
    end
endtask

//==========================================
// Task:        mbox_read_resp_data
// Description: Fetch all response data from uC in a loop
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_read_resp_data();
    uvm_reg_data_t data;
    uvm_reg_data_t dlen;
    int ii;
    reg_model.mbox_csr_rm.mbox_dlen.read(reg_sts, dlen, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_DATAOUT)));
    report_reg_sts(reg_sts, "mbox_dlen");
    if (!pauser_used_is_valid() && retry_failed_reg_axs) begin
        reg_model.mbox_csr_rm.mbox_dlen.read(reg_sts, dlen, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
        report_reg_sts(reg_sts, "mbox_dlen");
    end
    if (dlen != mbox_resp_expected_dlen) begin
        `uvm_error("MBOX_SEQ", $sformatf("SOC received response data with mbox_dlen [%0d] that does not match the expected data amount [%0d]!", dlen, mbox_resp_expected_dlen))
    end
    if (rand_delay_en) do_rand_delay(1, step_delay);
    for (ii=0; ii < dlen; ii+=4) begin
        reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_DATAOUT)));
        report_reg_sts(reg_sts, "mbox_dataout");
        if (!pauser_used_is_valid() && retry_failed_reg_axs) begin
            if (rand_delay_en) do_rand_delay(1, data_delay);
            `uvm_info("MBOX_SEQ", "Re-do dataout read with valid PAUSER", UVM_HIGH)
            reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
            report_reg_sts(reg_sts, "mbox_dataout");
        end
        if (rand_delay_en) do_rand_delay(1, data_delay);
    end
endtask

//==========================================
// Task:        mbox_poll_status
// Description: Issue calls to mbox_check_status
//              until status change indicates control is
//              returned to SOC.
//              Upon reclaiming control, read any available
//              response data from mbox_dataout.
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_poll_status();
    mbox_status_e data;
    mbox_fsm_state_e state;

    // A force-unlock would cause state->MBOX_IDLE, so we exit the polling loop
    do begin
        do_rand_delay(1, poll_delay);
        mbox_check_status(data, state);
    end while (data == CMD_BUSY && state != MBOX_IDLE);

    if (state == MBOX_IDLE) begin
        `uvm_info("MBOX_SEQ", "Detected mailbox state transition to IDLE - was mbox_unlock expected?", UVM_HIGH)
    end
    else if (data == DATA_READY) begin
        if (mbox_resp_expected_dlen == 0)
            `uvm_error("MBOX_SEQ", $sformatf("Received status %p when not expecting any bytes of response data!", data))
        else begin
            mbox_read_resp_data();
        end
    end
    else if (data == CMD_FAILURE) begin
        `uvm_error("MBOX_SEQ", $sformatf("Received unexpected mailbox status %p", data))
    end
    else if (data == CMD_COMPLETE) begin
        if (mbox_resp_expected_dlen != 0)
            `uvm_error("MBOX_SEQ", $sformatf("Received status %p when expecting 0x%x bytes of response data!", data, mbox_resp_expected_dlen))
    end
    else begin
        `uvm_error("MBOX_SEQ", $sformatf("Received unexpected mailbox status %p", data))
    end
endtask

//==========================================
// Task:        mbox_clr_execute
// Description: End the mailbox flow by writing
//              0 to mbox_execute register
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_clr_execute();
    uvm_reg_data_t err;

    // Write 0 to mbox_execute to clear mbox_lock and end the test
    reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, uvm_reg_data_t'(0), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_EXECUTE)));
    report_reg_sts(reg_sts, "mbox_execute");
    if (!pauser_used_is_valid() && retry_failed_reg_axs) begin
        if (rand_delay_en) do_rand_delay(1, step_delay);
        reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, uvm_reg_data_t'(0), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
        report_reg_sts(reg_sts, "mbox_execute");
    end

    if (rand_delay_en) do_rand_delay(1, step_delay);

    // Check for any non-fatal mailbox protocol errors that occurred during the test
    reg_model.soc_ifc_reg_rm.CPTRA_HW_ERROR_NON_FATAL.read(reg_sts, err, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(500)));
    // don't use report_reg_sts since this isn't a mbox reg and doesn't have pauser requirements
    if (reg_sts != UVM_IS_OK) begin
        `uvm_error("MBOX_SEQ", "Unexpected error on read from CPTRA_HW_ERROR_NON_FATAL")
    end
    if (|err) begin
        `uvm_info("MBOX_SEQ", "Detected non-fatal errors at end of mailbox flow. Clearing.", UVM_LOW)
        reg_model.soc_ifc_reg_rm.CPTRA_HW_ERROR_NON_FATAL.write(reg_sts, err, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(500)));
        if (reg_sts != UVM_IS_OK) begin
            `uvm_error("MBOX_SEQ", "Unexpected error on write to CPTRA_HW_ERROR_NON_FATAL")
        end
    end
endtask

//==========================================
// Task:        mbox_teardown
// Description: Placeholder task to allow derived classes
//              to add any end-of-sequence functionality.
//              Currently just reports PAUSER violation count.
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_teardown();
    // Summary at sequence end
    `uvm_info("MBOX_SEQ", $sformatf("Count of mailbox accesses performed with invalid PAUSER: %0d", hit_invalid_pauser_count), UVM_MEDIUM)
endtask

//==========================================
// Function:    do_rand_delay
// Description: Use the class variable "rand_delay"
//              to inject random stalls between various stages
//              of the sequence.
//              If do_delay_randomize is set to 1, the value
//              of rand_delay is re-randomized (according to
//              class constraints), otherwise the previous value
//              is used.
//==========================================
task soc_ifc_env_mbox_sequence_base::do_rand_delay(input bit do_delay_randomize=1, input delay_scale_e scale=DLY_SMALL);
    if (do_delay_randomize) begin
        // Update delay constraint based on delay mode
        this.zero_delay_c  .constraint_mode(scale == DLY_ZERO);
        this.small_delay_c .constraint_mode(scale == DLY_SMALL);
        this.medium_delay_c.constraint_mode(scale == DLY_MEDIUM);
        this.large_delay_c .constraint_mode(scale == DLY_LARGE);
        if (!this.randomize(rand_delay))
            `uvm_error("MBOX_SEQ", $sformatf("Failed to randomize rand_delay with scale %p", scale))
        else
            `uvm_info("MBOX_SEQ", $sformatf("Generated rand delay value: [%0d] cycles from constraint scale %p", rand_delay, scale), UVM_DEBUG)
    end
    if (rand_delay != 0)
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(rand_delay);
endtask

//==========================================
// Function:    set_pauser_prob_vals
// Description: Assign values to class variables
//              that control the likelihood of APB transfers
//              using an illegal PAUSER value at all stages
//              of the mailbox flow.
//==========================================
function void soc_ifc_env_mbox_sequence_base::set_pauser_prob_vals();
  this.PAUSER_PROB_LOCK    = FORCE_VALID_PAUSER;
  this.PAUSER_PROB_CMD     = FORCE_VALID_PAUSER;
  this.PAUSER_PROB_DATAIN  = FORCE_VALID_PAUSER;
  this.PAUSER_PROB_EXECUTE = FORCE_VALID_PAUSER;
  this.PAUSER_PROB_STATUS  = FORCE_VALID_PAUSER;
  this.PAUSER_PROB_DATAOUT = FORCE_VALID_PAUSER;
endfunction

//==========================================
// Function:    get_rand_user
// Description: Return a caliptra_apb_user object populated with some value of
//              addr_user (with which to override PAUSER in the reg adapter).
//              The likelihood that the generated addr_user is a invalid value
//              is given by the supplied argument.
//              The supplied argument is normalized against the value 1000 (the probability
//              of getting a valid value). I.e.:
//               - invalid_prob == 0   : returned addr_user is guaranteed to be valid
//               - invalid_prob <  1000: returned addr_user is most likely to be valid
//               - invalid_prob >  1000: returned addr_user is most likely to be invalid
//              A legal addr_user is defined as:
//               - A random selection from valid_users if the mbox_lock has yet to be acquired
//               - The value in mbox_user if mbox_lock has been acquired already
//==========================================
function caliptra_apb_user soc_ifc_env_mbox_sequence_base::get_rand_user(int unsigned invalid_prob = FORCE_VALID_PAUSER);
    apb_user_obj = new();
    if (!this.apb_user_obj.randomize() with {if (pauser_locked.locked)
                                                 (addr_user == pauser_locked.pauser) dist
                                                 {1 :/ 1000,
                                                  0 :/ invalid_prob};
                                             // Override only applies to user value used to acquire lock
                                             else if (override_mbox_user)
                                                 addr_user == mbox_user_override_val;
                                             else
                                                 (addr_user inside {mbox_valid_users}) dist
                                                 {1 :/ 1000,
                                                  0 :/ invalid_prob}; })
        `uvm_error("MBOX_SEQ", "Failed to randomize APB PAUSER override value")
    else
        `uvm_info("MBOX_SEQ", $sformatf("Randomized APB PAUSER override value to 0x%x", this.apb_user_obj.addr_user), UVM_HIGH)
    this.hit_invalid_pauser_count += pauser_used_is_valid() ? 0 : 1;
    return this.apb_user_obj;
endfunction

//==========================================
// Function:    pauser_used_is_valid
// Description: Assess whether the most recent APB
//              transfer used a valid PAUSER or not
//==========================================
function bit soc_ifc_env_mbox_sequence_base::pauser_used_is_valid();
    if (this.pauser_locked.locked)
        return this.apb_user_obj.get_addr_user() == this.pauser_locked.pauser;
    else 
        return this.apb_user_obj.get_addr_user() inside mbox_valid_users;
endfunction

//==========================================
// Function:    report_reg_sts
// Description: Generate informative messages about the result
//              of the most recent APB transfer, accounting for
//              the PAUSER value that was used.
//==========================================
function void soc_ifc_env_mbox_sequence_base::report_reg_sts(uvm_status_e reg_sts, string name);
    // APB error is flagged only for PAUSER that doesn't match the registered
    // values, it does not check that PAUSER matches the exact value in
    // mbox_user that was stored when lock was acquired (this results in a
    // silent error but a successful reg read).
    // Ergo, check against mbox_valid_users instead of pauser_locked.
    if (reg_sts != UVM_IS_OK && this.apb_user_obj.get_addr_user() inside mbox_valid_users)
        `uvm_error("MBOX_SEQ",
                   $sformatf("Register access failed unexpectedly with valid PAUSER! 0x%x (%s)", this.apb_user_obj.get_addr_user(), name))
    else if (reg_sts == UVM_IS_OK && !(this.apb_user_obj.get_addr_user() inside mbox_valid_users))
        `uvm_error("MBOX_SEQ",
                   $sformatf("Register access passed unexpectedly with invalid PAUSER! 0x%x (%s)", this.apb_user_obj.get_addr_user(), name))
    else
        `uvm_info("MBOX_SEQ",
                  $sformatf("Register access to (%s) with pauser_used_is_valid: %b and reg_sts: %p", name, this.pauser_used_is_valid(), reg_sts),
                  UVM_HIGH)
endfunction
