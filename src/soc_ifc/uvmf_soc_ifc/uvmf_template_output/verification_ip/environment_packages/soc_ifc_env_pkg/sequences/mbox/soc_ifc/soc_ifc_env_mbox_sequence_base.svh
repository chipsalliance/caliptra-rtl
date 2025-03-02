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
  uvm_event in_report_reg_sts;
  process teardown_proc;
  rand bit do_axi_lock_check;
  rand bit retry_failed_reg_axs;
  bit mbox_sts_exp_error = 0; // Indicates this sequence will inject an error, which should manifest as a CMD_FAILURE response status
                              // TODO make this more comprehensive/intelligent about randomized error injection
  mbox_sts_exp_error_type_e mbox_sts_exp_error_type = EXP_ERR_NONE; // Known error types to expect/handle from test sequences
  bit saw_mbox_unlock = 1'b0;
  int datain_ii = CPTRA_MBOX_SIZE_BYTES/4; // Initialize to max value. This iterator is reset in mbox_push_datain for loop, but is
                                           // evaluated against specific offsets for some error checking cases. So give it an
                                           // unambiguously invalid init value prior to use.

  typedef enum byte {
    DLY_ZERO,
    DLY_SMALL,
    DLY_MEDIUM,
    DLY_LARGE,
    DLY_CUSTOM
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

  // AxUSER tracking/override
  bit [aaxi_pkg::AAXI_AWUSER_WIDTH-1:0] mbox_valid_users [6];
  bit mbox_valid_users_initialized = 1'b0;
  bit [aaxi_pkg::AAXI_AWUSER_WIDTH-1:0] mbox_user_override_val;
  bit override_mbox_user = 1'b0;
  caliptra_axi_user axi_user_obj; // Handle to the most recently generated user object
  struct packed {
      bit [aaxi_pkg::AAXI_AWUSER_WIDTH-1:0] axi_user; /* Value of AxUSER when mbox lock acquired */
      bit                                   locked;
  } axi_user_locked = '{axi_user: '1, locked: 1'b0};
  int hit_invalid_axi_user_count = '0;

  localparam FORCE_VALID_AXI_USER = 0;
  int unsigned AXI_USER_PROB_LOCK   ;
  int unsigned AXI_USER_PROB_CMD    ;
  int unsigned AXI_USER_PROB_DATAIN ;
  int unsigned AXI_USER_PROB_EXECUTE;
  int unsigned AXI_USER_PROB_STATUS ;
  int unsigned AXI_USER_PROB_DATAOUT;

  extern virtual task mbox_setup();
  extern virtual task mbox_acquire_lock(output op_sts_e op_sts);
  extern virtual task mbox_set_cmd(input mbox_op_s op);
  extern virtual task mbox_push_datain();
  extern virtual task mbox_push_datain_axi();
  extern virtual task mbox_execute();
  extern virtual task mbox_check_status(output mbox_status_e data, output mbox_fsm_state_e state);
  extern virtual task mbox_read_resp_data();
  extern virtual task mbox_poll_status();
  extern virtual task mbox_clr_execute();
  extern virtual task mbox_teardown();

  extern virtual task                       do_rand_delay(input bit do_delay_randomize=1, input delay_scale_e scale=DLY_SMALL);
  extern virtual function void              set_axi_user_prob_vals();
  extern virtual function bit               axi_user_used_is_valid(caliptra_axi_user user_handle = null);
  extern virtual function caliptra_axi_user get_rand_user(int unsigned invalid_prob = FORCE_VALID_AXI_USER);
  extern virtual task                       report_reg_sts(uvm_status_e reg_sts, string name, caliptra_axi_user user_handle = null);

  // Constrain command to not be firmware or uC-initiated
  constraint mbox_cmd_c { mbox_op_rand.cmd.cmd_s.fw        == 1'b0;
                          mbox_op_rand.cmd.cmd_s.uc_to_soc == 1'b0; }

  // Constrain size to less than 128KiB for now (mailbox size), but we will
  // recalculate this based on the command being sent
  constraint mbox_dlen_max_c { mbox_op_rand.dlen <= CPTRA_MBOX_SIZE_BYTES; }
  // Minimum 2 dwords to include dlen/mbox_resp_expected_dlen at the beginning
  // IFF the response data is required
  constraint mbox_dlen_min_c { mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_op_rand.dlen >= 32'h8; }
  // Response data is only non-zero if a response is requested, and also must
  // be small enough to fit in the mailbox
  constraint mbox_resp_dlen_c {                                      mbox_resp_expected_dlen <= CPTRA_MBOX_SIZE_BYTES;
                                !mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_resp_expected_dlen == 0;
                                 mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_resp_expected_dlen >  0; }

  // After acquiring the lock, it is informative to read from the mbox_status
  // and mbox_user registers to confirm that lock acquisition had the intended
  // side-effects. But doing register reads on AXI actually affects the
  // system - so we get more interesting coverage by skipping it sometimes
  constraint axi_reg_check_c {do_axi_lock_check dist {0:/1, 1:/1};}
  constraint retry_failed_reg_c {retry_failed_reg_axs == 1'b1;}

  // Constraint on the random delays injected between each step of the flow.
  // By default, delays minimal to avoid protracting the test too much.
  // Targeted sequences may override this constraint.
  constraint delay_scale_c { poll_delay == DLY_MEDIUM;
                             step_delay == DLY_SMALL;
                             data_delay == DLY_ZERO; }
  // Should not be overridden
  constraint delay_scale_valid_c { poll_delay != DLY_CUSTOM;
                                   step_delay != DLY_CUSTOM;
                                   data_delay != DLY_CUSTOM; }
  // These constraints conflict with each other - only the one that is applicable
  // should be enabled; this is done in the definition of do_rand_delay
  constraint zero_delay_c  { rand_delay == 0;}
  constraint small_delay_c { rand_delay dist {   0  :/ 1000,
                                              [1:3] :/ 100,
                                              [4:7] :/ 25,
                                              [8:31]:/ 1};}
  constraint medium_delay_c { rand_delay dist {   0    :/ 10,
                                               [1:7]   :/ 50,
                                               [8:31]  :/ 100,
                                               [32:255]:/ 50};}
  constraint large_delay_c { rand_delay dist {        15  :/ 1,
                                              [ 16 : 255] :/ 50,
                                              [ 256:1023] :/ 100,
                                              [1024:8191] :/ 25};}
  // This deliberately intractable constraint must be overridden
  // by a child sequence if random delays are expected to be driven
  // by some custom rule set.
  constraint custom_delay_c { rand_delay == 0; rand_delay == 1; }

  //==========================================
  // Function:    new
  // Description: Constructor
  //==========================================
  function new(string name = "" );
    super.new(name);
    axi_user_obj = new();
    // Create an array of all defined mbox cmd values.
    // This can be used in constraints as appropriate
    defined_cmds = new[mbox_op_rand.cmd.cmd_e.num()];
    foreach (defined_cmds[idx]) begin
        if (idx == 0)
            defined_cmds[idx] = mbox_op_rand.cmd.cmd_e.first();
        else
            defined_cmds[idx] = defined_cmds[idx-1].next();
    end

    // Assign probabilties of generating invalid AxUSER at different stages
    set_axi_user_prob_vals();

    // Default constraint mode is SMALL random delays, updated when doing
    // the delay
    this.zero_delay_c  .constraint_mode(0);
    this.small_delay_c .constraint_mode(1);
    this.medium_delay_c.constraint_mode(0);
    this.large_delay_c .constraint_mode(0);
    this.custom_delay_c.constraint_mode(0);

    in_report_reg_sts = new("in_report_reg_sts");
  endfunction

  //==========================================
  // Function:    do_kill
  // Description: Called as part of sequencer.stop_sequences
  //              when invoked on the sequencer that is running
  //              this sequence.
  //==========================================
  virtual function void do_kill();
    // FIXME gracefully terminate any AXI requests pending?
    reg_model.soc_ifc_AXI_map.get_sequencer().stop_sequences(); // Kill any pending AXI transfers
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
        while (teardown_proc == null) begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    `uvm_info("MBOX_SEQ", $sformatf("Initiating command sequence to mailbox with cmd: [%p] dlen: [%p] resp_dlen: [%p]", mbox_op_rand.cmd.cmd_e, mbox_op_rand.dlen, mbox_resp_expected_dlen), UVM_MEDIUM)

    mbox_setup();               if (rand_delay_en) do_rand_delay(1, step_delay);
    mbox_acquire_lock(op_sts);  if (rand_delay_en) do_rand_delay(1, step_delay);
    fork
        while ((teardown_proc == null) && (!saw_mbox_unlock)) begin
            configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(1);
            saw_mbox_unlock = reg_model.mbox_csr_rm.mbox_unlock.unlock.get_mirrored_value();
        end
    join_none
    mbox_set_cmd(mbox_op_rand); if (rand_delay_en) do_rand_delay(1, step_delay);
    mbox_push_datain_axi();         if (rand_delay_en) do_rand_delay(1, step_delay);
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
    // Read the valid AxUSER fields from register mirrored value if the local array
    // has not already been overridden from default values
    if (!mbox_valid_users_initialized) begin
        for (ii=0; ii < $size(reg_model.soc_ifc_reg_rm.CPTRA_MBOX_AXI_USER_LOCK); ii++) begin: VALID_USER_LOOP
            if (reg_model.soc_ifc_reg_rm.CPTRA_MBOX_AXI_USER_LOCK[ii].LOCK.get_mirrored_value())
                mbox_valid_users[ii] = reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_AXI_USER[ii].get_mirrored_value();
            else
                mbox_valid_users[ii] = reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_AXI_USER[ii].get_reset("HARD");
        end
        // FIXME hardcoded default value of 32'hFFFF_FFFF
        mbox_valid_users[5] = '1;
        mbox_valid_users_initialized = 1'b1;
    end
    else begin
        for (ii=0; ii < $size(reg_model.soc_ifc_reg_rm.CPTRA_MBOX_AXI_USER_LOCK); ii++) begin: VALID_USER_CHECK_LOOP
            if (reg_model.soc_ifc_reg_rm.CPTRA_MBOX_AXI_USER_LOCK[ii].LOCK.get_mirrored_value() &&
                mbox_valid_users[ii] != reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_AXI_USER[ii].get_mirrored_value())
                `uvm_warning("MBOX_SEQ", "mbox_valid_users initialized with a value that does not match mirrored value in register model!")
        end
        if (~&mbox_valid_users[5]) begin
            `uvm_warning("MBOX_SEQ", $sformatf("mbox_valid_users initialized with a value that does not match the default valid user of 0x%x", 32'hFFFF_FFFF))
        end
    end
    if (override_mbox_user && !(mbox_user_override_val inside {mbox_valid_users})) begin
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
    reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_LOCK)));
    report_reg_sts(reg_sts, "mbox_lock");
    // Wait for read data to return with '0', indicating no other agent has lock
    while (data[reg_model.mbox_csr_rm.mbox_lock.lock.get_lsb_pos()]) begin
        do_rand_delay(1, poll_delay);
        reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_LOCK)));
        report_reg_sts(reg_sts, "mbox_lock");
    end

    if (do_axi_lock_check || reg_sts != UVM_IS_OK) begin
        // Check if we actually got the lock and if we expected to or not
        reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(this.axi_user_obj));
        report_reg_sts(reg_sts, "mbox_status");
        soc_has_lock = data[reg_model.mbox_csr_rm.mbox_status.soc_has_lock.get_lsb_pos()] && reg_sts == UVM_IS_OK;
        if (!soc_has_lock && axi_user_used_is_valid()) begin
            `uvm_error("MBOX_SEQ", "Failed to acquire lock when using valid AxUSER!")
            op_sts = CPTRA_INVALID;
        end
        else if (soc_has_lock && !axi_user_used_is_valid()) begin
            `uvm_error("MBOX_SEQ", "Acquired lock unexpectedly when using invalid AxUSER!")
        end

        // Check latest value of mbox_user
        reg_model.mbox_csr_rm.mbox_user.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(this.axi_user_obj));
        report_reg_sts(reg_sts, "mbox_user");
        if (soc_has_lock && (data != this.axi_user_obj.get_addr_user())) begin
            `uvm_error("MBOX_SEQ", "mbox_user does not match AXI_USER used when lock was acquired!")
            op_sts = CPTRA_INVALID;
        end
        else if (!soc_has_lock && (data == this.axi_user_obj.get_addr_user())) begin
            `uvm_error("MBOX_SEQ", "mbox_user unexpectedly updated when lock was not acquired!")
            op_sts = CPTRA_INVALID;
        end
        else begin
            `uvm_info("MBOX_SEQ", $sformatf("mbox_user matches expected value [0x%x] based on result of attempt to acquire lock", this.axi_user_obj.get_addr_user()), UVM_HIGH)
        end

        // If we don't already have the lock, acquire it using a valid AXI_USER
        if (!soc_has_lock && retry_failed_reg_axs) begin
            reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
            report_reg_sts(reg_sts, "mbox_lock");
            // Wait for read data to return with '0', indicating no other agent has lock
            while (data[reg_model.mbox_csr_rm.mbox_lock.lock.get_lsb_pos()]) begin
                do_rand_delay(1, poll_delay);
                reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(this.axi_user_obj));
                report_reg_sts(reg_sts, "mbox_lock");
            end
            this.axi_user_locked.axi_user = this.axi_user_obj.get_addr_user();

            // Check if we actually got the lock
            reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(this.axi_user_obj));
            report_reg_sts(reg_sts, "mbox_status");
            soc_has_lock = data[reg_model.mbox_csr_rm.mbox_status.soc_has_lock.get_lsb_pos()] && reg_sts == UVM_IS_OK;
            if (!axi_user_used_is_valid())
                `uvm_error("MBOX_SEQ", "AxUSER value used is not valid even after attempt to force it to a valid value!")
            else if (!soc_has_lock)
                `uvm_error("MBOX_SEQ", "Failed to acquire lock when using valid AxUSER!")
            else
                this.axi_user_locked.locked = 1'b1;

            // Check latest value of mbox_user
            reg_model.mbox_csr_rm.mbox_user.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(this.axi_user_obj));
            report_reg_sts(reg_sts, "mbox_user");
            if (soc_has_lock && (data != this.axi_user_obj.get_addr_user())) begin
                `uvm_error("MBOX_SEQ", "mbox_user does not match AxUSER used when lock was acquired!")
            end
            else if (!soc_has_lock && (data == this.axi_user_obj.get_addr_user())) begin
                `uvm_error("MBOX_SEQ", "mbox_user unexpectedly updated when using invalid AxUSER!")
            end
            else begin
                `uvm_info("MBOX_SEQ", $sformatf("mbox_user matches expected value [0x%x] based on result of attempt to acquire lock", this.axi_user_obj.get_addr_user()), UVM_HIGH)
            end

        end
        else if (soc_has_lock) begin
            this.axi_user_locked.axi_user = this.axi_user_obj.get_addr_user();
            this.axi_user_locked.locked = 1'b1;
        end
    end
    else begin
        this.axi_user_locked.axi_user = this.axi_user_obj.get_addr_user();
        this.axi_user_locked.locked = 1'b1;
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
    reg_model.mbox_csr_rm.mbox_cmd.write(reg_sts, uvm_reg_data_t'(op.cmd), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_CMD)));
    report_reg_sts(reg_sts, "mbox_cmd");
    if (!axi_user_used_is_valid()) begin
        if (rand_delay_en) do_rand_delay(1, step_delay);
        reg_model.mbox_csr_rm.mbox_cmd.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
        report_reg_sts(reg_sts, "mbox_cmd");
        if (data != prev_data)
            `uvm_error("MBOX_SEQ", "Write to mbox_cmd succeeded unexpectedly with invalid AxUSER!")
        else if (retry_failed_reg_axs) begin
            reg_model.mbox_csr_rm.mbox_cmd.write(reg_sts, uvm_reg_data_t'(op.cmd), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
            report_reg_sts(reg_sts, "mbox_cmd");
        end
    end

    if (rand_delay_en) do_rand_delay(1, step_delay);

    prev_data = reg_model.mbox_csr_rm.mbox_dlen.get_mirrored_value();
    reg_model.mbox_csr_rm.mbox_dlen.write(reg_sts, uvm_reg_data_t'(op.dlen), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_CMD)));
    report_reg_sts(reg_sts, "mbox_dlen");
    if (!axi_user_used_is_valid()) begin
        if (rand_delay_en) do_rand_delay(1, step_delay);
        reg_model.mbox_csr_rm.mbox_dlen.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
        report_reg_sts(reg_sts, "mbox_dlen");
        if (32'(data) != prev_data)
            `uvm_error("MBOX_SEQ", "Write to mbox_dlen succeeded unexpectedly with invalid AxUSER!")
        else if (retry_failed_reg_axs)  begin
            reg_model.mbox_csr_rm.mbox_dlen.write(reg_sts, uvm_reg_data_t'(op.dlen), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
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
    uvm_reg_data_t data;
    for (datain_ii=0; datain_ii < this.mbox_op_rand.dlen; datain_ii+=4) begin
        if (datain_ii == 0) begin
            data = uvm_reg_data_t'(mbox_op_rand.dlen - 8);
        end
        else if (datain_ii == 4) begin
            data = uvm_reg_data_t'(mbox_resp_expected_dlen);
        end
        else begin
            if (!std::randomize(data)) `uvm_error("MBOX_SEQ", "Failed to randomize data")
        end
        `uvm_info("MBOX_SEQ", $sformatf("[Iteration: %0d] Sending datain: 0x%x", datain_ii/4, data), UVM_DEBUG)
        reg_model.mbox_csr_rm.mbox_datain_sem.get();
        reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_DATAIN)));
        reg_model.mbox_csr_rm.mbox_datain_sem.put();
        report_reg_sts(reg_sts, "mbox_datain");
        if (!axi_user_used_is_valid() && retry_failed_reg_axs) begin
            if (rand_delay_en) do_rand_delay(1, data_delay);
            `uvm_info("MBOX_SEQ", "Re-do datain write with valid AxUSER", UVM_HIGH)
            reg_model.mbox_csr_rm.mbox_datain_sem.get();
            reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
            reg_model.mbox_csr_rm.mbox_datain_sem.put();
            report_reg_sts(reg_sts, "mbox_datain");
        end
        if (rand_delay_en) do_rand_delay(1, data_delay);
    end
endtask

//==========================================
// Task:        mbox_push_datain_axi
// Description: Write data in a loop to mbox_datain register
// NOTE:        This should be overridden with real data to write
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_push_datain_axi();
    uvm_reg_data_t data;
    aaxi_master_tr trans;
    for (datain_ii=0; datain_ii < this.mbox_op_rand.dlen; datain_ii+=4) begin
        if (datain_ii == 0) begin
            data = uvm_reg_data_t'(mbox_op_rand.dlen - 8);
            `uvm_info("KNU_MBOX", $sformatf("datain_ii = 0, data = %h", data), UVM_MEDIUM)
        end
        else if (datain_ii == 4) begin
            data = uvm_reg_data_t'(mbox_resp_expected_dlen);
            `uvm_info("KNU_MBOX", $sformatf("datain_ii = 4, data = %h", data), UVM_MEDIUM)
        end
        else begin
            if (!std::randomize(data)) `uvm_error("MBOX_SEQ", "Failed to randomize data")
        end
        `uvm_info("MBOX_SEQ", $sformatf("[Iteration: %0d] Sending datain: 0x%x", datain_ii/4, data), UVM_DEBUG)
        // reg_model.mbox_csr_rm.mbox_datain_sem.get();
        // reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_DATAIN)));
        // reg_model.mbox_csr_rm.mbox_datain_sem.put();
        // report_reg_sts(reg_sts, "mbox_datain");

        `uvm_create(trans);

        trans.kind = AAXI_WRITE;
        trans.vers = AAXI4;
        trans.addr = reg_model.mbox_csr_rm.mbox_datain.get_address(reg_model.soc_ifc_AXI_map);
        trans.id = 0;
        trans.len = 0;
        trans.size = 2;
        trans.burst = 0;
        trans.awuser = get_rand_user(FORCE_VALID_AXI_USER).get_addr_user();
        if ((datain_ii == 0) | (datain_ii == 4)) begin
            trans.data.push_back(data[7:0]);
            trans.data.push_back(data[15:8]);
            trans.data.push_back(data[23:16]);
            trans.data.push_back(data[31:24]);
        end
        else begin
            for (int k = 0; k < 4; k++)
                trans.data.push_back($urandom);
        end
        for (int k = 0; k < 4; k++)
            trans.strobes[k] = 1;
        trans.set_sequencer(reg_model.soc_ifc_AXI_map.get_sequencer());

        trans.adw_valid_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
        trans.aw_valid_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
        trans.b_valid_ready_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);

        `uvm_send(trans);

        // get_response(rsp);

        if (!axi_user_used_is_valid() && retry_failed_reg_axs) begin
            if (rand_delay_en) do_rand_delay(1, data_delay);
            `uvm_info("MBOX_SEQ", "Re-do datain write with valid AxUSER", UVM_HIGH)
            reg_model.mbox_csr_rm.mbox_datain_sem.get();
            reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
            reg_model.mbox_csr_rm.mbox_datain_sem.put();
            report_reg_sts(reg_sts, "mbox_datain");
        end
        if (rand_delay_en) do_rand_delay(1, data_delay);
    end
    for (datain_ii=0; datain_ii < this.mbox_op_rand.dlen; datain_ii+=4) begin
        get_response(rsp);
    end
endtask

//==========================================
// Task:        mbox_execute
// Description: Submit command to Caliptra by writing
//              1 to mbox_execute register
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_execute();
    uvm_reg_data_t data = uvm_reg_data_t'(1) << reg_model.mbox_csr_rm.mbox_execute.execute.get_lsb_pos();
    reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_EXECUTE)));
    report_reg_sts(reg_sts, "mbox_execute");
    if (!axi_user_used_is_valid() && retry_failed_reg_axs) begin
        if (rand_delay_en) do_rand_delay(1, step_delay);
        reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
        report_reg_sts(reg_sts, "mbox_execute");
    end
endtask

//==========================================
// Task:        mbox_check_status
// Description: Read mbox_status
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_check_status(output mbox_status_e data, output mbox_fsm_state_e state);
    uvm_reg_data_t reg_data;
    reg_model.mbox_csr_rm.mbox_status.read(reg_sts, reg_data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_STATUS)));
    report_reg_sts(reg_sts, "mbox_status");

    if (!axi_user_used_is_valid() && retry_failed_reg_axs) begin
        reg_model.mbox_csr_rm.mbox_status.read(reg_sts, reg_data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
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
    reg_model.mbox_csr_rm.mbox_dlen.read(reg_sts, dlen, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_DATAOUT)));
    report_reg_sts(reg_sts, "mbox_dlen");
    if (!axi_user_used_is_valid() && retry_failed_reg_axs) begin
        reg_model.mbox_csr_rm.mbox_dlen.read(reg_sts, dlen, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
        report_reg_sts(reg_sts, "mbox_dlen");
    end
    if (dlen != mbox_resp_expected_dlen) begin
        if (this.get_type_name() inside {"soc_ifc_env_mbox_reg_axs_invalid_sequence",
                                         "soc_ifc_env_mbox_reg_axs_invalid_small_sequence",
                                         "soc_ifc_env_mbox_reg_axs_invalid_medium_sequence",
                                         "soc_ifc_env_mbox_reg_axs_invalid_large_sequence"})
            `uvm_info("MBOX_SEQ", $sformatf("SOC received response data with mbox_dlen [%0d] that does not match the expected data amount [%0d]! Not flagging err since this is an invalid reg-access sequence [%s]", dlen, mbox_resp_expected_dlen, this.get_type_name()), UVM_LOW)
        else if (saw_mbox_unlock)
            `uvm_info("MBOX_SEQ", $sformatf("SOC received response data with mbox_dlen [%0d] that does not match the expected data amount [%0d]! Not flagging err since mbox_unlock was observed", dlen, mbox_resp_expected_dlen), UVM_LOW)
        else
            `uvm_error("MBOX_SEQ", $sformatf("SOC received response data with mbox_dlen [%0d] that does not match the expected data amount [%0d]!", dlen, mbox_resp_expected_dlen))
    end
    if (rand_delay_en) do_rand_delay(1, step_delay);
    for (ii=0; ii < dlen; ii+=4) begin
        reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_DATAOUT)));
        report_reg_sts(reg_sts, "mbox_dataout");
        if (!axi_user_used_is_valid() && retry_failed_reg_axs) begin
            if (rand_delay_en) do_rand_delay(1, data_delay);
            `uvm_info("MBOX_SEQ", "Re-do dataout read with valid AxUSER", UVM_HIGH)
            reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
            report_reg_sts(reg_sts, "mbox_dataout");
        end
        if (rand_delay_en && (ii+4) < dlen) do_rand_delay(1, data_delay);
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
    end while (data == CMD_BUSY && state != MBOX_IDLE && !saw_mbox_unlock);

    if (state == MBOX_IDLE) begin
        `uvm_info("MBOX_SEQ", "Detected mailbox state transition to IDLE - was mbox_unlock expected?", UVM_HIGH)
    end
    else if (saw_mbox_unlock) begin
        `uvm_info("MBOX_SEQ", "Detected mailbox unlock - was mbox_unlock expected?", UVM_HIGH)
    end
    else if (data == DATA_READY) begin
        if (mbox_resp_expected_dlen == 0 && sts_rsp_count > 0 && soc_ifc_status_agent_rsp_seq.rsp.cptra_error_non_fatal_intr_pending) begin
            `uvm_info("MBOX_SEQ", $sformatf("Unexpected status [%p] likely is the result of a spurious reg access injection specifically intended to cause a protocol violation", data), UVM_HIGH)
        end
        else if (mbox_resp_expected_dlen == 0)
            `uvm_error("MBOX_SEQ", $sformatf("Received status %p when not expecting any bytes of response data!", data))
        else begin
            mbox_read_resp_data();
        end
    end
    else if (data == CMD_FAILURE) begin
        if (sts_rsp_count > 0 && soc_ifc_status_agent_rsp_seq.rsp.cptra_error_non_fatal_intr_pending && mbox_sts_exp_error && mbox_sts_exp_error_type inside {EXP_ERR_PROT, EXP_ERR_ECC_UNC}) begin
            `uvm_info("MBOX_SEQ", $sformatf("Unexpected mailbox status [%p] likely is the result of a spurious reg access injection specifically intended to cause a protocol violation or a mailbox SRAM double bit flip. Expected err type: %p", data, mbox_sts_exp_error_type), UVM_HIGH)
        end
        else if (mbox_sts_exp_error && (mbox_sts_exp_error_type == EXP_ERR_RSP_DLEN)) begin
            `uvm_info("MBOX_SEQ", $sformatf("Mailbox status [%p] is expected due to spurious reg access injection against mbox_datain specifically intended to cause a protocol violation. Expected err type: %p", data, mbox_sts_exp_error_type), UVM_HIGH)
        end
        else begin
            `uvm_error("MBOX_SEQ", $sformatf("Received mailbox status %p unexpectedly, since there is no pending non_fatal error interrupt (or error injection was unexpected)", data))
        end
    end
    else if (data == CMD_COMPLETE) begin
        if (mbox_resp_expected_dlen != 0 && sts_rsp_count > 0 && soc_ifc_status_agent_rsp_seq.rsp.cptra_error_non_fatal_intr_pending)
            `uvm_info("MBOX_SEQ", $sformatf("Unexpected status [%p] when expecting 0x%x bytes of response data likely is the result of a spurious reg access injection specifically intended to cause a protocol violation", data, mbox_resp_expected_dlen), UVM_HIGH)
        else if (mbox_resp_expected_dlen != 0)
            `uvm_error("MBOX_SEQ", $sformatf("Received status %p when expecting 0x%x bytes of response data!", data, mbox_resp_expected_dlen))
    end
    else begin
        if (sts_rsp_count > 0 && soc_ifc_status_agent_rsp_seq.rsp.cptra_error_non_fatal_intr_pending)
            `uvm_info("MBOX_SEQ", $sformatf("Unexpected mailbox status [%p] likely is the result of a spurious reg access injection specifically intended to cause a protocol violation", data), UVM_HIGH)
        else
            `uvm_error("MBOX_SEQ", $sformatf("Received unexpected mailbox status [%p]", data))
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
    reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, uvm_reg_data_t'(0), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_EXECUTE)));
    report_reg_sts(reg_sts, "mbox_execute");
    if (!axi_user_used_is_valid() && retry_failed_reg_axs) begin
        if (rand_delay_en) do_rand_delay(1, step_delay);
        reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, uvm_reg_data_t'(0), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
        report_reg_sts(reg_sts, "mbox_execute");
    end

    if (rand_delay_en) do_rand_delay(1, step_delay);

    // Check for any non-fatal mailbox protocol or sram errors that occurred during the test
    reg_model.soc_ifc_reg_rm.CPTRA_HW_ERROR_NON_FATAL.read(reg_sts, err, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(500)));
    // don't use report_reg_sts since this isn't a mbox reg and doesn't have axi_user requirements
    if (reg_sts != UVM_IS_OK) begin
        `uvm_error("MBOX_SEQ", "Unexpected error on read from CPTRA_HW_ERROR_NON_FATAL")
    end
    if (|err) begin
        if (!mbox_sts_exp_error)
            `uvm_error("MBOX_SEQ", "Observed error in CPTRA_HW_ERROR_NON_FATAL unexpectedly, since sequence was not anticipating mailbox ECC errors or protocol violations")
        `uvm_info("MBOX_SEQ", "Detected non-fatal errors at end of mailbox flow. Clearing.", UVM_LOW)
        reg_model.soc_ifc_reg_rm.CPTRA_HW_ERROR_NON_FATAL.write(reg_sts, err, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(500)));
        if (reg_sts != UVM_IS_OK) begin
            `uvm_error("MBOX_SEQ", "Unexpected error on write to CPTRA_HW_ERROR_NON_FATAL")
        end
    end
endtask

//==========================================
// Task:        mbox_teardown
// Description: Placeholder task to allow derived classes
//              to add any end-of-sequence functionality.
//              Currently just reports AxUSER violation count.
//==========================================
task soc_ifc_env_mbox_sequence_base::mbox_teardown();
    this.teardown_proc = process::self();
    // Summary at sequence end
    `uvm_info("MBOX_SEQ", $sformatf("Count of mailbox accesses performed with invalid AxUSER: %0d", hit_invalid_axi_user_count), UVM_MEDIUM)
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
        this.custom_delay_c.constraint_mode(scale == DLY_CUSTOM);
        if (!this.randomize(rand_delay))
            `uvm_error("MBOX_SEQ", $sformatf("Failed to randomize rand_delay with scale %p", scale))
        else
            `uvm_info("MBOX_SEQ", $sformatf("Generated rand delay value: [%0d] cycles from constraint scale %p", rand_delay, scale), UVM_DEBUG)
    end
    if (rand_delay != 0)
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(rand_delay);
endtask

//==========================================
// Function:    set_axi_user_prob_vals
// Description: Assign values to class variables
//              that control the likelihood of AXI transfers
//              using an illegal AxUSER value at all stages
//              of the mailbox flow.
//==========================================
function void soc_ifc_env_mbox_sequence_base::set_axi_user_prob_vals();
  this.AXI_USER_PROB_LOCK    = FORCE_VALID_AXI_USER;
  this.AXI_USER_PROB_CMD     = FORCE_VALID_AXI_USER;
  this.AXI_USER_PROB_DATAIN  = FORCE_VALID_AXI_USER;
  this.AXI_USER_PROB_EXECUTE = FORCE_VALID_AXI_USER;
  this.AXI_USER_PROB_STATUS  = FORCE_VALID_AXI_USER;
  this.AXI_USER_PROB_DATAOUT = FORCE_VALID_AXI_USER;
endfunction

//==========================================
// Function:    get_rand_user
// Description: Return a caliptra_axi_user object populated with some value of
//              addr_user (with which to override AxUSER in the reg adapter).
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
// NOTE:        In the context of this function, the term 'valid' is overloaded.
//              mbox_valid_users contains the list of 'allowed' agent AxUSER values
//              that have access to issue commands to the mailbox.
//              Once the mailbox is locked, the only AxUSER value that is actually
//              considered "valid" is the value that was locked - other entries from
//              mbox_valid_users are not legal and will trigger protocol violations.
//              This function uses the more restrictive definition to evaluate constraints.
//==========================================
function caliptra_axi_user soc_ifc_env_mbox_sequence_base::get_rand_user(int unsigned invalid_prob = FORCE_VALID_AXI_USER);
    //axi_user_obj = new();
    if (!this.axi_user_obj.randomize() with {if (axi_user_locked.locked)
                                                 (addr_user == axi_user_locked.axi_user) dist
                                                 {1 :/ 1000,
                                                  0 :/ invalid_prob};
                                             // Override only applies to user value used to acquire lock
                                             else if (override_mbox_user)
                                                 addr_user == mbox_user_override_val;
                                             else
                                                 (addr_user inside {mbox_valid_users}) dist
                                                 {1 :/ 1000,
                                                  0 :/ invalid_prob};
                                             // When randomizing to a non-valid USER value after
                                             // AxUSER has been locked, make the assigned USER value
                                             // equally likely to be from the allowed agents as it is
                                             // to be some totally random (non-allowed) value
                                             if (axi_user_locked.locked)
                                                 (addr_user inside {mbox_valid_users}) dist
                                                 {1 :/ 1,
                                                  0 :/ 1}; })
        `uvm_error("MBOX_SEQ", "Failed to randomize AXI AxUSER override value")
    else
        `uvm_info("MBOX_SEQ", $sformatf("Randomized AXI AxUSER override value to 0x%x", this.axi_user_obj.addr_user), UVM_HIGH)
    this.hit_invalid_axi_user_count += axi_user_used_is_valid() ? 0 : 1;
    return this.axi_user_obj;
endfunction

//==========================================
// Function:    axi_user_used_is_valid
// Description: Assess whether the most recent AXI
//              transfer used a valid AxUSER or not
//==========================================
function bit soc_ifc_env_mbox_sequence_base::axi_user_used_is_valid(caliptra_axi_user user_handle = null);
    caliptra_axi_user user;
    if (user_handle == null) user = this.axi_user_obj;
    else                     user = user_handle;
    if (this.axi_user_locked.locked)
        return user.get_addr_user() == this.axi_user_locked.axi_user;
    else 
        return user.get_addr_user() inside {mbox_valid_users};
endfunction

//==========================================
// Function:    report_reg_sts
// Description: Generate informative messages about the result
//              of the most recent AXI transfer, accounting for
//              the AxUSER value that was used.
//==========================================
task soc_ifc_env_mbox_sequence_base::report_reg_sts(uvm_status_e reg_sts, string name, caliptra_axi_user user_handle = null);
    caliptra_axi_user user;
    int waiters = in_report_reg_sts.get_num_waiters();
    in_report_reg_sts.trigger();
    if (user_handle == null) user = this.axi_user_obj;
    else                     user = user_handle;
    // AXI error is flagged only for AxUSER that doesn't match the registered
    // values, it does not check that AxUSER matches the exact value in
    // mbox_user that was stored when lock was acquired (this results in a
    // silent error but a successful reg read).
    // Ergo, check against mbox_valid_users instead of axi_user_locked.
    if (reg_sts != UVM_IS_OK && user.get_addr_user() inside {mbox_valid_users})
        `uvm_error("MBOX_SEQ",
                   $sformatf("Register access failed unexpectedly with valid AxUSER! 0x%x (%s)", user.get_addr_user(), name))
    else if (reg_sts == UVM_IS_OK && !(user.get_addr_user() inside {mbox_valid_users}))
        `uvm_error("MBOX_SEQ",
                   $sformatf("Register access passed unexpectedly with invalid AxUSER! 0x%x (%s)", user.get_addr_user(), name))
    else
        `uvm_info("MBOX_SEQ",
                  $sformatf("Register access to (%s) with axi_user_used_is_valid: %b and reg_sts: %p", name, this.axi_user_used_is_valid(user), reg_sts),
                  UVM_HIGH)
    if (waiters)
        in_report_reg_sts.wait_off();
    else
        in_report_reg_sts.reset();
endtask
