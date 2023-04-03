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
// DESCRIPTION: Extended from mbox sequence base to exercise PAUSER filtering.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_rand_pauser_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_rand_pauser_sequence )

  bit [4:0] [apb5_master_0_params::PAUSER_WIDTH-1:0] mbox_valid_users;
  bit mbox_valid_users_initialized = 1'b0;
  rand bit [apb5_master_0_params::PAUSER_WIDTH-1:0] pauser_override;
  bit [31:0] hit_invalid_pauser_count = '0;
  struct packed {
      bit [apb5_master_0_params::PAUSER_WIDTH-1:0] pauser; /* Value of PAUSER when mbox lock acquired */
      bit                                          locked;
  } pauser_locked = '{pauser: '1, locked: 1'b0};
  bit retry_failed_reg_axs = 1'b1;

  function new(string name = "" );
    super.new(name);
  endfunction

  extern virtual function void adapter_set_pauser_valid();
  extern virtual function void adapter_set_lock_pauser();
  extern virtual function void adapter_set_cmd_pauser();
  extern virtual function void adapter_set_dlen_pauser();
  extern virtual function void adapter_set_datain_pauser();
  extern virtual function void adapter_set_execute_pauser();
  extern virtual function void adapter_set_check_status_pauser();
  extern virtual function void adapter_set_dataout_pauser();
  extern virtual function bit  pauser_override_in_valid_list();
  extern virtual function bit  pauser_override_is_valid();
  extern virtual function void report_reg_sts(uvm_status_e reg_sts, string name);
  extern virtual task mbox_setup();
  extern virtual task mbox_acquire_lock(output op_sts_e op_sts);
  extern virtual task mbox_set_cmd(input mbox_op_s op);
  extern virtual task mbox_push_datain();
  extern virtual task mbox_execute();
  extern virtual task mbox_check_status(output mbox_status_e data);
  extern virtual task mbox_read_resp_data();
  extern virtual task mbox_clr_execute();
  extern virtual task mbox_teardown();

endclass

// TODO these functions are all intended to be overridden by inheriting sequence
//      although some (acquire lock) are simple and may not need any modification
task soc_ifc_env_mbox_rand_pauser_sequence::mbox_setup();
    // Read the valid PAUSER fields from registers via APB if the local array
    // has not already been overridden from default values
    byte ii;
    uvm_status_e sts;
    if (!mbox_valid_users_initialized) begin
        for (ii=0; ii < 5; ii++) begin: VALID_USER_LOOP
            reg_model.soc_ifc_reg_rm.CPTRA_VALID_PAUSER[ii].read(sts, mbox_valid_users[ii], UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
            if (sts != UVM_IS_OK) `uvm_error("MBOX_PAUSER", $sformatf("Failed when reading CPTRA_VALID_PAUSER index %d", ii))
        end
        mbox_valid_users_initialized = 1'b1;
    end
endtask

task soc_ifc_env_mbox_rand_pauser_sequence::mbox_acquire_lock(output op_sts_e op_sts);
    uvm_reg_data_t data;
    bit soc_has_lock;

    // In first pass, set a random PAUSER (probably invalid) and attempt to get lock
    op_sts = CPTRA_TIMEOUT;
    adapter_set_lock_pauser();
    reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    report_reg_sts(reg_sts, "mbox_lock");
    // Wait for read data to return with '0', indicating no other agent has lock
    while (data[reg_model.mbox_csr_rm.mbox_lock.lock.get_lsb_pos()]) begin
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(200);
        adapter_set_lock_pauser();
        reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        report_reg_sts(reg_sts, "mbox_lock");
    end

    // Check if we actually got the lock and if we expected to or not
    reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    report_reg_sts(reg_sts, "mbox_status");
    soc_has_lock = data[reg_model.mbox_csr_rm.mbox_status.soc_has_lock.get_lsb_pos()];
    if (!soc_has_lock && (pauser_override_is_valid())) begin
        `uvm_error("MBOX_PAUSER", "Failed to acquire lock when using valid PAUSER!")
    end
    else if (soc_has_lock && !pauser_override_is_valid()) begin
        `uvm_error("MBOX_PAUSER", "Acquired lock unexpectedly when using invalid PAUSER!")
    end

    // Check latest value of mbox_user
    reg_model.mbox_csr_rm.mbox_user.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    report_reg_sts(reg_sts, "mbox_user");
    if (soc_has_lock && (data != this.pauser_override)) begin
        `uvm_error("MBOX_PAUSER", "mbox_user does not match pauser_override used when lock was acquired!")
    end
    else if (!soc_has_lock && (data == this.pauser_override)) begin
        `uvm_error("MBOX_PAUSER", "mbox_user unexpectedly updated when using invalid PAUSER!")
    end
    else begin
        `uvm_info("MBOX_PAUSER", "mbox_user matches expected value based on result of initial attempt to acquire lock", UVM_HIGH)
    end

    // If we don't already have the lock, acquire it using a valid PAUSER
    if (!soc_has_lock && retry_failed_reg_axs) begin
        adapter_set_pauser_valid();
        this.pauser_locked.pauser = this.pauser_override;
        reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        report_reg_sts(reg_sts, "mbox_lock");
        // Wait for read data to return with '0', indicating no other agent has lock
        while (data[reg_model.mbox_csr_rm.mbox_lock.lock.get_lsb_pos()]) begin
            configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(200);
            reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
            report_reg_sts(reg_sts, "mbox_lock");
        end

        // Check if we actually got the lock and if we expected to or not
        reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        report_reg_sts(reg_sts, "mbox_status");
        soc_has_lock = data[reg_model.mbox_csr_rm.mbox_status.soc_has_lock.get_lsb_pos()];
        if (!soc_has_lock)
            `uvm_error("MBOX_PAUSER", "Failed to acquire lock when using valid PAUSER!")
        else
            this.pauser_locked.locked = 1'b1;

        // Check latest value of mbox_user
        reg_model.mbox_csr_rm.mbox_user.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        report_reg_sts(reg_sts, "mbox_user");
        if (soc_has_lock && (data != this.pauser_override)) begin
            `uvm_error("MBOX_PAUSER", "mbox_user does not match pauser_override used when lock was acquired!")
        end
        else if (!soc_has_lock && (data == this.pauser_override)) begin
            `uvm_error("MBOX_PAUSER", "mbox_user unexpectedly updated when using invalid PAUSER!")
        end
        else begin
            `uvm_info("MBOX_PAUSER", "mbox_user matches expected value based on result of initial attempt to acquire lock", UVM_HIGH)
        end

    end
    else if (soc_has_lock) begin
        this.pauser_locked.pauser = this.pauser_override;
        this.pauser_locked.locked = 1'b1;
    end

    op_sts = CPTRA_SUCCESS;
endtask

task soc_ifc_env_mbox_rand_pauser_sequence::mbox_set_cmd(input mbox_op_s op);
    uvm_reg_data_t data;

    adapter_set_cmd_pauser();
    reg_model.mbox_csr_rm.mbox_cmd.write(reg_sts, uvm_reg_data_t'(op.cmd), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    report_reg_sts(reg_sts, "mbox_cmd");
    if (!pauser_override_is_valid()) begin
        adapter_set_pauser_valid();
        reg_model.mbox_csr_rm.mbox_cmd.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        report_reg_sts(reg_sts, "mbox_cmd");
        if (mbox_cmd_u'(data) == op.cmd)
            `uvm_error("MBOX_PAUSER", "Write to mbox_cmd succeeded unexpectedly with invalid PAUSER!")
        else if (retry_failed_reg_axs) begin
            reg_model.mbox_csr_rm.mbox_cmd.write(reg_sts, uvm_reg_data_t'(op.cmd), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
            report_reg_sts(reg_sts, "mbox_cmd");
        end
    end

    adapter_set_dlen_pauser();
    reg_model.mbox_csr_rm.mbox_dlen.write(reg_sts, uvm_reg_data_t'(op.dlen), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    report_reg_sts(reg_sts, "mbox_dlen");
    if (!pauser_override_is_valid()) begin
        adapter_set_pauser_valid();
        reg_model.mbox_csr_rm.mbox_dlen.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        report_reg_sts(reg_sts, "mbox_dlen");
        if (32'(data) == op.dlen)
            `uvm_error("MBOX_PAUSER", "Write to mbox_dlen succeeded unexpectedly with invalid PAUSER!")
        else if (retry_failed_reg_axs)  begin
            reg_model.mbox_csr_rm.mbox_dlen.write(reg_sts, uvm_reg_data_t'(op.dlen), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
            report_reg_sts(reg_sts, "mbox_dlen");
        end
    end
endtask

// This should be overridden with real data to write
task soc_ifc_env_mbox_rand_pauser_sequence::mbox_push_datain();
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
        `uvm_info("MBOX_SEQ", $sformatf("[Iteration: %d] Sending datain: 0x%x", ii/4, data), UVM_DEBUG)
        adapter_set_datain_pauser();
        reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        report_reg_sts(reg_sts, "mbox_datain");
        if (!pauser_override_is_valid() && retry_failed_reg_axs) begin
            `uvm_info("MBOX_PAUSER", "Re-do datain write with valid PAUSER", UVM_HIGH)
            adapter_set_pauser_valid();
            reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
            report_reg_sts(reg_sts, "mbox_datain");
        end
    end
endtask

task soc_ifc_env_mbox_rand_pauser_sequence::mbox_execute();
    uvm_reg_data_t data = uvm_reg_data_t'(1) << reg_model.mbox_csr_rm.mbox_execute.execute.get_lsb_pos();
    adapter_set_execute_pauser();
    reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    report_reg_sts(reg_sts, "mbox_execute");
    if (!pauser_override_is_valid() && retry_failed_reg_axs) begin
        adapter_set_pauser_valid();
        reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        report_reg_sts(reg_sts, "mbox_execute");
    end
endtask

task soc_ifc_env_mbox_rand_pauser_sequence::mbox_check_status(output mbox_status_e data);
    uvm_reg_data_t reg_data;
    adapter_set_check_status_pauser();

    reg_model.mbox_csr_rm.mbox_status.read(reg_sts, reg_data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    report_reg_sts(reg_sts, "mbox_status");

    if (!pauser_override_is_valid() && retry_failed_reg_axs) begin
        adapter_set_pauser_valid();
        reg_model.mbox_csr_rm.mbox_status.read(reg_sts, reg_data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        report_reg_sts(reg_sts, "mbox_status");
    end

    if (reg_sts != UVM_IS_OK) begin
        data = CMD_FAILURE;
    end
    else begin
        data = mbox_status_e'(reg_data >> reg_model.mbox_csr_rm.mbox_status.status.get_lsb_pos());
    end
endtask

task soc_ifc_env_mbox_rand_pauser_sequence::mbox_read_resp_data();
    uvm_reg_data_t data;
    int ii;
    for (ii=0; ii < mbox_resp_expected_dlen; ii+=4) begin
        adapter_set_dataout_pauser();
        reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        report_reg_sts(reg_sts, "mbox_dataout");
        if (!pauser_override_is_valid() && retry_failed_reg_axs) begin
            `uvm_info("MBOX_PAUSER", "Re-do dataout read with valid PAUSER", UVM_HIGH)
            adapter_set_pauser_valid();
            reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
            report_reg_sts(reg_sts, "mbox_dataout");
        end
    end
endtask

task soc_ifc_env_mbox_rand_pauser_sequence::mbox_clr_execute();
    adapter_set_execute_pauser();
    reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, uvm_reg_data_t'(0), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    report_reg_sts(reg_sts, "mbox_execute");
    if (!pauser_override_is_valid() && retry_failed_reg_axs) begin
        adapter_set_pauser_valid();
        reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, uvm_reg_data_t'(0), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        report_reg_sts(reg_sts, "mbox_execute");
    end
endtask

task soc_ifc_env_mbox_rand_pauser_sequence::mbox_teardown();
    // Summary at sequence end
    `uvm_info("MBOX_PAUSER", $sformatf("Count of mailbox accesses performed with invalid PAUSER: %d", hit_invalid_pauser_count), UVM_MEDIUM)
endtask

function bit soc_ifc_env_mbox_rand_pauser_sequence::pauser_override_in_valid_list();
    return (this.pauser_override inside {mbox_valid_users[0],
                                         mbox_valid_users[1],
                                         mbox_valid_users[2],
                                         mbox_valid_users[3],
                                         mbox_valid_users[4]});
endfunction

function bit soc_ifc_env_mbox_rand_pauser_sequence::pauser_override_is_valid();
    if (this.pauser_locked.locked)
        return this.pauser_override == this.pauser_locked.pauser;
    else 
        return pauser_override_in_valid_list();
endfunction

function void soc_ifc_env_mbox_rand_pauser_sequence::report_reg_sts(uvm_status_e reg_sts, string name);
    // APB error is flagged only for PAUSER that doesn't match the registered
    // values, it does not check that PAUSER matches the exact value in
    // mbox_user that was stored when lock was acquired (this results in a
    // silent error but a successful reg read).
    // Ergo, use pauser_override_in_valid_list instead of pauser_override_is_valid.
    if (reg_sts != UVM_IS_OK && pauser_override_in_valid_list())
        `uvm_error("MBOX_SEQ",
                   $sformatf("Register access failed unexpectedly with valid PAUSER! 0x%x (%s)", this.pauser_override, name))
    else if (reg_sts == UVM_IS_OK && !pauser_override_in_valid_list()/*!pauser_override_is_valid()*/)
        `uvm_error("MBOX_SEQ",
                   $sformatf("Register access passed unexpectedly with invalid PAUSER! 0x%x (%s)", this.pauser_override, name))
    else
        `uvm_info("MBOX_SEQ",
                  $sformatf("Register access to (%s) with pauser_override_is_valid: %b and reg_sts: %p", name, pauser_override_is_valid(), reg_sts),
                  UVM_HIGH)
endfunction

function void soc_ifc_env_mbox_rand_pauser_sequence::adapter_set_pauser_valid();
    if (this.pauser_locked.locked) begin
        this.pauser_override = this.pauser_locked.pauser;
        configuration.apb_reg_adapter_h.pauser_override = this.pauser_override;
        return;
    end
    if (!this.randomize(pauser_override) with { pauser_override inside {mbox_valid_users[0],mbox_valid_users[1],mbox_valid_users[2],mbox_valid_users[3],mbox_valid_users[4]}; }) begin
        `uvm_error("MBOX_PAUSER", "Failed to randomize pauser_override")
    end
    else begin
        configuration.apb_reg_adapter_h.pauser_override = this.pauser_override;
    end
endfunction

function void soc_ifc_env_mbox_rand_pauser_sequence::adapter_set_lock_pauser();
    // Slightly more likely to randomly generate a valid PAUSER override, so
    // the first occurrence of invalid PAUSER is later
    // on (or, very rarely, never happens).
    // We want to stimulate the bad-actor scenario, but at varying points
    // throughout the sequence.
    // It is occasionally interesting to let invalid PAUSER be generated on the
    // first attempt though.
    if (!this.randomize(pauser_override) with {(pauser_override inside { mbox_valid_users[0],mbox_valid_users[1],mbox_valid_users[2],mbox_valid_users[3],mbox_valid_users[4]})
                                               dist {1 :/ 3,
                                                     0 :/ 1};}) begin
        `uvm_fatal("MBOX_PAUSER", "Failed to randomize pauser_override")
    end
    else begin
        configuration.apb_reg_adapter_h.pauser_override = this.pauser_override;
        this.hit_invalid_pauser_count += pauser_override_is_valid() ? 0 : 1;
    end
endfunction

function void soc_ifc_env_mbox_rand_pauser_sequence::adapter_set_cmd_pauser();
    this.adapter_set_lock_pauser(); // FIXME
endfunction

function void soc_ifc_env_mbox_rand_pauser_sequence::adapter_set_dlen_pauser();
    this.adapter_set_lock_pauser(); // FIXME
endfunction

function void soc_ifc_env_mbox_rand_pauser_sequence::adapter_set_datain_pauser();
    // Wildly more likely to generate a valid PAUSER, since we do so many accesses
    // against datain it is almost certain at _some_ point to be invalid
    if (!this.randomize(pauser_override) with {(pauser_override inside { mbox_valid_users[0],mbox_valid_users[1],mbox_valid_users[2],mbox_valid_users[3],mbox_valid_users[4]})
                                               dist {1 :/ 100,
                                                     0 :/ 1};}) begin
        `uvm_fatal("MBOX_PAUSER", "Failed to randomize pauser_override")
    end
    else begin
        configuration.apb_reg_adapter_h.pauser_override = this.pauser_override;
        this.hit_invalid_pauser_count += pauser_override_is_valid() ? 0 : 1;
    end
endfunction

function void soc_ifc_env_mbox_rand_pauser_sequence::adapter_set_execute_pauser();
    this.adapter_set_lock_pauser(); // FIXME
endfunction

function void soc_ifc_env_mbox_rand_pauser_sequence::adapter_set_check_status_pauser();
    // More likely to generate a valid PAUSER, since we do so many accesses
    // against mbox_status while polling
    if (!this.randomize(pauser_override) with {(pauser_override inside { mbox_valid_users[0],mbox_valid_users[1],mbox_valid_users[2],mbox_valid_users[3],mbox_valid_users[4]})
                                               dist {1 :/ 8,
                                                     0 :/ 1};}) begin
        `uvm_fatal("MBOX_PAUSER", "Failed to randomize pauser_override")
    end
    else begin
        configuration.apb_reg_adapter_h.pauser_override = this.pauser_override;
        this.hit_invalid_pauser_count += pauser_override_is_valid() ? 0 : 1;
    end
endfunction

function void soc_ifc_env_mbox_rand_pauser_sequence::adapter_set_dataout_pauser();
    // Wildly more likely to generate a valid PAUSER, since we do so many accesses
    // against dataout it is almost certain at _some_ point to be invalid
    if (!this.randomize(pauser_override) with {(pauser_override inside { mbox_valid_users[0],mbox_valid_users[1],mbox_valid_users[2],mbox_valid_users[3],mbox_valid_users[4]})
                                               dist {1 :/ 100,
                                                     0 :/ 1};}) begin
        `uvm_fatal("MBOX_PAUSER", "Failed to randomize pauser_override")
    end
    else begin
        configuration.apb_reg_adapter_h.pauser_override = this.pauser_override;
        this.hit_invalid_pauser_count += pauser_override_is_valid() ? 0 : 1;
    end
endfunction
