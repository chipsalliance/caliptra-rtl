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

  extern virtual task mbox_setup();
  extern virtual task mbox_acquire_lock(output op_sts_e op_sts);
  extern virtual task mbox_set_cmd(input mbox_op_s op);
  extern virtual task mbox_push_datain();
  extern virtual task mbox_execute();
  extern virtual task mbox_check_status(output mbox_status_e data);
  extern virtual task mbox_read_resp_data();
  extern virtual task mbox_poll_status();
  extern virtual task mbox_clr_execute();
  extern virtual task mbox_teardown();

  // Constrain command to not be firmware
  constraint mbox_cmd_c { mbox_op_rand.cmd.cmd_s.fw == 1'b0; }

  // Constrain size to less than 128KiB for now (mailbox size), but we will
  // recalculate this based on the command being sent
  constraint mbox_dlen_max_c { mbox_op_rand.dlen <= 32'h0002_0000; }
  // Minimum 2 dwords to include dlen/mbox_resp_expected_dlen at the beginning
  // IFF the response data is required
  constraint mbox_dlen_min_c { mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_op_rand.dlen >= 32'h8; }
  // Response data is only non-zero if a response is requested, and also must
  // be small enough to fit in the mailbox
  constraint mbox_resp_dlen_c {                                      mbox_resp_expected_dlen <= 32'h0002_0000;
                                !mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_resp_expected_dlen == 0;
                                 mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_resp_expected_dlen >  0; }

  function new(string name = "" );
    super.new(name);

  endfunction

  virtual function void do_kill();
    // FIXME gracefully terminate any APB requests pending?
    reg_model.soc_ifc_APB_map.get_sequencer().stop_sequences(); // Kill any pending APB transfers
  endfunction

  virtual task pre_body();
    super.pre_body();
    reg_model = configuration.soc_ifc_rm;

    if (soc_ifc_status_agent_rsp_seq == null)
        `uvm_fatal("MBOX_SEQ", "Mailbox Sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")

    // Randomization checker requires a valid handle to reg-model, which it gets
    // from the configuration object (which is not set until pre_body())
    assert(mbox_op_rand.dlen <= (reg_model.mbox_mem_rm.get_size() * reg_model.mbox_mem_rm.get_n_bytes())) else
        `uvm_error("MBOX_SEQ", $sformatf("Randomized SOC_IFC environment mailbox base sequence with bad dlen. Max: [0x%x] Got: [0x%x]. Cmd randomized to %p", (reg_model.mbox_mem_rm.get_size() * reg_model.mbox_mem_rm.get_n_bytes()), mbox_op_rand.dlen, mbox_op_rand.cmd.cmd_e))
  endtask

  virtual task body();

    op_sts_e op_sts;

    sts_rsp_count = 0;

    fork
        forever begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    `uvm_info("MBOX_SEQ", $sformatf("Initiating command sequence to mailbox with cmd: [%p] dlen: [%p] resp_dlen: [%p]", mbox_op_rand.cmd.cmd_e, mbox_op_rand.dlen, mbox_resp_expected_dlen), UVM_MEDIUM)

    mbox_setup();
    mbox_acquire_lock(op_sts);
    mbox_set_cmd(mbox_op_rand);
    mbox_push_datain();
    mbox_execute();
    mbox_poll_status();
    mbox_clr_execute();
    mbox_teardown();
//    if (sts_rsp_count) `uvm_warning("MBOX_SEQ", $sformatf("Unhandled status responses received! Count: %d", sts_rsp_count))

  endtask

endclass

// TODO these functions are all intended to be overridden by inheriting sequence
//      although some (acquire lock) are simple and may not need any modification
task soc_ifc_env_mbox_sequence_base::mbox_setup();
    // placeholder
endtask

task soc_ifc_env_mbox_sequence_base::mbox_acquire_lock(output op_sts_e op_sts);
    uvm_reg_data_t data;
    op_sts = CPTRA_TIMEOUT;
    reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("MBOX_SEQ", "Register access failed (mbox_lock)")
    // Wait for read data to return with '0', indicating no other agent has lock
    while (data[reg_model.mbox_csr_rm.mbox_lock.lock.get_lsb_pos()]) begin
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(200);
        reg_model.mbox_csr_rm.mbox_lock.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        if (reg_sts != UVM_IS_OK)
            `uvm_error("MBOX_SEQ", "Register access failed (mbox_lock)")
    end
    op_sts = CPTRA_SUCCESS;
endtask

task soc_ifc_env_mbox_sequence_base::mbox_set_cmd(input mbox_op_s op);
    reg_model.mbox_csr_rm.mbox_cmd.write(reg_sts, uvm_reg_data_t'(op.cmd), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("MBOX_SEQ", "Register access failed (mbox_cmd)")
    reg_model.mbox_csr_rm.mbox_dlen.write(reg_sts, uvm_reg_data_t'(op.dlen), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("MBOX_SEQ", "Register access failed (mbox_dlen)")
endtask

// This should be overridden with real data to write
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
        `uvm_info("MBOX_SEQ", $sformatf("[Iteration: %d] Sending datain: 0x%x", ii/4, data), UVM_DEBUG)
        reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        if (reg_sts != UVM_IS_OK)
            `uvm_error("MBOX_SEQ", "Register access failed (mbox_datain)")
    end
endtask

task soc_ifc_env_mbox_sequence_base::mbox_execute();
    uvm_reg_data_t data = uvm_reg_data_t'(1) << reg_model.mbox_csr_rm.mbox_execute.execute.get_lsb_pos();
    reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("MBOX_SEQ", "Register access failed (mbox_execute)")
endtask

task soc_ifc_env_mbox_sequence_base::mbox_check_status(output mbox_status_e data);
    uvm_reg_data_t reg_data;
    reg_model.mbox_csr_rm.mbox_status.read(reg_sts, reg_data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    if (reg_sts != UVM_IS_OK) begin
        `uvm_error("MBOX_SEQ", "Register access failed (mbox_status)")
        data = CMD_FAILURE;
    end
    else begin
        data = mbox_status_e'(reg_data >> reg_model.mbox_csr_rm.mbox_status.status.get_lsb_pos());
    end
endtask

task soc_ifc_env_mbox_sequence_base::mbox_read_resp_data();
    uvm_reg_data_t data;
    int ii;
    for (ii=0; ii < mbox_resp_expected_dlen; ii+=4) begin
        reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    end
endtask

task soc_ifc_env_mbox_sequence_base::mbox_poll_status();
    mbox_status_e data;

    mbox_check_status(data);
    while (data == CMD_BUSY) begin
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(200);
        mbox_check_status(data);
    end

    if (data == DATA_READY) begin
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

task soc_ifc_env_mbox_sequence_base::mbox_clr_execute();
    reg_model.mbox_csr_rm.mbox_execute.write(reg_sts, uvm_reg_data_t'(0), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("MBOX_SEQ", "Register access failed (mbox_execute)")
endtask

task soc_ifc_env_mbox_sequence_base::mbox_teardown();
    // placeholder
endtask
