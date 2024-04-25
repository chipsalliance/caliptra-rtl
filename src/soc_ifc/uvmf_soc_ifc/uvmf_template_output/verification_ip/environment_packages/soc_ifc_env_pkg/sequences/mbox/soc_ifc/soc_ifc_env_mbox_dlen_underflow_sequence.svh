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
// DESCRIPTION: Extended from mbox_base sequence to provide additional
//              functionality in a test that sends small mailbox commands.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_dlen_underflow_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_dlen_underflow_sequence )

  // Constrain command to undefined opcode
  constraint mbox_cmd_undef_c { !(mbox_op_rand.cmd.cmd_s inside {defined_cmds}); }

  extern virtual task mbox_push_datain();

  function new(string name = "" );
    super.new(name);
  endfunction

endclass

task soc_ifc_env_mbox_dlen_underflow_sequence::mbox_push_datain();
    uvm_reg_data_t data;
    int unsigned underflow_bytes;

    // Push less data than dlen requires - randomize how much less
    if (!std::randomize(underflow_bytes) with {!mbox_op_rand.cmd.cmd_s.resp_reqd -> underflow_bytes <= mbox_op_rand.dlen;
                                                mbox_op_rand.cmd.cmd_s.resp_reqd -> underflow_bytes <= mbox_op_rand.dlen - 8;})
        `uvm_error("MBOX_UNDERFLOW_SEQ", "Failed to randomize underflow bytes")
    else
        `uvm_info("MBOX_UNDERFLOW_SEQ", $sformatf("Randomized underflow bytes to %0d", underflow_bytes), UVM_MEDIUM)

    for (datain_ii=0; datain_ii < this.mbox_op_rand.dlen-underflow_bytes; datain_ii+=4) begin
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
        reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_DATAIN)));
        reg_model.mbox_csr_rm.mbox_datain_sem.put();
        report_reg_sts(reg_sts, "mbox_datain");
        if (!pauser_used_is_valid() && retry_failed_reg_axs) begin
            `uvm_info("MBOX_SEQ", "Re-do datain write with valid PAUSER", UVM_HIGH)
            reg_model.mbox_csr_rm.mbox_datain_sem.get();
            reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
            reg_model.mbox_csr_rm.mbox_datain_sem.put();
            report_reg_sts(reg_sts, "mbox_datain");
        end
    end
endtask
