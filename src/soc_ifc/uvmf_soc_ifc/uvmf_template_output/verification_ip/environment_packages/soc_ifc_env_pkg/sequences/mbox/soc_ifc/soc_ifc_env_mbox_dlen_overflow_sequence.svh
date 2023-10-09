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
class soc_ifc_env_mbox_dlen_overflow_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_dlen_overflow_sequence )

  // Constrain command to undefined opcode
  constraint mbox_cmd_undef_c { !(mbox_op_rand.cmd.cmd_s inside {defined_cmds}); }

  extern virtual task mbox_push_datain();

  function new(string name = "" );
    super.new(name);
  endfunction

endclass

task soc_ifc_env_mbox_dlen_overflow_sequence::mbox_push_datain();
    int ii;
    uvm_reg_data_t data;
    int unsigned overflow_bytes;

    // Overflow the programmed DLEN by at least 1 dword, up to 4x the programmed DLEN
    // Ensure the constraint is solvable with dlen 0
    if (!std::randomize(overflow_bytes) with {overflow_bytes >= 4; 
                                              overflow_bytes <= (mbox_op_rand.dlen+1) * 4;})
        `uvm_error("MBOX_OVERFLOW_SEQ", "Failed to randomize overflow bytes")
    else
        `uvm_info("MBOX_OVERFLOW_SEQ", $sformatf("Randomized overflow bytes to %0d", overflow_bytes), UVM_MEDIUM)

    for (ii=0; ii < this.mbox_op_rand.dlen+overflow_bytes; ii+=4) begin
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
