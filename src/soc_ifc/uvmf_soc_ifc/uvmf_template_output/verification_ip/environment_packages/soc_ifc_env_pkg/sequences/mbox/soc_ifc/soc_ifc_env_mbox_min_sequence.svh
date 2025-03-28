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
class soc_ifc_env_mbox_min_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_min_sequence )

  extern virtual task mbox_push_datain();

  // Constrain command to undefined opcodes with no response required.
  constraint mbox_cmd_c { mbox_op_rand.cmd.cmd_e == MBOX_CMD_UC_OVERRUN;}

  // Constrain dlen to be 0-1 dword
  constraint mbox_dlen_minmax_c { mbox_op_rand.dlen inside {32'h0000_0000,32'h0000_0001,32'h0000_0002,32'h0000_0003}; }

endclass

//==========================================
// Task:        mbox_push_datain
// Description: Write data in a loop to mbox_datain register
// NOTE:        This should be overridden with real data to write
//==========================================
task soc_ifc_env_mbox_min_sequence::mbox_push_datain();
  uvm_reg_data_t data;
  for (datain_ii=0; datain_ii < this.mbox_op_rand.dlen; datain_ii+=4) begin

    if (!std::randomize(data)) `uvm_error("MBOX_SEQ", "Failed to randomize data")

    `uvm_info("MBOX_SEQ", $sformatf("[Iteration: %0d] Sending datain: 0x%x", datain_ii/4, data), UVM_DEBUG)
    reg_model.mbox_csr_rm.mbox_datain_sem.get();
    reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_DATAIN)));
    reg_model.mbox_csr_rm.mbox_datain_sem.put();
    report_reg_sts(reg_sts, "mbox_datain");
    if (!axi_user_used_is_valid() && retry_failed_reg_axs) begin
        `uvm_info("MBOX_SEQ", "Re-do datain write with valid AxUSER", UVM_HIGH)
        reg_model.mbox_csr_rm.mbox_datain_sem.get();
        reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
        reg_model.mbox_csr_rm.mbox_datain_sem.put();
        report_reg_sts(reg_sts, "mbox_datain");
    end
  end
endtask
