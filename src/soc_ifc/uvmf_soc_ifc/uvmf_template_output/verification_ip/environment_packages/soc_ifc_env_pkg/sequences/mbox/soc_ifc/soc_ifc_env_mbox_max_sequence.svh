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
class soc_ifc_env_mbox_max_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_max_sequence )

  extern virtual task mbox_push_datain();

  // Constrain command to undefined opcodes with no response required.
  constraint mbox_cmd_c { mbox_op_rand.cmd.cmd_e == MBOX_CMD_UC_OVERRUN;}

  // Constrain dlen to reach max or max-1
  constraint mbox_dlen_minmax_c { mbox_op_rand.dlen inside {32'h0002_0000,32'h0001_FFFF,32'h0001_FFFE,32'h0001_FFFD,
                                                            32'h0001_FFFC,32'h0001_FFFB,32'h0001_FFFA,32'h0001_FFF9}; }

endclass

//==========================================
// Task:        mbox_push_datain
// Description: Write data in a loop to mbox_datain register
// NOTE:        This should be overridden with real data to write
//==========================================
task soc_ifc_env_mbox_max_sequence::mbox_push_datain();
  int ii;
  uvm_reg_data_t data;
  for (ii=0; ii < this.mbox_op_rand.dlen; ii+=4) begin

    if (!std::randomize(data)) `uvm_error("MBOX_SEQ", "Failed to randomize data")

    `uvm_info("MBOX_SEQ", $sformatf("[Iteration: %0d] Sending datain: 0x%x", ii/4, data), UVM_DEBUG)
    reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_DATAIN)));
    report_reg_sts(reg_sts, "mbox_datain");
    if (!pauser_used_is_valid() && retry_failed_reg_axs) begin
        `uvm_info("MBOX_SEQ", "Re-do datain write with valid PAUSER", UVM_HIGH)
        reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
        report_reg_sts(reg_sts, "mbox_datain");
    end
  end
endtask