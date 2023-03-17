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
//              functionality that emulates the expected format of a
//              FW update transfer.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_uc_reg_access_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_uc_reg_access_sequence )

  extern virtual task mbox_push_datain();

  // This shouldn't be randomized, specify it
  constraint mbox_cmd_c { mbox_op_rand.cmd.cmd_e == MBOX_CMD_REG_ACCESS; }
  // maxing dlen, should be getting this from fw image
  constraint mbox_dlen_c { mbox_op_rand.dlen == 32'h0000_0008; }


endclass

// This should be overridden with real data to write
task soc_ifc_env_mbox_uc_reg_access_sequence::mbox_push_datain();

    uvm_reg_data_t data;

    data = uvm_reg_data_t'(32'h30030010);
    reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("MBOX_SEQ", "Register access failed (mbox_datain)")

endtask

