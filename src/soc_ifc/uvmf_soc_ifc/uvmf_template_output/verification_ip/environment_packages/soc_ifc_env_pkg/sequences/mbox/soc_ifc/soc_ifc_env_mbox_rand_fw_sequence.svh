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
class soc_ifc_env_mbox_rand_fw_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_rand_fw_sequence )

  extern virtual task mbox_push_datain();

  // Constrain command to be firmware
  constraint mbox_cmd_c { mbox_op_rand.cmd.cmd_s.fw == 1'b1; }
  // Constrain dlen to be a fw command
  // Max. size: 4096B
  constraint mbox_dlen_max_fw_c { mbox_op_rand.dlen <= 32'h0000_1000; }
  // Minimum 10 dwords to include dlen at the beginning of both ICCM/DCCM sections
  constraint mbox_dlen_min_fw_c { mbox_op_rand.dlen > 32'h28; }

endclass

// This should be overridden with real data to write
task soc_ifc_env_mbox_rand_fw_sequence::mbox_push_datain();
    int ii;
    uvm_reg_data_t data;
    uvm_reg_data_t first_size;
    first_size = uvm_reg_data_t'((mbox_op_rand.dlen - 32 - (mbox_op_rand.dlen%8))/2);
    `uvm_info("MBOX_SEQ", $sformatf("Starting FW push_datain, will inject dlen at ii= [0] and at [%d]", 16 + first_size), UVM_LOW)
    for (ii=0; ii < this.mbox_op_rand.dlen; ii+=4) begin
        if (ii == 0) begin
            data = first_size;
        end
        else if (ii == (16 + first_size)) begin
            data = uvm_reg_data_t'(mbox_op_rand.dlen - first_size);
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
