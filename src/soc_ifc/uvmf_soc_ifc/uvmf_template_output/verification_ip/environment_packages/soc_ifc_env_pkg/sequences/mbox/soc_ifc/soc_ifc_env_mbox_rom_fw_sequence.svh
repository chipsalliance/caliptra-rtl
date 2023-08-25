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
// DESCRIPTION: Extended from mbox_base sequence to complete a FW update
//              against the actual (FW-team developed) ROM.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_rom_fw_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_rom_fw_sequence )

  // 128KiB memory, with 32768 single-dword entries
  bit [7:0] fw_img [soc_ifc_pkg::MBOX_DEPTH][soc_ifc_pkg::MBOX_DATA_W/8-1:0];    

  extern virtual task mbox_setup();
  extern virtual task mbox_push_datain();

  // This shouldn't be randomized, specify it
  constraint mbox_cmd_c { mbox_op_rand.cmd == mbox_cmd_e'(MBOX_CMD_ROM_FW_UPD); }
  constraint mbox_dlen_c { mbox_op_rand.dlen == 13708; }
  // Response data is only non-zero if a response is requested, and also must
  // be small enough to fit in the mailbox
  // Firmware team encodes commands differently from this environment; response
  // bit is different, and ROM doesn't expect to provide a response for fw update.
  // Override to force this to 0.
  constraint mbox_resp_dlen_c { mbox_resp_expected_dlen == 0; }

endclass

task soc_ifc_env_mbox_rom_fw_sequence::mbox_setup();
    super.mbox_setup();
    //read FW from file to write to mailbox
    $readmemh("fw_update.hex", fw_img);
endtask

// This should be overridden with real data to write
task soc_ifc_env_mbox_rom_fw_sequence::mbox_push_datain();
    int ii;
    int firmware_end_dw;
    uvm_reg_data_t data;

    firmware_end_dw = this.mbox_op_rand.dlen / 4 + (this.mbox_op_rand.dlen%4 ? 1 : 0);

    `uvm_info("MBOX_SEQ", $sformatf("Starting FW push_datain. Size: [0x%x] dwords", firmware_end_dw), UVM_LOW)
    for (ii=0; ii < firmware_end_dw; ii++) begin
        data = uvm_reg_data_t'({fw_img[ii][3],fw_img[ii][2],fw_img[ii][1],fw_img[ii][0]});
        if (ii < 10)
            `uvm_info("MBOX_SEQ", $sformatf("[Iteration: %0d] Sending datain: 0x%x", ii, data), UVM_LOW)
        else
            `uvm_info("MBOX_SEQ", $sformatf("[Iteration: %0d] Sending datain: 0x%x", ii, data), UVM_DEBUG)
        reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_DATAIN)));
        report_reg_sts(reg_sts, "mbox_datain");
    end
endtask
