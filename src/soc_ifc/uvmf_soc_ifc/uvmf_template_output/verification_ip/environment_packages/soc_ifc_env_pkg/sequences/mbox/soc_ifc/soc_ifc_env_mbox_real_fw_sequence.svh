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
class soc_ifc_env_mbox_real_fw_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_real_fw_sequence )

  // 128KiB memory, with 32768 single-dword entries
  bit [7:0] fw_img [soc_ifc_pkg::MBOX_DEPTH][soc_ifc_pkg::MBOX_DATA_W/8-1:0];    
  int firmware_iccm_length;
  int firmware_dccm_length;
  int firmware_iccm_end;
  int firmware_end;

  extern virtual task mbox_setup();
  extern virtual task mbox_push_datain();

  // This shouldn't be randomized, specify it
  constraint mbox_cmd_c { mbox_op_rand.cmd.cmd_s.fw == 1'b1; }

endclass

task soc_ifc_env_mbox_real_fw_sequence::mbox_setup();
    super.mbox_setup();
    //read FW from file to write to mailbox
    if (mbox_op_rand.cmd.cmd_e == MBOX_CMD_FMC_UPDATE) begin
        $readmemh("caliptra_fmc.hex", fw_img);
    end else if (mbox_op_rand.cmd.cmd_e == MBOX_CMD_RT_UPDATE) begin
        $readmemh("caliptra_rt.hex", fw_img);
    end

    //Read the first dword, that's the length of ICCM location
    firmware_iccm_length = int'(fw_img[0][3:0]);
    firmware_iccm_end = firmware_iccm_length + 32'd16;
    //DCCM length is printed at end of ICCM
    firmware_dccm_length = int'(fw_img[firmware_iccm_end>>2][3:0]);
    //firmware end is after ICCM, DCCM and the two lines (16 bytes) of length encodings
    firmware_end = firmware_iccm_end + firmware_dccm_length + 32'd16;

    // Override dlen to reflect size of firmware image
    this.mbox_op_rand.dlen = firmware_end;
endtask

// This should be overridden with real data to write
task soc_ifc_env_mbox_real_fw_sequence::mbox_push_datain();
    int ii;
    int firmware_end_dw;
    uvm_reg_data_t data;

    firmware_end_dw = firmware_end/4 + (firmware_end%4 ? 1 : 0);

    `uvm_info("MBOX_SEQ", $sformatf("Starting FW push_datain, ICCM region ends at [0x%x] and DCCM region ends at [0x%x]", firmware_iccm_end, firmware_end), UVM_LOW)
    for (ii=0; ii < firmware_end_dw; ii++) begin
        data = uvm_reg_data_t'({fw_img[ii][3],fw_img[ii][2],fw_img[ii][1],fw_img[ii][0]});
        `uvm_info("MBOX_SEQ", $sformatf("[Iteration: %0d] Sending datain: 0x%x", ii/4, data), UVM_DEBUG)
        reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_DATAIN)));
        report_reg_sts(reg_sts, "mbox_datain");
    end
endtask

