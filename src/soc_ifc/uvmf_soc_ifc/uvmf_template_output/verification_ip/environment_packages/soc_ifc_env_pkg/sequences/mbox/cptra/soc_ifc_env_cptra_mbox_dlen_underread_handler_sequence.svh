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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: Sequence to wait for Mailbox commands (from SoC) and
//              respond/handle the command
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_cptra_mbox_dlen_underread_handler_sequence extends soc_ifc_env_cptra_mbox_handler_sequence;


  `uvm_object_utils( soc_ifc_env_cptra_mbox_dlen_underread_handler_sequence )

  extern virtual task mbox_pop_dataout();


  function new(string name = "" );
    super.new(name);
  endfunction

endclass

task soc_ifc_env_cptra_mbox_dlen_underread_handler_sequence::mbox_pop_dataout();
    int ii;
    int unsigned underrun_bytes;
    int unsigned bytes_to_read;
    uvm_reg_data_t data;

    // minimum 5 bytes so we can grab the resp dlen
    if (!std::randomize(underrun_bytes) with {if (op.dlen > 4) underrun_bytes < op.dlen - 4;
                                              else             underrun_bytes == 0;})
        `uvm_error("CPTRA_MBOX_HANDLER", "Failed to randomize overrun bytes")
    else
        `uvm_info("CPTRA_MBOX_HANDLER", $sformatf("Randomized underrun bytes to %d", underrun_bytes), UVM_MEDIUM)

    bytes_to_read = op.dlen-underrun_bytes;
    if (bytes_to_read > 32'h8000_0000) begin
        `uvm_warning("MBOX_SEQ", $sformatf("Bytes to read is calculated as a huge number - was this intentional? bytes_to_read: %d (0x%x)", bytes_to_read, bytes_to_read))
    end
    else begin
        `uvm_info("MBOX_SEQ", $sformatf("Bytes to read is calculated as %d (0x%x)", bytes_to_read, bytes_to_read), UVM_HIGH)
    end

    for (ii=0; ii < bytes_to_read; ii+=4) begin
        reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        if (reg_sts != UVM_IS_OK)
            `uvm_error("MBOX_SEQ", "Register access failed (mbox_dataout)")
        if (ii == 4) begin
            // dword 1 of data indicates number of response bytes requested
            mbox_resp_expected_dlen = data;
        end
    end
endtask
