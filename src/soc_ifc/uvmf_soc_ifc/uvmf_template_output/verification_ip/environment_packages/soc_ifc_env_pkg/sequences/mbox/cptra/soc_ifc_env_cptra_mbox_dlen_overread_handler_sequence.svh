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
class soc_ifc_env_cptra_mbox_dlen_overread_handler_sequence extends soc_ifc_env_cptra_mbox_handler_sequence;


  `uvm_object_utils( soc_ifc_env_cptra_mbox_dlen_overread_handler_sequence )

  extern virtual task mbox_pop_dataout();


  function new(string name = "" );
    super.new(name);
  endfunction

endclass

task soc_ifc_env_cptra_mbox_dlen_overread_handler_sequence::mbox_pop_dataout();
    int ii;
    int unsigned overrun_bytes;
    uvm_reg_data_t data;

    if (!std::randomize(overrun_bytes) with {overrun_bytes + op.dlen <= (reg_model.mbox_mem_rm.get_size() * reg_model.mbox_mem_rm.get_n_bytes()); overrun_bytes < op.dlen * 4;})
        `uvm_error("CPTRA_MBOX_HANDLER", "Failed to randomize overrun bytes")
    else
        `uvm_info("CPTRA_MBOX_HANDLER", $sformatf("Randomized overrun bytes to %d", overrun_bytes), UVM_MEDIUM)

    for (ii=0; ii < op.dlen+overrun_bytes; ii+=4) begin
        reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        if (reg_sts != UVM_IS_OK)
            `uvm_error("MBOX_SEQ", "Register access failed (mbox_dataout)")
        if (ii == 4) begin
            // dword 1 of data indicates number of response bytes requested
            mbox_resp_expected_dlen = data;
        end
    end
endtask
