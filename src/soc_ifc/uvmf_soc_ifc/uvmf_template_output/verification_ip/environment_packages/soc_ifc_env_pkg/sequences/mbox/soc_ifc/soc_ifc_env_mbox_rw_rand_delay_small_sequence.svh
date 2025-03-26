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
// DESCRIPTION: Extended from mbox delay sequence to exercise rand delays
//              throughout the test.
//              Tests small sized mailbox commands with delays.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_rw_rand_delay_small_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_rw_rand_delay_small_sequence )

  int datain_ii = CPTRA_MBOX_SIZE_BYTES/4;

  extern virtual task mbox_push_datain();
  extern virtual task mbox_read_resp_data();

  // Constrain dlen to be a small command
  // Max. size: 512B
  constraint mbox_dlen_max_small_c { mbox_op_rand.dlen <= 32'h0000_0200; }
  // Constrain response data size to also be small
  // Max. size: 512B
  constraint mbox_resp_dlen_max_small_c { mbox_resp_expected_dlen < 32'h0000_0200; }

  function new(string name = "");
    super.new(name);
    // super.axi_user_obj.set_addr_user(32'hFFFF_FFFF);
    // override_mbox_user = 1; //TODO: if this is removed, mbox valid users are changed and there's a hang - revisit
    // mbox_user_override_val = 32'hFFFF_FFFF;
  endfunction
endclass

task soc_ifc_env_mbox_rw_rand_delay_small_sequence::mbox_push_datain();
  uvm_reg_data_t data;

  for (datain_ii = 0; datain_ii < this.mbox_op_rand.dlen; datain_ii+=4) begin
    if (datain_ii == 0) begin
      data = uvm_reg_data_t'(this.mbox_op_rand.dlen - 8);
    end
    else if (datain_ii == 4) begin
      data = uvm_reg_data_t'(mbox_resp_expected_dlen);
    end
    else begin
      if (!std::randomize(data)) `uvm_error("MBOX_AXI_RW_SEQ", "Failed to randomize data")
    end
    `uvm_info("MBOX_AXI_RW_SEQ", $sformatf("[Iteration: %0d] Sending datain: 0x%x", datain_ii/4, data), UVM_MEDIUM)

    super.axi_user_obj.set_aw_valid_delay($urandom_range(configuration.aaxi_ci.minwaits,configuration.aaxi_ci.maxwaits));
    super.axi_user_obj.set_b_valid_ready_delay($urandom_range(configuration.aaxi_ci.minwaits,configuration.aaxi_ci.maxwaits));
    // super.axi_user_obj.set_wstrb();

    reg_model.mbox_csr_rm.mbox_datain_sem.get();
    reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(super.axi_user_obj));
    reg_model.mbox_csr_rm.mbox_datain_sem.put();
        
  end
endtask

task soc_ifc_env_mbox_rw_rand_delay_small_sequence::mbox_read_resp_data();
  uvm_reg_data_t data;
    uvm_reg_data_t dlen;
    int ii;

  reg_model.mbox_csr_rm.mbox_dlen.read(reg_sts, dlen, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(super.axi_user_obj));

  for (ii = 0; ii < dlen; ii+=4) begin
    super.axi_user_obj.set_ar_valid_delay($urandom_range(configuration.aaxi_ci.minwaits,configuration.aaxi_ci.maxwaits));
    super.axi_user_obj.set_resp_valid_ready_delay($urandom_range(configuration.aaxi_ci.minwaits,configuration.aaxi_ci.maxwaits));

    reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(super.axi_user_obj));
  end

endtask


