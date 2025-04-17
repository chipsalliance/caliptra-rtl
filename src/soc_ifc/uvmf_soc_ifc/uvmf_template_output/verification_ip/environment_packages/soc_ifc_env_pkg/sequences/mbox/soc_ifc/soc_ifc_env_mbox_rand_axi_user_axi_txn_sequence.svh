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
// DESCRIPTION: Extended from mbox sequence base to exercise AXI_USER filtering.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_rand_axi_user_axi_txn_sequence extends soc_ifc_env_mbox_axi_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_rand_axi_user_axi_txn_sequence )

  int datain_ii = CPTRA_MBOX_SIZE_BYTES/4; // Initialize to max value. This iterator is reset in mbox_push_datain for loop, but is
                                           // evaluated against specific offsets for some error checking cases. So give it an
                                           // unambiguously invalid init value prior to use.

  extern virtual function void              set_axi_user_prob_vals();
  extern virtual task                       mbox_push_datain();   
  extern virtual task                       mbox_read_resp_data();

  // Force the lock check when deliberately testing AXI accesses with invalid AXI_USER values
  constraint axi_reg_check_c {do_axi_lock_check == 1;}
  constraint retry_failed_reg_c {retry_failed_reg_axs == 1'b1;}

  // Constrain command to undefined opcode
  constraint mbox_cmd_undef_c { !(mbox_op_rand.cmd.cmd_s inside {defined_cmds}); }

  function new(string name = "" );
    super.new(name);
    this.mbox_sts_exp_error = 1;
    this.mbox_sts_exp_error_type = EXP_ERR_PROT;
  endfunction

endclass

function void soc_ifc_env_mbox_rand_axi_user_axi_txn_sequence::set_axi_user_prob_vals();
  // ============ OVERRIDES for rand probability members ============
  // Make it slightly more likely to randomly generate a valid AXI_USER override
  // for earlier calls, so the first occurrence of invalid AXI_USER is later
  // on (or, very rarely, never happens).
  // We want to stimulate the bad-actor scenario, but at varying points
  // throughout the sequence.
  // It is occasionally interesting to let invalid AXI_USER be generated on the
  // first attempt though.
  this.AXI_USER_PROB_LOCK    = 350;
  this.AXI_USER_PROB_CMD     = AXI_USER_PROB_LOCK;
  // Wildly more likely to generate a valid AXI_USER, since we do so many accesses
  // against datain it is almost certain at _some_ point to be invalid
  this.AXI_USER_PROB_DATAIN  = 25;
  this.AXI_USER_PROB_EXECUTE = AXI_USER_PROB_LOCK;
  // More likely to generate a valid AXI_USER, since we do so many accesses
  // against mbox_status while polling
  this.AXI_USER_PROB_STATUS  = 150;
  // Wildly more likely to generate a valid AXI_USER, since we do so many accesses
  // against dataout it is almost certain at _some_ point to be invalid
  this.AXI_USER_PROB_DATAOUT = AXI_USER_PROB_DATAIN;
endfunction

//==========================================
// Task:        mbox_push_datain_axi
// Description: Write data in a loop to mbox_datain register
// NOTE:        This should be overridden with real data to write
//==========================================
task soc_ifc_env_mbox_rand_axi_user_axi_txn_sequence::mbox_push_datain();
  uvm_reg_data_t data;
  aaxi_master_tr trans;
  for (datain_ii=0; datain_ii < this.mbox_op_rand.dlen; datain_ii+=4) begin
      if (datain_ii == 0) begin
          data = uvm_reg_data_t'(mbox_op_rand.dlen - 8);
      end
      else if (datain_ii == 4) begin
          data = uvm_reg_data_t'(mbox_resp_expected_dlen);
      end
      else begin
          if (!std::randomize(data)) `uvm_error("MBOX_AXI_SEQ", "Failed to randomize data")
      end
      `uvm_info("MBOX_AXI_SEQ", $sformatf("[Iteration: %0d] Sending datain: 0x%x", datain_ii/4, data), UVM_DEBUG)
      // reg_model.mbox_csr_rm.mbox_datain_sem.get();
      // reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_DATAIN)));
      // reg_model.mbox_csr_rm.mbox_datain_sem.put();
      // report_reg_sts(reg_sts, "mbox_datain");

      `uvm_create(trans);

      trans.kind = AAXI_WRITE;
      trans.vers = AAXI4;
      trans.addr = reg_model.mbox_csr_rm.mbox_datain.get_address(reg_model.soc_ifc_AXI_map);
      trans.id = $urandom();
      trans.len = 0;
      trans.size = 2;
      trans.burst = 0;
      trans.awuser = get_rand_user(FORCE_VALID_AXI_USER).get_addr_user();
      if ((datain_ii == 0) | (datain_ii == 4)) begin
          trans.data.push_back(data[7:0]);
          trans.data.push_back(data[15:8]);
          trans.data.push_back(data[23:16]);
          trans.data.push_back(data[31:24]);
      end
      else begin
          for (int k = 0; k < 4; k++)
              trans.data.push_back($urandom);
      end
      for (int k = 0; k < 4; k++)
          trans.strobes[k] = 1;
      trans.set_sequencer(reg_model.soc_ifc_AXI_map.get_sequencer());

      trans.adw_valid_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
      trans.aw_valid_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
      trans.b_valid_ready_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);

      `uvm_send(trans);

      // get_response(rsp);

      if (!axi_user_used_is_valid() && retry_failed_reg_axs) begin
          if (rand_delay_en) do_rand_delay(1, data_delay);
          `uvm_info("MBOX_AXI_SEQ", "Re-do datain write with valid AxUSER", UVM_HIGH)
          reg_model.mbox_csr_rm.mbox_datain_sem.get();
          reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
          reg_model.mbox_csr_rm.mbox_datain_sem.put();
          report_reg_sts(reg_sts, "mbox_datain");
      end
      if (rand_delay_en) do_rand_delay(1, data_delay);
  end
  for (datain_ii=0; datain_ii < this.mbox_op_rand.dlen; datain_ii+=4) begin
      get_response(rsp);
  end
endtask

//==========================================
// Task:        mbox_read_resp_data
// Description: Fetch all response data from uC in a loop
//==========================================
task soc_ifc_env_mbox_rand_axi_user_axi_txn_sequence::mbox_read_resp_data();
  uvm_reg_data_t data;
  uvm_reg_data_t dlen;
  int ii;
  aaxi_master_tr trans;
  reg_model.mbox_csr_rm.mbox_dlen.read(reg_sts, dlen, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(AXI_USER_PROB_DATAOUT)));
  report_reg_sts(reg_sts, "mbox_dlen");
  if (!axi_user_used_is_valid() && retry_failed_reg_axs) begin
      reg_model.mbox_csr_rm.mbox_dlen.read(reg_sts, dlen, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
      report_reg_sts(reg_sts, "mbox_dlen");
  end
  if (dlen != mbox_resp_expected_dlen) begin
      if (this.get_type_name() inside {"soc_ifc_env_mbox_reg_axs_invalid_sequence",
                                       "soc_ifc_env_mbox_reg_axs_invalid_small_sequence",
                                       "soc_ifc_env_mbox_reg_axs_invalid_medium_sequence",
                                       "soc_ifc_env_mbox_reg_axs_invalid_large_sequence"})
          `uvm_info("MBOX_AXI_SEQ", $sformatf("SOC received response data with mbox_dlen [%0d] that does not match the expected data amount [%0d]! Not flagging err since this is an invalid reg-access sequence [%s]", dlen, mbox_resp_expected_dlen, this.get_type_name()), UVM_LOW)
      else if (saw_mbox_unlock)
          `uvm_info("MBOX_AXI_SEQ", $sformatf("SOC received response data with mbox_dlen [%0d] that does not match the expected data amount [%0d]! Not flagging err since mbox_unlock was observed", dlen, mbox_resp_expected_dlen), UVM_LOW)
      else
          `uvm_error("MBOX_AXI_SEQ", $sformatf("SOC received response data with mbox_dlen [%0d] that does not match the expected data amount [%0d]!", dlen, mbox_resp_expected_dlen))
  end
  if (rand_delay_en) do_rand_delay(1, step_delay);
  for (ii=0; ii < dlen; ii+=4) begin

      `uvm_create(trans);

      trans.kind = AAXI_READ;
      trans.vers = AAXI4;
      trans.addr = reg_model.mbox_csr_rm.mbox_dataout.get_address(reg_model.soc_ifc_AXI_map);
      trans.id = $urandom();
      trans.len = 0;
      trans.size = 2;
      trans.burst = 0;
      trans.aruser = get_rand_user(FORCE_VALID_AXI_USER).get_addr_user();
      trans.set_sequencer(reg_model.soc_ifc_AXI_map.get_sequencer());
      trans.ar_valid_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
      trans.resp_valid_ready_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);

      `uvm_send(trans);

      if (!axi_user_used_is_valid() && retry_failed_reg_axs) begin
          if (rand_delay_en) do_rand_delay(1, data_delay);
          `uvm_info("MBOX_AXI_SEQ", "Re-do dataout read with valid AxUSER", UVM_HIGH)
          reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(get_rand_user(FORCE_VALID_AXI_USER)));
          report_reg_sts(reg_sts, "mbox_dataout");
      end
      if (rand_delay_en && (ii+4) < dlen) do_rand_delay(1, data_delay);
  end
  for (ii=0; ii<dlen; ii+=4) begin
      get_response(rsp);
  end
endtask
