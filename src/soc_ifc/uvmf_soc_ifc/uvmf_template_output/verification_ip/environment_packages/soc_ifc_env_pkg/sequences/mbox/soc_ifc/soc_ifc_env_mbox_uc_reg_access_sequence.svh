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
  extern virtual task mbox_poll_status();

  int i;
  rand int num_reg;
  rand bit out_of_bounds;
  rand int slave_sel[];
  rand bit [31:0] reg_addr[];
  bit [`CALIPTRA_AHB_SLAVES_NUM-1:0][31:0] addr_min_temp = `CALIPTRA_SLAVE_BASE_ADDR;
  bit [`CALIPTRA_AHB_SLAVES_NUM-1:0][31:0] addr_max_temp = `CALIPTRA_SLAVE_MASK_ADDR;
  
  constraint out_of_bounds_c {
    out_of_bounds dist {
        1'b1 := 1,
        1'b0 := 99
    };
  }

  constraint num_reg_c { 
    out_of_bounds == 0 -> num_reg inside {[25:50]};
    out_of_bounds == 1 -> num_reg == 1;
    solve out_of_bounds before num_reg;
  }

  // This sequence only sends reg access
  constraint mbox_cmd_c { out_of_bounds == 0 -> mbox_op_rand.cmd.cmd_e == MBOX_CMD_REG_ACCESS; 
                          out_of_bounds == 1 -> mbox_op_rand.cmd.cmd_e == MBOX_CMD_OOB_ACCESS;
                          solve out_of_bounds before mbox_op_rand; }

  // setting to min dlen for a resp reqd command
  constraint mbox_dlen_c { out_of_bounds == 0 -> mbox_op_rand.dlen == (num_reg << 2); //4 bytes for each reg address
                           out_of_bounds == 1 -> mbox_op_rand.dlen == 32'h8; //min dlen for "resp req" command
                           solve out_of_bounds before mbox_op_rand;
                           solve num_reg before mbox_op_rand; }

  // pick a slave to select an address in a valid range
  constraint slave_sel_c { slave_sel.size() == num_reg;
                           foreach (slave_sel[i]) { slave_sel[i] <  `CALIPTRA_AHB_SLAVES_NUM; 
                                                    slave_sel[i] != `CALIPTRA_SLAVE_SEL_I3C;
                                                    slave_sel[i] != `CALIPTRA_SLAVE_SEL_UART;
                                                    slave_sel[i] != `CALIPTRA_SLAVE_SEL_QSPI; 
                                                    slave_sel[i] != `CALIPTRA_SLAVE_SEL_SOC_IFC;
                                                    slave_sel[i] != `CALIPTRA_SLAVE_SEL_CSRNG;
                                                    slave_sel[i] != `CALIPTRA_SLAVE_SEL_ENTROPY_SRC; }
                           solve num_reg before slave_sel;
  }
  
  //constrain address within min/max
  //specifically disable "lock" registers so we don't accidentally acquire a lock
  constraint reg_addr_c { reg_addr.size() == num_reg;
                          foreach (reg_addr[i]) { 
                            out_of_bounds == 0 -> reg_addr[i] <= addr_max_temp[slave_sel[i]];
                            out_of_bounds == 0 -> reg_addr[i] >= addr_min_temp[slave_sel[i]];
                            out_of_bounds == 1 -> reg_addr[i] >= 32'h7000_0000;
                            out_of_bounds == 1 -> reg_addr[i] <= 32'hFFFF_FFFF;
                            reg_addr[i][1:0] == '0;
                            reg_addr[i] != `CLP_MBOX_CSR_MBOX_LOCK;
                            reg_addr[i] != `CLP_SHA512_ACC_CSR_LOCK; }
                          solve slave_sel before reg_addr;
                          solve out_of_bounds before reg_addr;
                          solve num_reg before reg_addr;
                          }

  function void post_randomize();
    for (int i = 0; i < num_reg; i++) begin
      `uvm_info("MBOX_SEQ", $sformatf("Constraints for reg access [%x] - out_of_bounds: [%x] slave_sel: [%x] reg_addr: [%x]", i, out_of_bounds, slave_sel[i], reg_addr[i]), UVM_MEDIUM)
    end
  endfunction
  
endclass

// This should be overridden with real data to write
task soc_ifc_env_mbox_uc_reg_access_sequence::mbox_push_datain();

    uvm_reg_data_t data;
    for (int i = 0; i < num_reg; i++) begin
      data = uvm_reg_data_t'(reg_addr[i]);
      reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_DATAIN)));
      report_reg_sts(reg_sts, "mbox_datain");
    end

endtask

task soc_ifc_env_mbox_uc_reg_access_sequence::mbox_poll_status();
  mbox_status_e data;
  mbox_fsm_state_e state;

  // A force-unlock would cause state->MBOX_IDLE, so we exit the polling loop
  do begin
      configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(200);
      mbox_check_status(data, state);
  end while (data == CMD_BUSY && state != MBOX_IDLE);

  if (state == MBOX_IDLE) begin
        `uvm_info("MBOX_SEQ", "Detected mailbox state transition to IDLE - was mbox_unlock expected?", UVM_HIGH)
  end
  else if (data == DATA_READY) begin
      if (mbox_resp_expected_dlen == 0)
          `uvm_error("MBOX_SEQ", $sformatf("Received status %p when not expecting any bytes of response data!", data))
      else begin
          mbox_read_resp_data();
      end
  end
  else if (data == CMD_FAILURE) begin
      if (mbox_op_rand.cmd.cmd_e == MBOX_CMD_OOB_ACCESS) begin
        //This was expected, move on
      end else begin
        `uvm_error("MBOX_SEQ", $sformatf("Received unexpected mailbox status %p", data))
      end
  end
  else if (data == CMD_COMPLETE) begin
      if (mbox_resp_expected_dlen != 0)
          `uvm_error("MBOX_SEQ", $sformatf("Received status %p when expecting 0x%x bytes of response data!", data, mbox_resp_expected_dlen))
  end
  else begin
      `uvm_error("MBOX_SEQ", $sformatf("Received unexpected mailbox status %p", data))
  end
endtask
