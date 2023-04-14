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
//              functionality in a test that sends medium-sized mailbox commands.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_rand_medium_interference_sequence extends soc_ifc_env_mbox_rand_medium_sequence;

  `uvm_object_utils( soc_ifc_env_mbox_rand_medium_interference_sequence )

  extern virtual task mbox_poll_status();

  rand uvm_reg_data_t data;
  rand int reg_select;
  rand apb3_rw_e RnW;
  rand byte unsigned xfers;
  rand byte unsigned cycles;

endclass

task soc_ifc_env_mbox_rand_medium_interference_sequence::mbox_poll_status();
    mbox_status_e sts;
    uvm_reg regs[$];
    byte unsigned ii;

    reg_model.soc_ifc_APB_map.get_registers(regs, UVM_HIER);

    // If we read status immediately, the mbox_fsm_ps will not have transitioned
    // yet and will predict the prior value in the reg-model, missing the transition.
    // This affects valid_requester/valid_receiver logic in soc_ifc_predictor,
    // which results in false error reporting.
    // Maybe we need a better way to predict mbox_fsm_ps field changes?
    do begin
        if(!this.randomize(xfers) with {xfers inside {[1:20]}; }) begin
            `uvm_error("MBOX_SEQ", "Failed to randomize APB reg transfer count in mbox_poll_status")
        end
        else begin
            for (ii=0; ii<xfers; ii++) begin: XFER_LOOP
                // Do random access to mailbox to trigger arb logic as cptra sequence reads command data
                // and writes response data
                // TODO also mix in some reg writes?
                if(!this.randomize(RnW, reg_select, data, cycles) with {RnW == APB3_TRANS_READ;
                                                                        reg_select < regs.size();
                                                                        cycles inside {[1:200]}; }) begin
                    `uvm_error("MBOX_SEQ", "Failed to randomize memory APB transfer in mbox_wait_for_command")
                end
                else begin
                    if (RnW == APB3_TRANS_READ) regs[reg_select].read (reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_STATUS)));
                    else                        regs[reg_select].write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_STATUS)));
                end
            end
        end
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(cycles);
        mbox_check_status(sts);
    end while (sts == CMD_BUSY);

    if (sts == DATA_READY) begin
        if (mbox_resp_expected_dlen == 0)
            `uvm_error("MBOX_SEQ", $sformatf("Received status %p when not expecting any bytes of response data!", sts))
        else begin
            mbox_read_resp_data();
        end
    end
    else if (sts == CMD_FAILURE) begin
        `uvm_error("MBOX_SEQ", $sformatf("Received unexpected mailbox status %p", sts))
    end
    else if (sts == CMD_COMPLETE) begin
        if (mbox_resp_expected_dlen != 0)
            `uvm_error("MBOX_SEQ", $sformatf("Received status %p when expecting 0x%x bytes of response data!", sts, mbox_resp_expected_dlen))
    end
    else begin
        `uvm_error("MBOX_SEQ", $sformatf("Received unexpected mailbox status %p", sts))
    end
endtask
