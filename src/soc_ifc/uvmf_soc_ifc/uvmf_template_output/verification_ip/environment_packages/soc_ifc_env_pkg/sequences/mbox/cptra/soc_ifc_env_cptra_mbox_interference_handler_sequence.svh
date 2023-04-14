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
class soc_ifc_env_cptra_mbox_interference_handler_sequence extends soc_ifc_env_cptra_mbox_handler_sequence;


  `uvm_object_utils( soc_ifc_env_cptra_mbox_interference_handler_sequence )

  extern virtual task mbox_wait_for_command(output op_sts_e op_sts);

  rand uvm_reg_data_t data;
  rand uvm_reg_addr_t mem_offset;
  rand ahb_rnw_e RnW;
  rand byte unsigned xfers;
  rand byte unsigned cycles;

endclass

task soc_ifc_env_cptra_mbox_interference_handler_sequence::mbox_wait_for_command(output op_sts_e op_sts);
    byte ii;

    op_sts = CPTRA_TIMEOUT;
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    while (!data[reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_cmd_avail_sts.get_lsb_pos()]) begin
        if(!this.randomize(xfers) with {xfers inside {[1:20]}; }) begin
            `uvm_error("MBOX_SEQ", "Failed to randomize memory AHB transfer count in mbox_wait_for_command")
        end
        else begin
            for (ii=0; ii<xfers; ii++) begin: XFER_LOOP
                // Do random access to mailbox memory to trigger arb logic as soc APB actor writes command data
                // TODO also mix in some reg accesses?
                if(!this.randomize(RnW, mem_offset, data, cycles) with {mem_offset inside {[0:reg_model.mbox_mem_rm.get_size()-1]};
                                                                        cycles inside {[1:200]}; }) begin
                    `uvm_error("MBOX_SEQ", "Failed to randomize memory AHB transfer in mbox_wait_for_command")
                end
                else begin
                    if (RnW == AHB_READ) begin
                        reg_model.mbox_mem_rm.read (reg_sts, mem_offset, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
                    end
                    else begin
                        reg_model.mbox_mem_rm.write(reg_sts, mem_offset, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
                    end
                end
            end
        end
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(cycles);
        reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    end
    data &= uvm_reg_data_t'(1) << reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_cmd_avail_sts.get_lsb_pos();
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    op_sts = CPTRA_SUCCESS;
endtask
