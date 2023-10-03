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

// Reg predictions that will be scheduled on AHB write to internal_fw_update_reset
class soc_ifc_reg_delay_job_soc_ifc_reg_internal_fw_update_reset_core_rst extends soc_ifc_reg_delay_job;
    `uvm_object_utils( soc_ifc_reg_delay_job_soc_ifc_reg_internal_fw_update_reset_core_rst )
    soc_ifc_reg_ext rm; /* soc_ifc_reg_rm */
    uvm_reg_block rm_top;
    uvm_reg_map map;
    bit iccm_unlock = 1'b0;
    bit fsm_done_to_rst = 1'b0;
    bit fsm_rst_to_wait = 1'b0;
    bit fsm_wait_to_done = 1'b0;

    virtual task do_job();
        `uvm_info("SOC_IFC_REG_DELAY_JOB", "Running delayed job for soc_ifc_reg.internal_fw_update_reset.core_rst", UVM_LOW)
        rm_top = rm.get_parent();
        `uvm_info("SOC_IFC_REG_CBS", $sformatf("iccm_lock value 0x%x, boot FSM tracker: [%p]", rm.internal_iccm_lock.lock.get_mirrored_value(), rm.boot_fn_state_sigs), UVM_LOW)
        if (fsm_done_to_rst) begin
            rm.boot_fn_state_sigs = '{boot_fw_rst: 1'b1, default: 1'b0};
            `uvm_info("SOC_IFC_REG_CBS", $sformatf("iccm_lock value 0x%x, boot FSM tracker: [%p]", rm.internal_iccm_lock.lock.get_mirrored_value(), rm.boot_fn_state_sigs), UVM_LOW)
        end
        else if (fsm_rst_to_wait && rm.boot_fn_state_sigs.boot_fw_rst) begin
            rm.boot_fn_state_sigs = '{boot_wait: 1'b1, default: 1'b0};
            `uvm_info("SOC_IFC_REG_CBS", $sformatf("iccm_lock value 0x%x, boot FSM tracker: [%p]", rm.internal_iccm_lock.lock.get_mirrored_value(), rm.boot_fn_state_sigs), UVM_LOW)
            // This delay job should also trigger the assertion of uC reset in the predictor
        end
        else if (fsm_wait_to_done && rm.boot_fn_state_sigs.boot_wait) begin
            rm.boot_fn_state_sigs = '{boot_done: 1'b1, default: 1'b0};
            `uvm_info("SOC_IFC_REG_CBS", $sformatf("iccm_lock value 0x%x, boot FSM tracker: [%p]", rm.internal_iccm_lock.lock.get_mirrored_value(), rm.boot_fn_state_sigs), UVM_LOW)
            // This delay job should also trigger the de-assertion of fw_update_rst_window in the predictor
        end
        else if (iccm_unlock && rm.boot_fn_state_sigs.boot_done) begin
            rm.internal_iccm_lock.lock.predict(uvm_reg_data_t'(0));
            `uvm_info("SOC_IFC_REG_CBS", $sformatf("iccm_lock value 0x%x, boot FSM tracker: [%p]", rm.internal_iccm_lock.lock.get_mirrored_value(), rm.boot_fn_state_sigs), UVM_LOW)
            // This delay job should also trigger the de-assertion of iccm_lock in the predictor
        end
        else if (rm.boot_fn_state_sigs.boot_done) begin
            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Delay job should trigger uC reset deassertion. iccm_lock value 0x%x, boot FSM tracker: [%p]", rm.internal_iccm_lock.lock.get_mirrored_value(), rm.boot_fn_state_sigs), UVM_LOW)
            // This delay job should also trigger the de-assertion of uC reset in the predictor
        end
        else begin
            `uvm_error("SOC_IFC_REG_CBS",
                       $sformatf("Delay job for internal_fw_update_reset_core_rst ran with unexpected options and Boot FSM state! options: [iccm:%0x fwrst:%0x wait:%0x done:%0x] iccm_lock value 0x%x, boot FSM tracker: [%p]",
                                 iccm_unlock     ,
                                 fsm_done_to_rst ,
                                 fsm_rst_to_wait ,
                                 fsm_wait_to_done,
                                 rm.internal_iccm_lock.lock.get_mirrored_value(),
                                 rm.boot_fn_state_sigs))
        end
    endtask
endclass

// Callback for fw update reset register
class soc_ifc_reg_cbs_soc_ifc_reg_internal_fw_update_reset extends soc_ifc_reg_cbs_soc_ifc_reg_internal;

    `uvm_object_utils(soc_ifc_reg_cbs_soc_ifc_reg_internal_fw_update_reset)

    string AHB_map_name = "soc_ifc_AHB_map";
    string APB_map_name = "soc_ifc_APB_map";

    // Function: post_predict
    //
    // Called by the <uvm_reg_field::predict()> method
    // after a successful UVM_PREDICT_READ or UVM_PREDICT_WRITE prediction.
    //
    // ~previous~ is the previous value in the mirror and
    // ~value~ is the latest predicted value. Any change to ~value~ will
    // modify the predicted mirror value.
    //
    virtual function void post_predict(input uvm_reg_field  fld,
                                       input uvm_reg_data_t previous,
                                       inout uvm_reg_data_t value,
                                       input uvm_predict_e  kind,
                                       input uvm_path_e     path,
                                       input uvm_reg_map    map);

        soc_ifc_reg_delay_job_soc_ifc_reg_internal_fw_update_reset_core_rst delay_job_boot_fsm_fwrst;
        soc_ifc_reg_delay_job_soc_ifc_reg_internal_fw_update_reset_core_rst delay_job_boot_fsm_wait;
        soc_ifc_reg_delay_job_soc_ifc_reg_internal_fw_update_reset_core_rst delay_job_rst_window;
        soc_ifc_reg_delay_job_soc_ifc_reg_internal_fw_update_reset_core_rst delay_job_iccm_unlock;
        soc_ifc_reg_delay_job_soc_ifc_reg_internal_fw_update_reset_core_rst delay_job_uc_rst;
        soc_ifc_reg_ext rm; /* soc_ifc_reg_rm */
        uvm_reg_block blk = fld.get_parent().get_parent(); /* soc_ifc_reg_rm */
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")

        delay_job_boot_fsm_fwrst = soc_ifc_reg_delay_job_soc_ifc_reg_internal_fw_update_reset_core_rst::type_id::create("delay_job_boot_fsm_fwrst");
        delay_job_boot_fsm_fwrst.rm = rm;
        delay_job_boot_fsm_fwrst.map = map;
        delay_job_boot_fsm_fwrst.fsm_done_to_rst = 1;
        delay_job_boot_fsm_fwrst.set_delay_cycles(0); // transition to state boot_fw_rst occurs 1 clock after the reg write

        delay_job_boot_fsm_wait = soc_ifc_reg_delay_job_soc_ifc_reg_internal_fw_update_reset_core_rst::type_id::create("delay_job_boot_fsm_wait");
        delay_job_boot_fsm_wait.rm = rm;
        delay_job_boot_fsm_wait.map = map;
        delay_job_boot_fsm_wait.fsm_rst_to_wait = 1;
        delay_job_boot_fsm_wait.set_delay_cycles(delay_job_boot_fsm_fwrst.get_delay_cycles() + 2); //transition to state boot_wait (and uC reset assertion) occurs 2 clocks after the boot_fw_rst state

        delay_job_rst_window = soc_ifc_reg_delay_job_soc_ifc_reg_internal_fw_update_reset_core_rst::type_id::create("delay_job_rst_window");
        delay_job_rst_window.rm = rm;
        delay_job_rst_window.map = map;
        delay_job_rst_window.fsm_wait_to_done = 1;
        delay_job_rst_window.set_delay_cycles(delay_job_boot_fsm_wait.get_delay_cycles()+1+rm.internal_fw_update_reset_wait_cycles.wait_cycles.get_mirrored_value()); //calculate total delay until transition to state boot_done and deassertion of fw_update_rst_window

        delay_job_iccm_unlock = soc_ifc_reg_delay_job_soc_ifc_reg_internal_fw_update_reset_core_rst::type_id::create("delay_job_iccm_unlock");
        delay_job_iccm_unlock.rm = rm;
        delay_job_iccm_unlock.map = map;
        delay_job_iccm_unlock.iccm_unlock = 1;
        delay_job_iccm_unlock.set_delay_cycles(delay_job_rst_window.get_delay_cycles()+1); //this iccm unlock comes 1 clock after state transition

        delay_job_uc_rst = soc_ifc_reg_delay_job_soc_ifc_reg_internal_fw_update_reset_core_rst::type_id::create("delay_job_uc_rst");
        delay_job_uc_rst.rm = rm;
        delay_job_uc_rst.map = map;
        delay_job_uc_rst.set_delay_cycles(delay_job_iccm_unlock.get_delay_cycles()+1); // Deassertion of uC reset is the last event triggered by this reg access

        if (map.get_name() == this.AHB_map_name) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    if (value & !previous) begin
                        //push a job to catch transition to boot_fw_rst state 1 clock later
                        delay_jobs.push_back(delay_job_boot_fsm_fwrst);
                        //push a job to catch transition to boot_wait state and assertion of uC reset 1 clock later
                        delay_jobs.push_back(delay_job_boot_fsm_wait);
                        //push another job to catch de-assertion of fw_update_rst_window on state transition to boot_done
                        delay_jobs.push_back(delay_job_rst_window);
                        //push a delayed job for de-assertion of iccm lock 1 clock later
                        delay_jobs.push_back(delay_job_iccm_unlock);
                        //push another job to catch de-assertion of reset 1 clock later
                        delay_jobs.push_back(delay_job_uc_rst);
                        `uvm_info("SOC_IFC_REG_CBS",
                                  $sformatf("Sending 5 delay jobs for internal register field %s with clk delays: [%0d] [%0d] [%0d] [%0d] [%0d]",
                                            fld.get_full_name(),
                                            delay_job_boot_fsm_fwrst.get_delay_cycles(),
                                            delay_job_boot_fsm_wait.get_delay_cycles(),
                                            delay_job_rst_window.get_delay_cycles(),
                                            delay_job_iccm_unlock.get_delay_cycles(),
                                            delay_job_uc_rst.get_delay_cycles()),
                                  UVM_LOW)
                    end else begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] on map [%s] has no effect on internal register field %s", kind, map.get_name(), fld.get_full_name()), UVM_FULL)
                    end
                end
                default: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] on map [%s] has no effect on internal register field %s", kind, map.get_name(), fld.get_full_name()), UVM_FULL)
        
                end
            endcase
        end
        else if (map.get_name() == this.APB_map_name) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict blocked write attempt to internal reg field %s on map %s. value: 0x%x previous: 0x%x", fld.get_full_name(), map.get_name(), value, previous), UVM_LOW)
                    value = previous;
                end
                default: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] on map [%s] has no effect on internal register field %s. value: 0x%x previous: 0x%x", kind, map.get_name(), fld.get_full_name(), value, previous), UVM_FULL)
                end
            endcase
        end
        else begin
            `uvm_error("SOC_IFC_REG_CBS", {"post_predict called through unsupported reg map! ", map.get_name()})
        end
    endfunction

endclass
