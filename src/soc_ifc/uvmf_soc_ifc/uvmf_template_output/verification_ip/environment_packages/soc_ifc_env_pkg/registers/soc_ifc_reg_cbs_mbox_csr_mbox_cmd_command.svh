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

// Reg predictions that will be scheduled on AHB write to mbox_cmd
class soc_ifc_reg_delay_job_mbox_csr_mbox_cmd_command extends soc_ifc_reg_delay_job;
    `uvm_object_utils( soc_ifc_reg_delay_job_mbox_csr_mbox_cmd_command )
    mbox_csr_ext rm; /* mbox_csr_rm */
    mbox_fsm_state_e state_nxt;
    uvm_reg_map map;
    virtual task do_job();
        `uvm_info("SOC_IFC_REG_DELAY_JOB", "Running delayed job for mbox_csr.mbox_cmd.command", UVM_HIGH)
        // Check mbox_unlock before predicting FSM change, since a force unlock
        // has priority over normal flow
        // mbox_unlock only 'activates' on the falling edge of the pulse; if we detect
        // that, bail out of this prediction job
        if (rm.mbox_unlock.unlock.get_mirrored_value()) begin
            uvm_wait_for_nba_region();
            if (!rm.mbox_unlock.unlock.get_mirrored_value()) begin
                return;
            end
        end
        if (rm.mbox_lock.lock.get_mirrored_value() && rm.mbox_fn_state_sigs.soc_cmd_stage) begin
            rm.mbox_status.mbox_fsm_ps.predict(state_nxt, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
            rm.mbox_fn_state_sigs = '{soc_dlen_stage: 1'b1, default: 1'b0};
            `uvm_info("SOC_IFC_REG_DELAY_JOB", $sformatf("post_predict called through map [%p] on mbox_cmd results in state transition. Functional state tracker: [%p] mbox_fsm_ps transition [%p]", map.get_name(), rm.mbox_fn_state_sigs, state_nxt), UVM_FULL)
        end
        else if (rm.mbox_lock.lock.get_mirrored_value() && rm.mbox_fn_state_sigs.uc_cmd_stage) begin
            rm.mbox_status.mbox_fsm_ps.predict(state_nxt, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
            rm.mbox_fn_state_sigs = '{uc_dlen_stage: 1'b1, default: 1'b0};
            `uvm_info("SOC_IFC_REG_DELAY_JOB", $sformatf("post_predict called through map [%p] on mbox_cmd results in state transition. Functional state tracker: [%p] mbox_fsm_ps transition [%p]", map.get_name(), rm.mbox_fn_state_sigs, state_nxt), UVM_FULL)
        end
    endtask
endclass

class soc_ifc_reg_cbs_mbox_csr_mbox_cmd_command extends soc_ifc_reg_cbs_mbox_csr;

    `uvm_object_utils(soc_ifc_reg_cbs_mbox_csr_mbox_cmd_command)

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
        mbox_csr_ext rm; /* mbox_csr_rm */
        soc_ifc_reg_delay_job_mbox_csr_mbox_cmd_command delay_job;
        soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error  error_job;
        uvm_reg_block blk = fld.get_parent().get_parent(); /* mbox_csr_rm */
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")
        if (map.get_name() == this.AHB_map_name) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    if (rm.mbox_fn_state_sigs.uc_cmd_stage) begin
                        delay_job = soc_ifc_reg_delay_job_mbox_csr_mbox_cmd_command::type_id::create("delay_job");
                        delay_job.rm = rm;
                        delay_job.map = map;
                        delay_job.set_delay_cycles(0);
                        delay_job.state_nxt = MBOX_RDY_FOR_DLEN;
                        delay_jobs.push_back(delay_job);
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to %s on map [%s] with value [%x] predicts a state change. Delay job is queued to update DUT model.", fld.get_name(), map.get_name(), value), UVM_HIGH)
                    end
//                    else if (rm.mbox_fn_state_sigs.mbox_idle) begin
//                        error_job = soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error::type_id::create("error_job");
//                        error_job.rm = rm;
//                        error_job.map = map;
//                        error_job.fld = fld;
//                        error_job.set_delay_cycles(0);
//                        error_job.state_nxt = MBOX_IDLE;
//                        error_job.error = '{axs_without_lock: 1'b1, default: 1'b0};
//                        delay_jobs.push_back(error_job);
//                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to %s on map [%s] with value [%x] causes a mbox no_lock protocol error. Delay job is queued to update DUT model.", fld.get_name(), map.get_name(), value), UVM_HIGH)
//                    end
//                    else begin
//                        error_job = soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error::type_id::create("error_job");
//                        error_job.rm = rm;
//                        error_job.map = map;
//                        error_job.fld = fld;
//                        error_job.set_delay_cycles(0);
//                        error_job.state_nxt = MBOX_ERROR;
//                        error_job.error = '{axs_incorrect_order: 1'b1, default: 1'b0};
//                        delay_jobs.push_back(error_job);
//                        `uvm_warning("SOC_IFC_REG_CBS", $sformatf("Command written during unexpected mailbox state [%p] results in mbox ooo protocol error!", rm.mbox_fn_state_sigs))
//                    end
                end
                default: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] has no effect", kind), UVM_FULL)
                end
            endcase
        end
        else if (map.get_name() == this.APB_map_name) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    if (rm.mbox_fn_state_sigs.soc_cmd_stage/* && (rm.mbox_status.mbox_fsm_ps.get_mirrored_value() == MBOX_RDY_FOR_CMD)*/) begin
                        delay_job = soc_ifc_reg_delay_job_mbox_csr_mbox_cmd_command::type_id::create("delay_job");
                        delay_job.rm = rm;
                        delay_job.map = map;
                        delay_job.set_delay_cycles(0);
                        delay_job.state_nxt = MBOX_RDY_FOR_DLEN;
                        delay_jobs.push_back(delay_job);
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to %s on map [%s] with value [%x] predicts a state change. Delay job is queued to update DUT model.", fld.get_name(), map.get_name(), value), UVM_HIGH)
                    end
                    else if (rm.mbox_fn_state_sigs.mbox_idle) begin
                        error_job = soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error::type_id::create("error_job");
                        error_job.rm = rm;
                        error_job.map = map;
                        error_job.fld = fld;
                        error_job.set_delay_cycles(0);
                        error_job.state_nxt = MBOX_IDLE;
                        error_job.error = '{axs_without_lock: 1'b1, default: 1'b0};
                        delay_jobs.push_back(error_job);
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to %s on map [%s] with value [%x] causes a mbox no_lock protocol violation. Delay job is queued to update DUT model.", fld.get_name(), map.get_name(), value), UVM_HIGH)
                    end
                    else if (rm.mbox_fn_state_sigs.mbox_error) begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to %s on map [%s] with value [%x] during mailbox state [%p] has no additional side effects!", fld.get_name(), map.get_name(), value, rm.mbox_fn_state_sigs), UVM_LOW)
                    end
                    else begin
                        error_job = soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error::type_id::create("error_job");
                        error_job.rm = rm;
                        error_job.map = map;
                        error_job.fld = fld;
                        error_job.set_delay_cycles(0);
                        error_job.state_nxt = MBOX_ERROR;
                        error_job.error = '{axs_incorrect_order: 1'b1, default: 1'b0};
                        delay_jobs.push_back(error_job);
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to %s on map [%s] with value [%x] during unexpected mailbox state [%p] results in mbox ooo protocol violation!", fld.get_name(), map.get_name(), value, rm.mbox_fn_state_sigs), UVM_LOW)
                        rm.mbox_fn_state_sigs = '{mbox_error: 1'b1, default: 1'b0};
                    end
                end
                default: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] has no effect", kind), UVM_FULL)
                end
            endcase
        end
        else begin
            `uvm_error("SOC_IFC_REG_CBS", "post_predict called through unsupported reg map!")
        end
    endfunction

endclass
