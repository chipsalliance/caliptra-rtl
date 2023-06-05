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

// Reg predictions that will be scheduled on AHB write to mbox_dlen
class soc_ifc_reg_delay_job_mbox_csr_mbox_dlen_length extends soc_ifc_reg_delay_job;
    `uvm_object_utils( soc_ifc_reg_delay_job_mbox_csr_mbox_dlen_length )
    mbox_csr_ext rm; /* mbox_csr_rm */
    mbox_fsm_state_e state_nxt;
    uvm_reg_map map;
    virtual task do_job();
        `uvm_info("SOC_IFC_REG_DELAY_JOB", "Running delayed job for mbox_csr.mbox_dlen.length", UVM_HIGH)
        // Check mbox_unlock before predicting FSM change, since a force unlock
        // has priority over normal flow
        if (rm.mbox_lock.lock.get_mirrored_value() && !rm.mbox_unlock.unlock.get_mirrored_value() && rm.mbox_status.mbox_fsm_ps.get_mirrored_value() == MBOX_RDY_FOR_DLEN) begin
            rm.mbox_status.mbox_fsm_ps.predict(state_nxt, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
            `uvm_info("SOC_IFC_REG_DELAY_JOB", $sformatf("post_predict called through map [%p] on mbox_dlen results in state transition. Functional state tracker: [%p] mbox_fsm_ps transition [%p]", map.get_name(), rm.mbox_fn_state_sigs, state_nxt), UVM_FULL)
        end
    endtask
endclass

class soc_ifc_reg_cbs_mbox_csr_mbox_dlen_length extends soc_ifc_reg_cbs_mbox_csr;

    `uvm_object_utils(soc_ifc_reg_cbs_mbox_csr_mbox_dlen_length)

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
        soc_ifc_reg_delay_job_mbox_csr_mbox_dlen_length delay_job;
        soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error  error_job;
        uvm_reg_block blk = fld.get_parent().get_parent(); /* mbox_csr_rm */
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")
        delay_job = soc_ifc_reg_delay_job_mbox_csr_mbox_dlen_length::type_id::create("delay_job");
        delay_job.rm = rm;
        delay_job.map = map;
        delay_job.set_delay_cycles(0);
        if (map.get_name() == this.AHB_map_name) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    if (rm.mbox_fn_state_sigs.uc_send_stage) begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Predicting mbox_fsm_ps transition to [%p] on write to mbox_dlen", MBOX_RDY_FOR_DATA), UVM_HIGH)
                        delay_job.state_nxt = MBOX_RDY_FOR_DATA;
                        delay_jobs.push_back(delay_job);
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_dlen on map [%s] with value [%x] predicts a state change. Delay job is queued to update DUT model.", map.get_name(), value), UVM_HIGH)
                    end
                    // uC updates mbox_dlen to reflect size of response data
                    else if (rm.mbox_fn_state_sigs.uc_receive_stage) begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_dlen (to update size of response data) in state [%p] has no impact on system state", rm.mbox_fn_state_sigs), UVM_MEDIUM)
                    end
                    else begin
                        `uvm_warning("SOC_IFC_REG_CBS", $sformatf("DLEN written during unexpected mailbox state [%p]!", rm.mbox_fn_state_sigs))
                    end
                end
                default: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] has no effect", kind), UVM_FULL)
                end
            endcase
        end
        else if (map.get_name() == this.APB_map_name) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    if (rm.mbox_fn_state_sigs.soc_send_stage && (rm.mbox_status.mbox_fsm_ps.get_mirrored_value() == MBOX_RDY_FOR_DLEN)) begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Predicting mbox_fsm_ps transition to [%p] on write to mbox_dlen", MBOX_RDY_FOR_DATA), UVM_HIGH)
                        delay_job.state_nxt = MBOX_RDY_FOR_DATA;
                        delay_jobs.push_back(delay_job);
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_dlen on map [%s] with value [%x] predicts a state change. Delay job is queued to update DUT model.", map.get_name(), value), UVM_HIGH)
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
                        `uvm_warning("SOC_IFC_REG_CBS", $sformatf("DLEN written during unexpected mailbox state [%p]!", rm.mbox_fn_state_sigs))
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
                        `uvm_warning("SOC_IFC_REG_CBS", $sformatf("DLEN written during unexpected mailbox state [%p]!", rm.mbox_fn_state_sigs))
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
