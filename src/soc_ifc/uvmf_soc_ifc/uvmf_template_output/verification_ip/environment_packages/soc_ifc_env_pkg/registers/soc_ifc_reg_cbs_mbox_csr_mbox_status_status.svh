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

// Reg predictions that will be scheduled on AHB write to mbox_status
class soc_ifc_reg_delay_job_mbox_csr_mbox_status_status extends soc_ifc_reg_delay_job;
    `uvm_object_utils( soc_ifc_reg_delay_job_mbox_csr_mbox_status_status )
    mbox_csr_ext rm; /* mbox_csr_rm */
    mbox_fsm_state_e state_nxt;
    uvm_reg_map map;
    virtual task do_job();
        `uvm_info("SOC_IFC_REG_DELAY_JOB", "Running delayed job for mbox_csr.mbox_status.status", UVM_HIGH)
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
        if (rm.mbox_fn_state_sigs.mbox_error) begin
            // NOTE: This is due to a logic bug in mbox.sv. Regular state transitions
            //       take priority over error state transitions, so if an arc_..._ERROR state
            //       goes high at the same time as that state's normal arc_<next_state> signal,
            //       RTL won't go to the ERROR state as predicted.
            //       Flag this as an error here, that will cause regression failures until fixed.
            `uvm_error("SOC_IFC_REG_DELAY_JOB", $sformatf("While running [%s] (scheduled due to access against mbox_status on map [%p]), functional state value detected as: %p. Skipping delay job state transitions. This is a known RTL bug in mbox.sv", this.get_type_name(), map.get_name(), rm.mbox_fn_state_sigs))
        end
        else if (rm.mbox_lock.lock.get_mirrored_value()) begin
            rm.mbox_status.mbox_fsm_ps.predict(state_nxt, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
            if (state_nxt == MBOX_EXECUTE_SOC) begin
                rm.mbox_fn_state_sigs = '{soc_done_stage: 1'b1, default: 1'b0};
            end
            else if (state_nxt == MBOX_EXECUTE_UC) begin
                rm.mbox_fn_state_sigs = '{uc_done_stage: 1'b1, default: 1'b0};
            end
            `uvm_info("SOC_IFC_REG_DELAY_JOB", $sformatf("post_predict called through map [%p] on mbox_status results in state transition. Functional state tracker: %p", map.get_name(), rm.mbox_fn_state_sigs), UVM_FULL)
        end
    endtask
endclass

class soc_ifc_reg_cbs_mbox_csr_mbox_status_status extends soc_ifc_reg_cbs_mbox_csr;

    `uvm_object_utils(soc_ifc_reg_cbs_mbox_csr_mbox_status_status)

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
        soc_ifc_reg_delay_job_mbox_csr_mbox_status_status delay_job;
        soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error error_job;
        mbox_csr_ext rm; /* mbox_csr_rm */
        uvm_mem mm; /* mbox_mem_rm "mem model" */
        uvm_reg_block blk = fld.get_parent().get_parent(); /* mbox_csr_rm */
        mm = blk.get_parent().get_mem_by_name("mbox_mem_rm");
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")
        delay_job = soc_ifc_reg_delay_job_mbox_csr_mbox_status_status::type_id::create("delay_job");
        delay_job.rm = rm;
        delay_job.map = map;
        delay_job.set_delay_cycles(0);
        if (map.get_name() == this.AHB_map_name) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    if (rm.mbox_fn_state_sigs.uc_receive_stage &&
                        mbox_status_e'(value) != mbox_status_e'(previous) &&
                        mbox_status_e'(value) != CMD_BUSY) begin
                        if (!rm.mbox_status.soc_has_lock.get_mirrored_value()) begin
                            `uvm_warning("SOC_IFC_REG_CBS", $sformatf("Write to mbox_status in state [%p] on map [%s] is unexpected!", rm.mbox_fn_state_sigs, map.get_name()))
                        end
                        else begin
                            // Maximum allowable size for data transferred via mailbox
                            int unsigned dlen_cap_dw = (mbox_status_e'(value) != DATA_READY)                         ? 0 : /* ignore DLEN if the uC is not sending response data to SOC */
                                                       (mbox_dlen_mirrored(rm) < (mm.get_size() * mm.get_n_bytes())) ? mbox_dlen_mirrored_dword_ceil(rm) :
                                                                                                                       (mm.get_size() * mm.get_n_bytes()) >> ($clog2(MBOX_DATA_W/8));
                            if (rm.mbox_data_q.size() > 0) begin
                                `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_status transfers control back to SOC, but mbox_data_q is not empty! Size: %0d", rm.mbox_data_q.size()), UVM_LOW) /* TODO: Make a warning that can be disabled for DLEN violation cases? */
                                rm.mbox_data_q.delete();
                            end
                            //Pre populated dataout with the first entry of the resp q
                            rm.mbox_datain_to_dataout_predict.trigger();
                            rm.mbox_dataout.dataout.predict(rm.mbox_resp_q[0], .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
                            rm.mbox_datain_to_dataout_predict.reset();
                            //move resp q to data q
                            rm.mbox_data_q = rm.mbox_resp_q;
                            rm.mbox_resp_q.delete();
                            // On transfer of control, remove extraneous entries from data_q since
                            // reads of these values will be gated for the receiver
                            // in the DUT
                            if (rm.mbox_data_q.size > dlen_cap_dw) begin
                                `uvm_info("SOC_IFC_REG_CBS", $sformatf("Extra entries detected in mbox_data_q on control transfer - deleting %d entries", rm.mbox_data_q.size() - dlen_cap_dw), UVM_LOW)
                                while (rm.mbox_data_q.size > dlen_cap_dw) begin
                                    // Continuously remove last entry until size is equal to dlen, since entries are added with push_back
                                    rm.mbox_data_q.delete(rm.mbox_data_q.size()-1);
                                end
                            end
                            else if (rm.mbox_data_q.size < dlen_cap_dw) begin
                                uvm_reg_data_t zeros [$];
                                `uvm_info("SOC_IFC_REG_CBS", $sformatf("Insufficient entries detected in mbox_data_q on control transfer - 0-filling %d entries", dlen_cap_dw - rm.mbox_data_q.size()), UVM_LOW)
                                zeros = '{MBOX_DEPTH{32'h0}};
                                zeros = zeros[0:dlen_cap_dw - rm.mbox_data_q.size() - 1];
                                rm.mbox_data_q = {rm.mbox_data_q, zeros};
                            end
                            delay_job.state_nxt = MBOX_EXECUTE_SOC;
                            delay_jobs.push_back(delay_job);
                            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_status on map [%s] with value [%x] predicts a state change. Delay job is queued to update DUT model.", map.get_name(), value), UVM_HIGH)
                        end
                    end
                    else begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_status on map [%s] with value [%x] during state [%p] does not update the status field (previous value [%x]), so no state change is predicted", map.get_name(), mbox_status_e'(value), rm.mbox_fn_state_sigs, mbox_status_e'(previous)), UVM_MEDIUM)
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
                    if (rm.mbox_fn_state_sigs.soc_receive_stage &&
                        mbox_status_e'(value) != mbox_status_e'(previous) &&
                        mbox_status_e'(value) != CMD_BUSY) begin
                        if (rm.mbox_status.soc_has_lock.get_mirrored_value()) begin
                            `uvm_warning("SOC_IFC_REG_CBS", $sformatf("Write to mbox_status in state [%p] on map [%s] is unexpected! soc_has_lock is %x", rm.mbox_fn_state_sigs, map.get_name(), rm.mbox_status.soc_has_lock.get_mirrored_value()))
                        end
                        else begin
                            if (rm.mbox_data_q.size() > 0) begin
                                `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_status transfers control back to uC, but mbox_data_q is not empty! Size: %0d", rm.mbox_data_q.size()), UVM_LOW) /* TODO: Make a warning that can be disabled for DLEN violation cases? */
                            end
                            if (rm.mbox_resp_q.size() > 0) begin
                                `uvm_warning("SOC_IFC_REG_CBS", $sformatf("Write to mbox_status transfers control back to uC, but mbox_resp_q is not empty! Size: %0d", rm.mbox_resp_q.size()))
                            end
                            rm.mbox_data_q.delete();
                            rm.mbox_resp_q.delete();
                            delay_job.state_nxt = MBOX_EXECUTE_UC;
                            delay_jobs.push_back(delay_job);
                            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_status on map [%s] with value [%x] predicts a state change. Delay job is queued to update DUT model.", map.get_name(), value), UVM_HIGH)
                        end
                    end
                    // Check for protocol violations
                    if (rm.mbox_fn_state_sigs.mbox_idle) begin
                        error_job = soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error::type_id::create("error_job");
                        error_job.rm = rm;
                        error_job.map = map;
                        error_job.fld = fld;
                        error_job.set_delay_cycles(0);
                        error_job.state_nxt = MBOX_IDLE;
                        error_job.error = '{axs_without_lock: 1'b1, default: 1'b0};
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to %s on map [%s] with value [%x] causes a mbox no_lock protocol violation. Delay job is queued to update DUT model.", fld.get_name(), map.get_name(), value), UVM_HIGH)
                        delay_jobs.push_back(error_job);
                    end
                    else if (rm.mbox_fn_state_sigs.mbox_error) begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to %s on map [%s] with value [%x] during mailbox state [%p] has no additional side effects!", fld.get_name(), map.get_name(), value, rm.mbox_fn_state_sigs), UVM_LOW)
                    end
                    else if (!rm.mbox_fn_state_sigs.soc_receive_stage) begin
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
