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

class soc_ifc_reg_cbs_mbox_csr_mbox_dataout_dataout extends soc_ifc_reg_cbs_mbox_csr;

    `uvm_object_utils(soc_ifc_reg_cbs_mbox_csr_mbox_dataout_dataout)

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
        soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error  error_job;
        mbox_csr_ext rm; /* mbox_csr_rm */
        uvm_reg_block blk = fld.get_parent().get_parent(); /* mbox_csr_rm */
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")
        // Flag unexpected accesses based on system state, leaving an exception
        // for UVM_PREDICT calls triggered by writes to mbox_datain
        case (map.get_name()) inside
            this.AHB_map_name: begin
                if (!rm.mbox_fn_state_sigs.uc_receive_stage &&
                    rm.mbox_datain_to_dataout_predict.is_off())
                    `uvm_error("SOC_IFC_REG_CBS", $sformatf("Access to dataout of kind [%p] is unexpected on map [%s]! Mailbox state tracker: %p", kind, map.get_name(), rm.mbox_fn_state_sigs))
            end
            this.APB_map_name: begin
                if (rm.mbox_fn_state_sigs.mbox_idle && rm.mbox_datain_to_dataout_predict.is_off()) begin
                    error_job = soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error::type_id::create("error_job");
                    error_job.rm = rm;
                    error_job.map = map;
                    error_job.fld = fld;
                    error_job.set_delay_cycles(0);
                    error_job.state_nxt = MBOX_IDLE;
                    error_job.error = '{axs_without_lock: 1'b1, default: 1'b0};
                    delay_jobs.push_back(error_job);
                end
                else if ((kind == UVM_PREDICT_WRITE) ||
                         ((!rm.mbox_fn_state_sigs.soc_receive_stage && !rm.mbox_fn_state_sigs.soc_done_stage) &&
                          rm.mbox_datain_to_dataout_predict.is_off())) begin
                    error_job = soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error::type_id::create("error_job");
                    error_job.rm = rm;
                    error_job.map = map;
                    error_job.fld = fld;
                    error_job.set_delay_cycles(0);
                    error_job.state_nxt = MBOX_ERROR;
                    error_job.error = '{axs_incorrect_order: 1'b1, default: 1'b0};
                    delay_jobs.push_back(error_job);
                    `uvm_error("SOC_IFC_REG_CBS", $sformatf("Access to dataout of kind [%p] is unexpected on map [%s]! Flagging mailbox protocol violation. Mailbox state tracker: %p", kind, map.get_name(), rm.mbox_fn_state_sigs))
                end
            end
        endcase
        // Update the data queue and modify predicted value for mbox_dataout
        if ((map.get_name() == this.AHB_map_name) ||
            (map.get_name() == this.APB_map_name)) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    if (value != previous) begin
                        `uvm_error("SOC_IFC_REG_CBS", "Writes to mbox_dataout should be dropped, but reg_predictor calculated a value change")
                        value = previous;
                    end
                end
                UVM_PREDICT_READ: begin
                    // Current entry at front of Queue should match 'previous' i.e.
                    // the mirrored value of mbox_dataout.
                    // Next entry in the queue is the predicted value for the
                    // subsequent access
                    if (rm.mbox_data_q.size() > 0) begin
                        if (previous != rm.mbox_data_q[0])
                            `uvm_error("SOC_IFC_REG_CBS", $sformatf("Current mirrored value [0x%x] in %s does not match the element at the front of the mailbox data queue [0x%x]!", previous, fld.get_full_name(), rm.mbox_data_q[0]))
                        rm.mbox_data_q.pop_front();
                        // New value (for next read) will be the next queued entry
                        // instead of the current read value
                        if (rm.mbox_data_q.size() > 0) begin
                            value = rm.mbox_data_q[0];
                        end
                        else begin
                            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Read from %s gets the last available value in the mailbox", fld.get_full_name()), UVM_HIGH)
                        end
                    end
                    else begin
                        // TODO escalate to uvm_warning?
                        // Some tests do this deliberately, we don't want those to fail
                        `uvm_info("SOC_IFC_REG_CBS", "Attempted read from mbox_dataout when mailbox_data_q is empty!", UVM_MEDIUM)
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
