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

class soc_ifc_reg_cbs_mbox_csr_mbox_datain_datain extends soc_ifc_reg_cbs_mbox_csr;

    `uvm_object_utils(soc_ifc_reg_cbs_mbox_csr_mbox_datain_datain)

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
        // Maximum allowable size for data transferred via mailbox
        int unsigned dlen_cap_dw;
        soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error  error_job;
        mbox_csr_ext rm; /* mbox_csr_rm */
        uvm_mem mm; /* mbox_mem_rm "mem model" */
        uvm_reg_block blk = fld.get_parent().get_parent(); /* mbox_csr_rm */
        mm = blk.get_parent().get_mem_by_name("mbox_mem_rm");
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")
        dlen_cap_dw = (mbox_dlen_mirrored(rm) < (mm.get_size() * mm.get_n_bytes())) ? mbox_dlen_mirrored_dword_ceil(rm) :
                                                                                      (mm.get_size() * mm.get_n_bytes()) >> ($clog2(MBOX_DATA_W/8));
        if (map.get_name() == this.AHB_map_name) begin
            case (kind) inside
                // The mailbox_data_q is reset for each new mailbox command to represent
                // desired DUT behavior.
                // Pushes are only allowed on AHB when:
                //  - uC has lock (checked in soc_ifc_predictor)
                //  - mbox state is in MBOX_RDY_FOR_DATA or EXECUTE_UC
                UVM_PREDICT_WRITE: begin
                    if (rm.mbox_fn_state_sigs.uc_data_stage) begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called through map [%s] results in data entry push to mbox_data_q", map.get_name()), UVM_FULL)
                        // A potential issue because uC should have set dlen prior to pushing data
                        if (rm.mbox_data_q.size() >= dlen_cap_dw) begin
//                            `uvm_warning("SOC_IFC_REG_CBS", "Push to datain observed when mbox_data_q already contains the same number of entries as indicated in mbox_dlen or the mailbox maximum capacity!")
                            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Push to datain observed when mbox_data_q already contains the same number of entries [%d] as indicated in mbox_dlen [%d bytes] or the mailbox maximum capacity!", rm.mbox_data_q.size(), mbox_dlen_mirrored(rm)), UVM_LOW)
                        end
                        rm.mbox_data_q.push_back(value);
                        if (rm.mbox_data_q.size() == 1) begin
                            `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called through map [%s] results in data entry updating dataout mirror", map.get_name()), UVM_FULL)
                            // Use UVM_PREDICT_READ to workaround the warning that gets thrown (on
                            // accesses while busy) when running UVM_PREDICT_DIRECT.
                            // The warning is safe to ignore because the mbox_dataout
                            // callback does post-prediction from data queue accordingly
                            rm.mbox_data_q.push_front(rm.mbox_dataout.dataout.get_mirrored_value()); /* Sacrificial entry will be immediately removed in mbox_dataout callback */
                            rm.mbox_datain_to_dataout_predict.trigger();
                            rm.mbox_dataout.dataout.predict(value, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
                            rm.mbox_datain_to_dataout_predict.reset();
                        end
                    end
                    else if (rm.mbox_fn_state_sigs.uc_receive_stage) begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called through map [%s] results in data entry push to mbox_resp_q", map.get_name()), UVM_FULL)
                        // Not necessarily an error because uC might update dlen value before updating mbox_status
                        if (rm.mbox_resp_q.size() >= dlen_cap_dw) begin
                            `uvm_info("SOC_IFC_REG_CBS", "Push to datain observed when mbox_resp_q already contains the same number of entries as indicated in mbox_dlen or the mailbox maximum capacity!", UVM_HIGH)
                        end
                        rm.mbox_resp_q.push_back(value);
                    end
                    else begin
                        `uvm_error("SOC_IFC_REG_CBS", $sformatf("Attempted push to mbox_datain in unexpected mbox FSM state: [%p]", rm.mbox_fn_state_sigs))
                    end
                end
                default: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] has no effect", kind), UVM_FULL)
                end
            endcase
        end
        else if (map.get_name() == this.APB_map_name) begin
            case (kind) inside
                // The mailbox_data_q is reset for each new mailbox command to represent
                // desired DUT behavior.
                // Pushes are only allowed on APB when:
                //  - SOC has lock (checked in soc_ifc_predictor)
                //  - mbox state is in MBOX_RDY_FOR_DATA
                //  - if mbox state is EXECUTE_SOC, pushes not allowed because there is never resp data SOC->uC
                UVM_PREDICT_WRITE: begin
                    if (rm.mbox_fn_state_sigs.soc_data_stage) begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called through map [%s] results in data entry push to mbox_data_q", map.get_name()), UVM_FULL)
                        if (rm.mbox_data_q.size() >= dlen_cap_dw) begin
                            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Push to datain observed when mbox_data_q already contains the same number of entries [%d] as indicated in mbox_dlen [%d bytes] or the mailbox maximum capacity!", rm.mbox_data_q.size(), mbox_dlen_mirrored(rm)), UVM_LOW)
                        end
                        rm.mbox_data_q.push_back(value);
                        if (rm.mbox_data_q.size() == 1) begin
                            `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called through map [%s] results in data entry updating dataout mirror", map.get_name()), UVM_FULL)
                            // Use UVM_PREDICT_READ to workaround the warning that gets thrown (on
                            // accesses while busy) when running UVM_PREDICT_DIRECT.
                            // The warning is safe to ignore because the mbox_dataout
                            // callback does post-prediction from data queue accordingly
                            rm.mbox_data_q.push_front(rm.mbox_dataout.dataout.get_mirrored_value()); /* Sacrificial entry will be immediately removed in mbox_dataout callback */
                            rm.mbox_datain_to_dataout_predict.trigger();
                            rm.mbox_dataout.dataout.predict(value, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
                            rm.mbox_datain_to_dataout_predict.reset();
                        end
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("After processing write to mbox_datain, mbox_data_q.size(): [%d]", rm.mbox_data_q.size()), UVM_DEBUG)
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
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to [%s] on map [%s] with value [%x] causes a mbox no_lock protocol error. Delay job is queued to update DUT model.", fld.get_name(), map.get_name(), value), UVM_HIGH)
                    end
                    else begin
                        mbox_fsm_state_e mbox_fsm_ps;
                        error_job = soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error::type_id::create("error_job");
                        error_job.rm = rm;
                        error_job.map = map;
                        error_job.fld = fld;
                        error_job.set_delay_cycles(0);
                        error_job.state_nxt = MBOX_ERROR;
                        error_job.error = '{axs_incorrect_order: 1'b1, default: 1'b0};
                        delay_jobs.push_back(error_job);
                        mbox_fsm_ps = mbox_fsm_state_e'(rm.mbox_status.mbox_fsm_ps.get_mirrored_value());
                        `uvm_warning("SOC_IFC_REG_CBS", $sformatf("Write to %s on map [%s] with value [%x] during unexpected mailbox state [%p] [%p] results in mbox ooo protocol error!", fld.get_name(), map.get_name(), value, rm.mbox_fn_state_sigs, mbox_fsm_ps))
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
