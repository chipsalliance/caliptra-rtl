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

// Reg predictions that will be scheduled on AHB write to mbox_execute
class soc_ifc_reg_delay_job_mbox_csr_mbox_execute_execute extends soc_ifc_reg_delay_job;
    `uvm_object_utils( soc_ifc_reg_delay_job_mbox_csr_mbox_execute_execute )
    mbox_csr_ext rm; /* mbox_csr_rm */
    uvm_reg_block rm_top;
    uvm_reg_field intr_fld;
    mbox_fsm_state_e state_nxt;
    uvm_reg_map map;
    virtual task do_job();
        `uvm_info("SOC_IFC_REG_DELAY_JOB", "Running delayed job for mbox_csr.mbox_execute.execute", UVM_HIGH)
        rm_top = rm.get_parent();
        intr_fld = rm_top.get_block_by_name("soc_ifc_reg_rm").get_block_by_name("intr_block_rf_ext").get_field_by_name("notif_cmd_avail_sts");
        // Check mbox_unlock before predicting FSM change, since a force unlock
        // has priority over normal flow
        if (rm.mbox_lock.lock.get_mirrored_value() && !rm.mbox_unlock.unlock.get_mirrored_value()) begin
            rm.mbox_status.mbox_fsm_ps.predict(state_nxt, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
            case (state_nxt) inside
                MBOX_IDLE: begin
                    rm.mbox_fn_state_sigs = '{mbox_idle: 1'b1, default: 1'b0};
                    rm.mbox_status.soc_has_lock.predict(1'b0, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called through map [%p] on mbox_execute results in state transition. Functional state tracker: [%p] mbox_fsm_ps transition [%p]", map.get_name(), rm.mbox_fn_state_sigs, state_nxt), UVM_FULL)
                    if (rm.mbox_lock.is_busy()) begin
                        `uvm_info("SOC_IFC_REG_DELAY_JOB", "Delay job for mbox_execute attempted to clear mbox_lock, but hit access collision! Flagging clear event in reg-model for mbox_lock callback to handle", UVM_LOW)
                        rm.mbox_lock_clr_miss.trigger(null);
                        uvm_wait_for_nba_region();
                        // If the bus transfer is still in progress (it didn't terminate on the same
                        // falling clock edge as when this delay job was run), then just override the 
                        // mirrored value immediately. Clear is_busy to avoid a UVM_WARNING.
                        // This use-case is definitely a hack, but it is necessary to synchronize
                        // the mbox_lock mirror with the design, chronologically.
                        if (rm.mbox_lock.is_busy()) begin
                            rm.mbox_lock.Xset_busyX(0);
                            rm.mbox_lock.lock.predict(0);
                            rm.mbox_lock.Xset_busyX(1);
                        end
                        else begin
                            fork
                                begin
                                    rm.mbox_lock_clr_miss.wait_off();
                                    disable MBOX_CLR_TIMEOUT;
                                end
                                begin: MBOX_CLR_TIMEOUT
                                    // If it takes any amount of time for the pending lock to be cleared, that
                                    // means we've encountered some environment bug (since the accessing i/f
                                    // completed it's transfer, the reg prediction should be instantaneous)
                                    uvm_wait_for_nba_region();
                                    `uvm_error("SOC_IFC_REG_DELAY_JOB", $sformatf("mbox_lock clear activity, originally requested by mbox_execute callback but unserviceable, was scheduled to be completed during mbox_lock callback but took longer than expected to finish!"))
                                end
                            join_any
                        end
                    end
                    else begin
                        rm.mbox_lock.lock.predict(0);
                    end
                end
                MBOX_EXECUTE_SOC: begin
                    rm.mbox_fn_state_sigs = '{soc_receive_stage: 1'b1, default: 1'b0};
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called through map [%p] on mbox_execute results in state transition. Functional state tracker: [%p] mbox_fsm_ps transition [%p]", map.get_name(), rm.mbox_fn_state_sigs, state_nxt), UVM_FULL)
                end
                MBOX_EXECUTE_UC: begin
                    rm.mbox_fn_state_sigs = '{uc_receive_stage: 1'b1, default: 1'b0};
                    // Predict intr sts register is set
                    //  - Use UVM_PREDICT_READ kind so that all the callbacks associated with
                    //    notif_cmd_avail_sts are also called to detect interrupt pin assertion
                    //  - Use UVM_PREDICT_READ instead of UVM_PREDICT_WRITE so that
                    //    "do_predict" bypasses the access-check and does not enforce W1C
                    //    behavior on this attempt to set interrupt status to 1
                    intr_fld.predict(1'b1, -1, UVM_PREDICT_READ, UVM_PREDICT, rm_top.get_map_by_name("soc_ifc_AHB_map")); /* Intr reg access expected only via AHB i/f */
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called through map [%p] on mbox_execute results in state transition. Functional state tracker: [%p] mbox_fsm_ps transition [%p]", map.get_name(), rm.mbox_fn_state_sigs, state_nxt), UVM_FULL)
                end
                default: begin
                    `uvm_warning("SOC_IFC_REG_CBS", $sformatf("post_predict called through map [%p] on mbox_execute results in unexpected state transition. Functional state tracker: [%p] mbox_fsm_ps transition [%p]", map.get_name(), rm.mbox_fn_state_sigs, state_nxt))
                end
            endcase
            `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called through map [%p] on mbox_execute finished processing", map.get_name()), UVM_FULL)
        end
        else begin
            `uvm_info("SOC_IFC_REG_CBS",
                      $sformatf("Delay job for mbox_execute does not predict any changes due to: mbox_lock mirror [%d] mbox_unlock mirror [%d] mbox_fsm_ps [%p]",
                                rm.mbox_lock.lock.get_mirrored_value(),
                                rm.mbox_unlock.unlock.get_mirrored_value(),
                                rm.mbox_status.mbox_fsm_ps.get_mirrored_value()),
                      UVM_LOW)
        end
    endtask
endclass

class soc_ifc_reg_cbs_mbox_csr_mbox_execute_execute extends soc_ifc_reg_cbs_mbox_csr;

    `uvm_object_utils(soc_ifc_reg_cbs_mbox_csr_mbox_execute_execute)

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
        soc_ifc_reg_delay_job_mbox_csr_mbox_execute_execute delay_job;
        uvm_queue #(soc_ifc_reg_delay_job) delay_jobs;
        mbox_csr_ext rm; /* mbox_csr_rm */
        uvm_mem mm; /* mbox_mem_rm "mem model" */
        uvm_reg_block rm_top;
        uvm_reg_block blk = fld.get_parent().get_parent(); /* mbox_csr_rm */
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")
        rm_top = rm.get_parent();
        mm = rm_top.get_mem_by_name("mbox_mem_rm");
        delay_job = soc_ifc_reg_delay_job_mbox_csr_mbox_execute_execute::type_id::create("delay_job");
        delay_job.rm = rm;
        delay_job.map = map;
        delay_job.set_delay_cycles(0);
        if (!uvm_config_db#(uvm_queue#(soc_ifc_reg_delay_job))::get(null, "soc_ifc_reg_model_top", "delay_jobs", delay_jobs))
            `uvm_error("SOC_IFC_REG_CBS", "Failed to get handle for 'delay_jobs' queue from config database!")
        if (map.get_name() == this.AHB_map_name) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    // Clearing 'execute' - Expect state transition to MBOX_IDLE
                    if (~value & previous) begin
                        if (rm.mbox_data_q.size() != 0 || rm.mbox_resp_q.size() != 0) begin
                            `uvm_warning("SOC_IFC_REG_CBS", $sformatf("Clearing mbox_execute when data queues are not empty! Did the receiver fetch the amount of data it expected to? mbox_data_q.size() [%0d] mbox_resp_q.size() [%0d]", rm.mbox_data_q.size(), rm.mbox_resp_q.size()))
                        end
                        if (!rm.mbox_fn_state_sigs.uc_done_stage) begin
                            `uvm_error("SOC_IFC_REG_CBS", $sformatf("uC is clearing mbox_execute in unexpected mbox FSM state: [%p]", rm.mbox_fn_state_sigs))
                        end
                        `uvm_info("SOC_IFC_REG_CBS", "Write to mbox_execute clears the field and ends a command", UVM_HIGH)
                        rm.mbox_data_q.delete();
                        rm.mbox_resp_q.delete();
                        delay_job.state_nxt = MBOX_IDLE;
                        delay_jobs.push_back(delay_job);
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_execute on map [%s] with value [%x] predicts a state change. Delay job is queued to update DUT model.", map.get_name(), value), UVM_HIGH)
                    end
                    // Setting 'execute' - Expect state transition to MBOX_EXECUTE_SOC
                    else if (value & !previous) begin
                        // Maximum allowable size for data transferred via mailbox
                        int unsigned dlen_cap_dw = (mbox_dlen_mirrored(rm) < (mm.get_size() * mm.get_n_bytes())) ? mbox_dlen_mirrored_dword_ceil(rm) :
                                                                                                                   (mm.get_size() * mm.get_n_bytes()) >> ($clog2(MBOX_DATA_W/8));
                        if (!rm.mbox_fn_state_sigs.uc_send_stage)
                            `uvm_error("SOC_IFC_REG_CBS", $sformatf("mbox_execute is set by uC when in an unexpected state [%p]!", rm.mbox_fn_state_sigs))
                        // Round dlen up to nearest dword boundary and compare with data queue size
                        // On transfer of control, remove extraneous entries from data_q since
                        // reads of these values will be gated for the receiver in DUT
                        if ((rm.mbox_data_q.size()) != mbox_dlen_mirrored_dword_ceil(rm)) begin
                            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_execute initiates mailbox command, but the data queue entry count [%0d dwords] does not match the value of dlen [%0d bytes]!", rm.mbox_data_q.size(), mbox_dlen_mirrored(rm)), UVM_LOW)
                        end
                        if (rm.mbox_data_q.size > dlen_cap_dw) begin
                            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Extra entries detected in mbox_data_q on control transfer - deleting %d entries", rm.mbox_data_q.size() - dlen_cap_dw), UVM_FULL)
                            while (rm.mbox_data_q.size > dlen_cap_dw) begin
                                // Continuously remove last entry until size is equal to dlen, since entries are added with push_back
                                rm.mbox_data_q.delete(rm.mbox_data_q.size()-1);
                            end
                        end
                        else if (rm.mbox_data_q.size < dlen_cap_dw) begin
                            uvm_reg_data_t zeros [$];
                            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Insufficient entries detected in mbox_data_q on control transfer - 0-filling %d entries", dlen_cap_dw - rm.mbox_data_q.size()), UVM_FULL)
                            zeros = '{MBOX_DEPTH{32'h0}};
                            zeros = zeros[0:dlen_cap_dw - rm.mbox_data_q.size() - 1];
                            rm.mbox_data_q = {rm.mbox_data_q, zeros};
                        end
                        `uvm_info("SOC_IFC_REG_CBS", "Write to mbox_execute sets the field and initiates a command", UVM_HIGH)
                        delay_job.state_nxt = MBOX_EXECUTE_SOC;
                        delay_jobs.push_back(delay_job);
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_execute on map [%s] with value [%x] predicts a state change. Delay job is queued to update DUT model.", map.get_name(), value), UVM_HIGH)
                    end
                    else begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] has no effect", kind), UVM_FULL)
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
                    // Clearing 'execute' - Expect sts pin change
                    if (~value & previous) begin
                        if (rm.mbox_data_q.size() != 0 || rm.mbox_resp_q.size() != 0) begin
                            `uvm_warning("SOC_IFC_REG_CBS", $sformatf("Clearing mbox_execute when data queues are not empty! Did the receiver fetch the amount of data it expected to? mbox_data_q.size() [%0d] mbox_resp_q.size() [%0d]", rm.mbox_data_q.size(), rm.mbox_resp_q.size()))
                        end
                        if (!rm.mbox_fn_state_sigs.soc_done_stage) begin
                            `uvm_error("SOC_IFC_REG_CBS", $sformatf("SOC is clearing mbox_execute in unexpected mbox FSM state: [%p]", rm.mbox_fn_state_sigs))
                        end
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_execute clears the field and ends a command"), UVM_HIGH)
                        rm.mbox_data_q.delete();
                        rm.mbox_resp_q.delete();
                        delay_job.state_nxt = MBOX_IDLE;
                        delay_jobs.push_back(delay_job);
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_execute on map [%s] with value [%x] predicts a state change. Delay job is queued to update DUT model.", map.get_name(), value), UVM_HIGH)
                    end
                    // Setting 'execute' - Expect a uC interrupt if enabled
                    else if (value & !previous) begin
                        // Maximum allowable size for data transferred via mailbox
                        int unsigned dlen_cap_dw = (mbox_dlen_mirrored(rm) < (mm.get_size() * mm.get_n_bytes())) ? mbox_dlen_mirrored_dword_ceil(rm) :
                                                                                                                   (mm.get_size() * mm.get_n_bytes()) >> ($clog2(MBOX_DATA_W/8));
                        if (!rm.mbox_fn_state_sigs.soc_send_stage)
                            `uvm_error("SOC_IFC_REG_CBS", $sformatf("mbox_execute is set by SOC when in an unexpected state [%p]!", rm.mbox_fn_state_sigs))
                        // Round dlen up to nearest dword boundary and compare with data queue size
                        // On transfer of control, remove extraneous entries from data_q since
                        // reads of these values will be gated for the receiver in DUT
                        if (rm.mbox_data_q.size() != mbox_dlen_mirrored_dword_ceil(rm)) begin
                            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_execute initiates mailbox command, but the data queue entry count [%0d dwords] does not match the value of dlen [%0d bytes]!", rm.mbox_data_q.size(), mbox_dlen_mirrored(rm)), UVM_LOW)
                        end
                        if (rm.mbox_data_q.size > dlen_cap_dw) begin
                            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Extra entries detected in mbox_data_q on control transfer - deleting %d entries", rm.mbox_data_q.size() - dlen_cap_dw), UVM_FULL)
                            while (rm.mbox_data_q.size > dlen_cap_dw) begin
                                // Continuously remove last entry until size is equal to dlen, since entries are added with push_back
                                rm.mbox_data_q.delete(rm.mbox_data_q.size()-1);
                            end
                        end
                        else if (rm.mbox_data_q.size < dlen_cap_dw) begin
                            uvm_reg_data_t zeros [$];
                            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Insufficient entries detected in mbox_data_q on control transfer - 0-filling %d entries", dlen_cap_dw - rm.mbox_data_q.size()), UVM_FULL)
                            zeros = '{MBOX_DEPTH{32'h0}};
                            zeros = zeros[0:dlen_cap_dw - rm.mbox_data_q.size() - 1];
                            rm.mbox_data_q = {rm.mbox_data_q, zeros};
                        end
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_execute sets the field and initiates a command"), UVM_HIGH)
                        delay_job.state_nxt = MBOX_EXECUTE_UC;
                        delay_jobs.push_back(delay_job);
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_execute on map [%s] with value [%x] predicts a state change. Delay job is queued to update DUT model.", map.get_name(), value), UVM_HIGH)
                    end
                    else begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] has no effect", kind), UVM_FULL)
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
