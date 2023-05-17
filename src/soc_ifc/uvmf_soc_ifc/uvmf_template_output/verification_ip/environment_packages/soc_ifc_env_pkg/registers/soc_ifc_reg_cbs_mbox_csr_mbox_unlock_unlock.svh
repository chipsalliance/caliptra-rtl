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

// Reg predictions that will be scheduled on AHB write to mbox_unlock
class soc_ifc_reg_delay_job_mbox_csr_mbox_unlock_unlock extends soc_ifc_reg_delay_job;
    `uvm_object_utils( soc_ifc_reg_delay_job_mbox_csr_mbox_unlock_unlock )
    mbox_csr_ext rm; /* mbox_csr_rm */
    uvm_reg_map map;
    virtual task do_job();
        `uvm_info("SOC_IFC_REG_DELAY_JOB", "Running delayed job for mbox_csr.mbox_unlock.unlock", UVM_HIGH)
        rm.mbox_execute.execute.predict(1'b0, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
        rm.mbox_status.status.predict(CMD_BUSY, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
        rm.mbox_status.mbox_fsm_ps.predict(MBOX_IDLE, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
        rm.mbox_status.soc_has_lock.predict(1'b0, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
        rm.mbox_fn_state_sigs = '{mbox_idle: 1'b1, default: 1'b0};
        rm.mbox_unlock.unlock.predict(1'b0);
        if (rm.mbox_lock.is_busy()) begin
            `uvm_info("SOC_IFC_REG_DELAY_JOB", "Delay job for mbox_unlock attempted to clear mbox_lock, but hit access collision! Flagging clear event in reg-model for mbox_lock callback to handle", UVM_LOW)
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
                        `uvm_error("SOC_IFC_REG_DELAY_JOB", $sformatf("mbox_lock clear activity, originally requested by mbox_unlock callback but unserviceable, was scheduled to be completed during mbox_lock callback but took longer than expected to finish!"))
                    end
                join_any
            end
        end
        else begin
            rm.mbox_lock.lock.predict(0);
        end
    endtask
endclass

class soc_ifc_reg_cbs_mbox_csr_mbox_unlock_unlock extends soc_ifc_reg_cbs_mbox_csr;

    `uvm_object_utils(soc_ifc_reg_cbs_mbox_csr_mbox_unlock_unlock)

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
        soc_ifc_reg_delay_job_mbox_csr_mbox_unlock_unlock delay_job;
        uvm_queue #(soc_ifc_reg_delay_job) delay_jobs;
        mbox_csr_ext rm; /* mbox_csr_rm */
        uvm_reg_block blk = fld.get_parent().get_parent(); /* mbox_csr_rm */
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")
        if (!uvm_config_db#(uvm_queue#(soc_ifc_reg_delay_job))::get(null, "soc_ifc_reg_model_top", "delay_jobs", delay_jobs))
            `uvm_error("SOC_IFC_REG_CBS", "Failed to get handle for 'delay_jobs' queue from config database!")
        delay_job = soc_ifc_reg_delay_job_mbox_csr_mbox_unlock_unlock::type_id::create("delay_job");
        delay_job.rm = rm;
        delay_job.map = map;
        delay_job.set_delay_cycles(0);
        if ((map.get_name() == this.AHB_map_name)) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    if (value) begin
                        delay_jobs.push_back(delay_job);
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_unlock on map [%s] with value [%x] clears mbox_lock and auto-clears. Delay job is queued to update DUT model.", map.get_name(), value), UVM_HIGH)
                        //value = previous; // Delay this (field is 1 for 1-cycle)
                    end
                    else begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_unlock on map [%s] with value [%x] has no effect", map.get_name(), value), UVM_FULL)
                    end
                end
                default: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] has no effect", kind), UVM_FULL)
                end
            endcase
        end
        else if ((map.get_name() == this.APB_map_name)) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_unlock on map [%s] has no effect and is discarded", map.get_name()), UVM_FULL)
                    value = previous;
                end
                default: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] has no effect", kind), UVM_FULL)
                end
            endcase
        end
        else begin
            `uvm_error("SOC_IFC_REG_CBS", {"post_predict called through unsupported reg map! ", map.get_name()})
        end
    endfunction

endclass
