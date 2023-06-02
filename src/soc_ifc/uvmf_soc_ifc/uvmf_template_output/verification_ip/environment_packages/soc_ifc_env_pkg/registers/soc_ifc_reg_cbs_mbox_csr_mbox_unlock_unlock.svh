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
    virtual task do_job();
        `uvm_info("SOC_IFC_REG_DELAY_JOB", "Running delayed job for mbox_csr.mbox_unlock.unlock", UVM_HIGH)
        rm.mbox_lock.lock.predict(1'b0);
        rm.mbox_execute.execute.predict(1'b0);
        rm.mbox_status.status.predict(CMD_BUSY);
        rm.mbox_status.mbox_fsm_ps.predict(MBOX_IDLE);
        rm.mbox_status.soc_has_lock.predict(1'b0);
        rm.mbox_fn_state_sigs = '{mbox_idle: 1'b1, default: 1'b0};
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
        mbox_csr_ext rm; /* mbox_csr_rm */
        uvm_reg_block blk = fld.get_parent().get_parent(); /* mbox_csr_rm */
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")
        if ((map.get_name() == this.AHB_map_name)) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    if (value) begin
                        uvm_queue #(soc_ifc_reg_delay_job) delay_jobs;
                        if (!uvm_config_db#(uvm_queue#(soc_ifc_reg_delay_job))::get(null, "soc_ifc_reg_model_top", "delay_jobs", delay_jobs))
                            `uvm_error("SOC_IFC_REG_CBS", "Failed to get handle for 'delay_jobs' queue from config database!")
                        delay_job = soc_ifc_reg_delay_job_mbox_csr_mbox_unlock_unlock::type_id::create("delay_job");
                        delay_job.rm = rm;
                        delay_job.set_delay_cycles(1);
                        delay_jobs.push_back(delay_job);
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Write to mbox_unlock on map [%s] with value [%x] clears mbox_lock and auto-clears. Delay job is queued to update DUT model.", map.get_name(), value), UVM_HIGH)
                        value = previous;
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
