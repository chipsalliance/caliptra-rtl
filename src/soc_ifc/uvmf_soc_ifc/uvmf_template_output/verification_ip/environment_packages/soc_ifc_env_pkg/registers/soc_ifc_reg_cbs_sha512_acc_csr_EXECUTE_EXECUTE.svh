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
class soc_ifc_reg_delay_job_sha512_acc_csr_EXECUTE_EXECUTE extends soc_ifc_reg_delay_job;
    `uvm_object_utils( soc_ifc_reg_delay_job_sha512_acc_csr_EXECUTE_EXECUTE )
    sha512_acc_csr_ext rm; /* sha512_acc_csr_rm */
    uvm_reg_block rm_top;
    uvm_reg_field intr_fld;
    uvm_reg_map map;
    virtual task do_job();
        `uvm_info("SOC_IFC_REG_DELAY_JOB", "Running delayed job for sha512_acc_csr.EXECUTE.EXECUTE", UVM_HIGH)
        rm_top = rm.get_parent();
        intr_fld = rm_top.get_block_by_name("sha512_acc_csr_rm").get_block_by_name("intr_block_rf_ext").get_field_by_name("notif_cmd_done_sts");
        // Check LOCK before predicting interrupt occurrence
        if (rm.LOCK.LOCK.get_mirrored_value()) begin
            // Predict intr sts register is set to indicate operation completes
            //  - Use UVM_PREDICT_READ kind so that all the callbacks associated with
            //    notif_cmd_done_sts are also called to detect interrupt pin assertion
            //  - Use UVM_PREDICT_READ instead of UVM_PREDICT_WRITE so that
            //    "do_predict" bypasses the access-check and does not enforce W1C
            //    behavior on this attempt to set interrupt status to 1
            intr_fld.predict(1'b1, -1, UVM_PREDICT_READ, UVM_PREDICT, rm_top.get_map_by_name("soc_ifc_AHB_map")); /* Intr reg access expected only via AHB i/f */
            `uvm_info("SOC_IFC_REG_DELAY_JOB", $sformatf("post_predict called through map [%p] on EXECUTE results in interrupt status bit being set.", map.get_name()), UVM_FULL)
        end
        else begin
            `uvm_error("SOC_IFC_REG_DELAY_JOB",
                       $sformatf("Delay job for EXECUTE does not predict any changes due to: LOCK mirror [%d]",
                                 rm.LOCK.LOCK.get_mirrored_value()))
        end
    endtask
endclass

class soc_ifc_reg_cbs_sha512_acc_csr_EXECUTE_EXECUTE extends uvm_reg_cbs;

    `uvm_object_utils(soc_ifc_reg_cbs_sha512_acc_csr_EXECUTE_EXECUTE)

    string AHB_map_name = "soc_ifc_AHB_map";
    string APB_map_name = "soc_ifc_APB_map";
    
    uvm_queue #(soc_ifc_reg_delay_job) delay_jobs;

    function new(string name = "uvm_reg_cbs");
        super.new(name);
        if (!uvm_config_db#(uvm_queue#(soc_ifc_reg_delay_job))::get(null, "soc_ifc_reg_model_top", "delay_jobs", delay_jobs))
            `uvm_error("SOC_IFC_REG_CBS", "Failed to get handle for 'delay_jobs' queue from config database!")
    endfunction

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
        soc_ifc_reg_delay_job_sha512_acc_csr_EXECUTE_EXECUTE delay_job;
        sha512_acc_csr_ext rm; /* sha512_acc_csr_rm */
        uvm_reg_block blk = fld.get_parent().get_parent(); /* sha512_acc_csr_rm */
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")
        delay_job = soc_ifc_reg_delay_job_sha512_acc_csr_EXECUTE_EXECUTE::type_id::create("delay_job");
        delay_job.rm = rm;
        delay_job.map = map;
        // 82 cycle delay based on waveform analysis of minimum delay from EXECUTE->DONE
        // Commentary on a more sophisticated analysis:
        // -----------------------------------------------------------
        //   Streaming mode - 82 or 164 clocks after setting execute. If the
        //   padding fits in the current block we pad and process, interrupt will
        //   come 82 clocks later. If padding doesn't fit, we process the current
        //   block and another block with the padding. 164 clocks. There may be a
        //   clock or two for state transitions in there.
        //    
        //   Mailbox mode - DLEN/128 should tell you how many 1024 bit blocks
        //   you have to process. We can read a block faster than process, so the
        //   long pole is the process time. Something like 32 clocks to read
        //   the first block + 82 clocks per block to process each. Total DLEN
        //   could be less than 1024, so in that case the initial read would be
        //   DLEN/4 clocks. There's also the case that the size requires an
        //   additional padding block, which may be computed if necessary.
        // -----------------------------------------------------------
        delay_job.set_delay_cycles(81);
        if (map.get_name() == this.AHB_map_name) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    if (value & ~previous) begin
                        delay_jobs.push_back(delay_job);
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] on map [%s] results in predicted interrupt. Delay job queued. value: 0x%x previous: 0x%x", kind, map.get_name(), value, previous), UVM_FULL)
                    end
                    else begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] on map [%s] has no effect", kind, map.get_name()), UVM_FULL)
                    end
                end
                default: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] on map [%s] has no effect", kind, map.get_name()), UVM_FULL)
                end
            endcase
        end
        else if (map.get_name() == this.APB_map_name) begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] on map [%s] has no effect", kind, map.get_name()), UVM_FULL)
        end
        else begin
            `uvm_error("SOC_IFC_REG_CBS", $sformatf("post_predict called through unsupported reg map %s!", map.get_name()))
        end
    endfunction

endclass
