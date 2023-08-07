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
class soc_ifc_reg_delay_job_soc_ifc_reg_CPTRA_TRNG_CTRL_CLEAR extends soc_ifc_reg_delay_job;
    `uvm_object_utils( soc_ifc_reg_delay_job_soc_ifc_reg_CPTRA_TRNG_CTRL_CLEAR )
    soc_ifc_reg_ext rm; /* soc_ifc_reg_rm */
    uvm_reg_block rm_top;
    uvm_reg_map map;
    bit clear_trng_data_regs;
    int i;

    virtual task do_job();
        `uvm_info("SOC_IFC_REG_DELAY_JOB", "Running delayed job for soc_ifc_reg.CPTRA_TRNG_CTRL.clear", UVM_LOW)
        rm_top = rm.get_parent();
        for (i=0; i<$size(rm.CPTRA_TRNG_DATA); i++) begin
            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Before clear: TRNG data[%0d] value 0x%x", i, rm.CPTRA_TRNG_DATA[i].DATA.get_mirrored_value()), UVM_DEBUG)
        end
        if (clear_trng_data_regs) begin
            for (i=0; i<$size(rm.CPTRA_TRNG_DATA); i++) begin
                rm.CPTRA_TRNG_DATA[i].DATA.predict(uvm_reg_data_t'(0));
            end
        end
        for (i=0; i<$size(rm.CPTRA_TRNG_DATA); i++) begin
            `uvm_info("SOC_IFC_REG_CBS", $sformatf("After clear: TRNG data[%0d] value 0x%x", i, rm.CPTRA_TRNG_DATA[i].DATA.get_mirrored_value()), UVM_DEBUG)
        end
    endtask
endclass

// Callback for CPTRA TRNG CTRL register
class soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_CTRL_CLEAR extends uvm_reg_cbs;

    `uvm_object_utils(soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_CTRL_CLEAR)

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

        soc_ifc_reg_delay_job_soc_ifc_reg_CPTRA_TRNG_CTRL_CLEAR delay_job_clear_trng_data_regs;
        soc_ifc_reg_ext rm; /* soc_ifc_reg_rm */
        uvm_reg_block blk = fld.get_parent().get_parent(); /* soc_ifc_reg_rm */
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")
        delay_job_clear_trng_data_regs = soc_ifc_reg_delay_job_soc_ifc_reg_CPTRA_TRNG_CTRL_CLEAR::type_id::create("delay_job_clear_trng_data_regs");
        delay_job_clear_trng_data_regs.rm = rm;
        delay_job_clear_trng_data_regs.map = map;
        delay_job_clear_trng_data_regs.clear_trng_data_regs = 1;
        //account for state transitions + variable wait cycle time
        delay_job_clear_trng_data_regs.set_delay_cycles(1);

        if (map.get_name() == this.AHB_map_name) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    if (value & !previous) begin
                        //push a delayed job for clearing of TRNG data regs
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Sending delay job for internal register field %s with %0d clk delay", fld.get_full_name(), delay_job_clear_trng_data_regs.get_delay_cycles()), UVM_LOW)
                        value = 1'b0; //TRNG_CTRL.clear is a pulse
                        delay_jobs.push_back(delay_job_clear_trng_data_regs);
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
