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

class soc_ifc_reg_cbs_intr_block_rf_ext_notif_intr_en_r_base extends uvm_reg_cbs;

    `uvm_object_utils(soc_ifc_reg_cbs_intr_block_rf_ext_notif_intr_en_r_base)

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
        soc_ifc_reg_delay_job_intr_block_rf_ext delay_job;
        uvm_reg       en_reg;
        uvm_reg_block rm;
        string        event_name;
        uvm_reg       sts_reg;
        uvm_reg_field sts_fld;
        uvm_reg_field en_glb ;
        uvm_reg_field sts_glb;

        delay_job = soc_ifc_reg_delay_job_intr_block_rf_ext::type_id::create("delay_job");
        delay_job.map = map;
        en_reg = fld.get_parent();
        rm     = en_reg.get_parent(); /* intr_block_rf_ext */
        // Get a base-name for the event by truncating the '_en' suffix
        event_name = fld.get_name().substr(0,fld.get_name().len()-4);
        sts_reg = rm.get_reg_by_name("notif_internal_intr_r");
        sts_fld = sts_reg.get_field_by_name({event_name, "_sts"});
        en_glb  = rm.get_reg_by_name("global_intr_en_r").get_field_by_name("notif_en");
        sts_glb = rm.get_reg_by_name("notif_global_intr_r").get_field_by_name("agg_sts");

        if (map.get_name() == this.APB_map_name) begin
            if (kind == UVM_PREDICT_WRITE) begin
                `uvm_warning("SOC_IFC_REG_CBS", {"Unexpected write to interrupt register ", fld.get_full_name(), " through APB interface is blocked!"})
                value = previous;
                return;
            end
            else
                `uvm_info("SOC_IFC_REG_CBS", "Unexpected read to interrupt register through APB interface!", UVM_LOW)
        end
        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Access to %s with path %p", fld.get_full_name(), path), UVM_FULL)

        // On rising edge of field value, check if the interrupt output pin will
        // transition to high.
        // Global interrupt pin "agg_sts" is non-sticky
        if ((value & ~previous))
        begin
            `uvm_info("SOC_IFC_REG_CBS", {"Predicted update to ", fld.get_name(), " triggers interrupt output pin assertion"}, UVM_MEDIUM)
            delay_job.req_fld = fld;
            delay_job.sts_reg = sts_reg;
            delay_job.en_reg  = en_reg;
            delay_job.sts_glb = sts_glb;
            delay_job.en_glb  = en_glb;
            delay_jobs.push_back(delay_job);
        end
        // On falling edge of field value, check if the interrupt output pin will
        // transition from high to low.
        // Global interrupt pin "agg_sts" is non-sticky
        else if ((~value & previous))
        begin
            `uvm_info("SOC_IFC_REG_CBS", {"Predicted update to ", fld.get_name(), " triggers interrupt output pin deassertion"}, UVM_MEDIUM)
            delay_job.req_fld = fld;
            delay_job.sts_reg = sts_reg;
            delay_job.en_reg  = en_reg;
            delay_job.sts_glb = sts_glb;
            delay_job.en_glb  = en_glb;
            delay_jobs.push_back(delay_job);
        end
        else begin
            `uvm_info("SOC_IFC_REG_CBS",
                      $sformatf("Write to %s with value %0d does not trigger interrupt output transition due to %s: [%x], %s: [%x], and %s: [%x]",
                                fld.get_name(),
                                value,
                                en_glb.get_name(),
                                en_glb.get_mirrored_value(),
                                sts_fld.get_name(),
                                sts_fld.get_mirrored_value(),
                                sts_glb.get_name(),
                                sts_glb.get_mirrored_value()),
                      UVM_HIGH)
        end
    endfunction

endclass
