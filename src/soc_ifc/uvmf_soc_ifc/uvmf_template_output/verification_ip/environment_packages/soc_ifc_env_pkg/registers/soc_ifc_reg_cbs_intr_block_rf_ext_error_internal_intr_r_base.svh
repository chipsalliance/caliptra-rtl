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

class soc_ifc_reg_cbs_intr_block_rf_ext_error_internal_intr_r_base extends uvm_reg_cbs;

    `uvm_object_utils(soc_ifc_reg_cbs_intr_block_rf_ext_error_internal_intr_r_base)

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
        uvm_reg_block rm;
        soc_ifc_reg__intr_block_t_ext    sir_intr_rm;
        sha512_acc_csr__intr_block_t_ext sac_intr_rm;
        bit           fld_hwset_active = 1'b0;
        uvm_reg       sts_reg;
        string event_name    ;
        uvm_reg       en_reg ;
        uvm_reg_field en_fld ;
        uvm_reg_field en_glb ;
        uvm_reg_field sts_glb;
        uvm_reg_field cnt_fld;

        delay_job = soc_ifc_reg_delay_job_intr_block_rf_ext::type_id::create("delay_job");
        delay_job.map = map;
        sts_reg = fld.get_parent();
        rm = sts_reg.get_parent(); /* intr_block_rf_ext */
        if (rm.get_parent().get_name() == "sha512_acc_csr_rm") begin
            if (!$cast(sac_intr_rm,rm)) `uvm_fatal("SOC_IFC_REG_CBS", {"Failed to get handle of expected sub-type for parent uvm_reg_block. ", fld.get_full_name()})
            fld_hwset_active = sac_intr_rm.error_internal_intr_r_hwset_active[fld.get_lsb_pos()];
        end
        else if (rm.get_parent().get_name() == "soc_ifc_reg_rm") begin
            if (!$cast(sir_intr_rm,rm)) `uvm_fatal("SOC_IFC_REG_CBS", {"Failed to get handle of expected sub-type for parent uvm_reg_block. ", fld.get_full_name()})
            fld_hwset_active = sir_intr_rm.error_internal_intr_r_hwset_active[fld.get_lsb_pos()];
        end
        else begin
            `uvm_fatal("SOC_IFC_REG_CBS", "Callback is registered to an unrecognized register block!")
        end
        // Get a base-name for the event by truncating the '_sts' suffix
        event_name = fld.get_name().substr(0,fld.get_name().len()-5);
        en_reg     = rm.get_reg_by_name("error_intr_en_r");
        en_fld     = en_reg.get_field_by_name({event_name, "_en"});
        en_glb     = rm.get_reg_by_name("global_intr_en_r").get_field_by_name("error_en");
        sts_glb    = rm.get_reg_by_name("error_global_intr_r").get_field_by_name("agg_sts");
        cnt_fld    = rm.get_reg_by_name({event_name, "_intr_count_r"}).get_field_by_name("cnt");

        if (map.get_name() == this.APB_map_name) begin
            if (kind == UVM_PREDICT_WRITE)
                `uvm_warning("SOC_IFC_REG_CBS", "Unexpected write to interrupt register through APB interface!")
            else
                `uvm_info("SOC_IFC_REG_CBS", "Unexpected read to interrupt register through APB interface!", UVM_LOW)
        end
        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Access to %s with path %p", fld.get_full_name(), path), UVM_FULL)

        // Predict an increment to event interrupt counter
        // regardless of interrupt enablement (the sts reg being
        // set is all that is tracked by the interrupt counter)
        // FIXME if a new interrupt event occurs while the interrupt sts is already 1,
        // this won't increment the counter, even though it should.
        if (value & ~previous) begin
            `uvm_info("SOC_IFC_REG_CBS", $sformatf("hwset to %s triggers increment on %s from %d to %d", fld.get_name(), cnt_fld.get_name(), cnt_fld.get_mirrored_value(), cnt_fld.get_mirrored_value() + uvm_reg_data_t'(1)), UVM_HIGH)
            cnt_fld.predict(cnt_fld.get_mirrored_value() + uvm_reg_data_t'(1));
        end

        // Anytime an access intr sts register predicts a value of 1, we can treat
        // that as a hwset (even if it's just an AHB/APB read) because we _know_ a
        // W1C won't result in value=1, which is the case we're protecting against
        // by tracking this hwset flag.
        // We must track the hwset flag for all value=1 (not just the transitions
        // where previous=0) because occasionally an actual hwset will occur when
        // the interrupt is already pending, and we still must protect against W1C
        // in that case.
        if (value) begin
            if (sir_intr_rm != null) begin
                sir_intr_rm.error_internal_intr_r_hwset_active[fld.get_lsb_pos()] = 1'b1;
                fork
                    begin
                    uvm_wait_for_nba_region();
                    sir_intr_rm.error_internal_intr_r_hwset_active[fld.get_lsb_pos()] = 1'b0;
                    end
                join_none
            end
            else if (sac_intr_rm != null) begin
                sac_intr_rm.error_internal_intr_r_hwset_active[fld.get_lsb_pos()] = 1'b1;
                fork
                    begin
                    uvm_wait_for_nba_region();
                    sac_intr_rm.error_internal_intr_r_hwset_active[fld.get_lsb_pos()] = 1'b0;
                    end
                join_none
            end
            else
                `uvm_fatal("SOC_IFC_REG_CBS", "Bad handle")
        end

        // On rising edge of field value, schedule a delay job to check if the
        // interrupt output pin will
        // transition to high.
        // Global interrupt pin "agg_sts" is non-sticky
        if ((value & ~previous))
        begin
            `uvm_info("SOC_IFC_REG_CBS", {"Predicted update to ", fld.get_name(), " triggers interrupt output pin check delay job"}, UVM_MEDIUM)
            delay_job.req_fld = fld;
            delay_job.sts_reg = sts_reg;
            delay_job.en_reg  = en_reg;
            delay_job.sts_glb = sts_glb;
            delay_job.en_glb  = en_glb;
            delay_job.grab_values();
            delay_jobs.push_back(delay_job);
        end
        // On falling edge of field value, caused by W1C, check if another thread
        // is already attempting to perform hwset to this interrupt field (hwset is
        // higher priority than W1C).
        else if ((~value & previous) && fld_hwset_active)
        begin
            `uvm_info("SOC_IFC_REG_CBS", {"Predicted update to ", fld.get_name(), " attempts to clear the interrupt bit but is preempted by an active hwset"}, UVM_MEDIUM)
            value = previous;
            // NOTE: No delay job is scheduled because no changes are predicted to
            //       other interrupt register fields based on this activity
        end
        // On falling edge of field value, schedule a delay job to
        // check if the interrupt output pin will
        // transition from high to low.
        // Global interrupt pin "agg_sts" is non-sticky
        else if ((~value & previous))
        begin
            `uvm_info("SOC_IFC_REG_CBS", {"Predicted update to ", fld.get_name(), " triggers interrupt output pin check delay job"}, UVM_MEDIUM)
            delay_job.req_fld = fld;
            delay_job.sts_reg = sts_reg;
            delay_job.en_reg  = en_reg;
            delay_job.sts_glb = sts_glb;
            delay_job.en_glb  = en_glb;
            delay_job.grab_values();
            delay_jobs.push_back(delay_job);
        end
        else begin
            `uvm_info("SOC_IFC_REG_CBS",
                      $sformatf("Access to %s does not trigger interrupt output transition due to %s: [%x], %s: [%x], masked %s: [%x], and %s: [%x]",
                                fld.get_name(),
                                en_glb.get_name(),
                                en_glb.get_mirrored_value(),
                                en_fld.get_name(),
                                en_fld.get_mirrored_value(),
                                sts_reg.get_name(),
                                sts_reg.get_mirrored_value() & ~(uvm_reg_data_t'(1) << fld.get_lsb_pos()),
                                sts_glb.get_name(),
                                sts_glb.get_mirrored_value()),
                      UVM_HIGH)
        end
    endfunction

endclass
