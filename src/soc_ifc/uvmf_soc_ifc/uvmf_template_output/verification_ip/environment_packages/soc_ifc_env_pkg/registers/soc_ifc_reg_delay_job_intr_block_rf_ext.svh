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

// Reg predictions that will be scheduled on value change in notif_internal_intr_r
class soc_ifc_reg_delay_job_intr_block_rf_ext extends soc_ifc_reg_delay_job;
    `uvm_object_utils( soc_ifc_reg_delay_job_intr_block_rf_ext )

    uvm_reg_field req_fld; /* used to report the reg field that caused the delay job */
    uvm_reg       sts_reg;
    uvm_reg       en_reg ;
    uvm_reg_field en_glb ;
    uvm_reg_field sts_glb;
    uvm_reg_map map;

    uvm_reg_data_t val_sts_reg;
    uvm_reg_data_t val_en_reg ;
    uvm_reg_data_t val_en_glb ;
    uvm_reg_data_t val_sts_glb;

    virtual function void grab_values();
        fork
            begin
            // Wait for all predictor callbacks to run for every intr bit accessed
            // during the current clock cycle, so mirrors are up to date
            uvm_wait_for_nba_region();
            // There might be delay_jobs running additional bit updates
            // at this point, so wait again
            // FIXME -- find a better way to capture field updates at each clock edge
            uvm_wait_for_nba_region();
            // Snapshot of current value, since next cycle may see value changes again
            val_sts_reg = sts_reg.get_mirrored_value();
            val_en_reg  = en_reg .get_mirrored_value();
            val_en_glb  = en_glb .get_mirrored_value();
            val_sts_glb = sts_glb.get_mirrored_value();
            end
        join_none
    endfunction

    virtual task do_job();
        `uvm_info("SOC_IFC_REG_DELAY_JOB", $sformatf("Running delayed job for %s", req_fld.get_full_name()), UVM_MEDIUM)
        if (!sts_glb.get_mirrored_value() && |(val_sts_reg & val_en_reg)) begin
            sts_glb.predict(1'b1);
            `uvm_info("SOC_IFC_REG_DELAY_JOB",
                      $sformatf("post_predict called through map [%p] on %s results in interrupt status bit being set to 0x%0x. Values: en_reg(latched) [0x%0x(0x%0x)] sts_reg [0x%0x(0x%0x)] en_glb [0x%0x(0x%0x)] sts_glb [0x%0x(0x%0x)]",
                                map.get_name(), req_fld.get_full_name(), sts_glb.get_mirrored_value(),
                                en_reg.get_mirrored_value(),  val_en_reg ,
                                sts_reg.get_mirrored_value(), val_sts_reg,
                                en_glb.get_mirrored_value(),  val_en_glb ,
                                sts_glb.get_mirrored_value(), val_sts_glb),
                      UVM_MEDIUM)
        end
        else if (sts_glb.get_mirrored_value() && !(|(val_sts_reg & val_en_reg))) begin
            sts_glb.predict(1'b0);
            `uvm_info("SOC_IFC_REG_DELAY_JOB",
                      $sformatf("post_predict called through map [%p] on %s results in interrupt status bit being cleared to 0x%0x. Values: en_reg(latched) [0x%0x(0x%0x)] sts_reg [0x%0x(0x%0x)] en_glb [0x%0x(0x%0x)] sts_glb [0x%0x(0x%0x)]",
                                map.get_name(), req_fld.get_full_name(), sts_glb.get_mirrored_value(),
                                en_reg.get_mirrored_value(),  val_en_reg ,
                                sts_reg.get_mirrored_value(), val_sts_reg,
                                en_glb.get_mirrored_value(),  val_en_glb ,
                                sts_glb.get_mirrored_value(), val_sts_glb),
                      UVM_MEDIUM)
        end
        else begin
            `uvm_info("SOC_IFC_REG_DELAY_JOB",
                      $sformatf("Delay job for %s does not predict any changes due to: en_reg(latched) [0x%0x(0x%0x)] sts_reg [0x%0x(0x%0x)] en_glb [0x%0x(0x%0x)] sts_glb [0x%0x(0x%0x)]",
                                req_fld.get_full_name(),
                                en_reg.get_mirrored_value(),  val_en_reg ,
                                sts_reg.get_mirrored_value(), val_sts_reg,
                                en_glb.get_mirrored_value(),  val_en_glb ,
                                sts_glb.get_mirrored_value(), val_sts_glb),
                      UVM_HIGH)
        end
    endtask
endclass


