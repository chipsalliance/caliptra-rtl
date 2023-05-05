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

class soc_ifc_reg_cbs_intr_block_rf_ext_error_intr_trig_r_base extends uvm_reg_cbs;

    `uvm_object_utils(soc_ifc_reg_cbs_intr_block_rf_ext_error_intr_trig_r_base)

    string AHB_map_name = "soc_ifc_AHB_map";
    string APB_map_name = "soc_ifc_APB_map";

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
        uvm_reg_block rm;
        string        event_name;
        uvm_reg       sts_reg;
        uvm_reg_field sts_fld;

        rm = fld.get_parent().get_parent(); /* intr_block_rf_ext */
        // Get a base-name for the event by truncating the '_trig' suffix
        event_name = fld.get_name().substr(0,fld.get_name().len()-6);
        sts_reg  = rm.get_reg_by_name("error_internal_intr_r");
        sts_fld  = sts_reg.get_field_by_name({event_name, "_sts"});

        if (map.get_name() == this.APB_map_name) begin
            if (kind == UVM_PREDICT_WRITE)
                `uvm_warning("SOC_IFC_REG_CBS", "Unexpected write to interrupt register through APB interface!")
            else
                `uvm_info("SOC_IFC_REG_CBS", "Unexpected read to interrupt register through APB interface!", UVM_LOW)
        end
        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Access to %s with path %p", fld.get_full_name(), path), UVM_FULL)

        if (kind == UVM_PREDICT_WRITE) begin
            // On rising edge of field trigger value, predict interrupt status will
            // be set
            if (value & ~previous) begin
                `uvm_info("SOC_IFC_REG_CBS", {"Predicted update to ", fld.get_name(), " triggers interrupt output pin assertion"}, UVM_MEDIUM)
                //  - Use UVM_PREDICT_READ kind so that all the callbacks associated with
                //    notif_<event>_sts are also called to detect interrupt pin assertion
                //  - Use UVM_PREDICT_READ instead of UVM_PREDICT_WRITE so that
                //    "do_predict" bypasses the access-check and does not enforce W1C
                //    behavior on this attempt to set interrupt status to 1
                sts_fld.predict(1'b1, -1, UVM_PREDICT_READ, UVM_PREDICT, map); /* Intr reg access expected only via AHB i/f */
            end

            // Because interrupt triggers are single-pulse, they auto-clear immediately on
            // being written.
            // So set predicted value to 0.
            value = 0;
            `uvm_info("SOC_IFC_REG_CBS",
                      $sformatf("Write to %s results in mirrored value forcibly predicted to [%x]",
                                fld.get_name(),
                                value),
                      UVM_HIGH)
        end
    endfunction

endclass
