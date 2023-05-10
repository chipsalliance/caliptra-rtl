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

class soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_DATA_DATA extends uvm_reg_cbs;

    `uvm_object_utils(soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_DATA_DATA)

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
        soc_ifc_reg_ext rm; /* soc_ifc_reg_rm */
        uvm_reg_adapter ah; // Adapter handle, need to cast to Caliptra specialization
        uvm_reg_block blk = fld.get_parent().get_parent(); /* soc_ifc_reg_rm */
        ah = map.get_root_map().get_adapter();
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")
        if (map.get_name() == this.AHB_map_name) begin
            case (kind) inside
                UVM_PREDICT_READ: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] has no effect. value: 0x%x previous: 0x%x", kind, value, previous), UVM_FULL)
                end
                UVM_PREDICT_WRITE: begin
                    if (value != previous) begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] attempts to change register value but is blocked. value: 0x%x previous: 0x%x", kind, value, previous), UVM_LOW)
                        // AHB has RO access to TRNG_DATA only
                        value = previous;
                    end
                    else begin
                        `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] has no effect. value: 0x%x previous: 0x%x", kind, value, previous), UVM_FULL)
                    end
                end
                default: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] has no effect", kind), UVM_FULL)
                end
            endcase
        end
        else if (map.get_name() == this.APB_map_name) begin
            apb_reg_adapter_t adapter;
            if (!$cast(adapter,ah)) `uvm_fatal("SOC_IFC_REG_CBS", "Failed to get valid adapter handle")
            case (kind) inside
                UVM_PREDICT_READ, UVM_PREDICT_WRITE: begin
                    // Compare the PAUSER value used for the current reg access
                    // with the locked value in the reg model. If mismatch, block
                    // any reg-prediction changes on this field.
                    // The current reg access PAUSER value is stored to the user_obj
                    // inside the adapter by the apb_reg_predictor when it receives
                    // a request to do prediction for a reg access, via a call
                    // to bus2reg. This occurs prior to invoking "do_predict".
                    if (rm.CPTRA_TRNG_PAUSER_LOCK.LOCK.get_mirrored_value() &&
                        adapter.bus2reg_user_obj.get_addr_user() != rm.CPTRA_TRNG_VALID_PAUSER.PAUSER.get_mirrored_value() &&
                        value != previous) begin
                        `uvm_info("SOC_IFC_REG_CBS",
                                  $sformatf("post_predict called with kind [%p] blocked attempt to update CPTRA_TRNG_STATUS.%s due to PAUSER mismatch. lock: %0d VALID_PAUSER: 0x%x BUS_PAUSER: 0x%x",
                                            kind,
                                            fld.get_name(),
                                            rm.CPTRA_TRNG_PAUSER_LOCK.LOCK.get_mirrored_value(),
                                            rm.CPTRA_TRNG_VALID_PAUSER.PAUSER.get_mirrored_value(),
                                            adapter.bus2reg_user_obj.get_addr_user()),
                                  UVM_FULL)
                        value = previous;
                    end
                    else begin
                        // Any access with a valid PAUSER means post_predict won't manipulate the predicted value update to the mirror
                        `uvm_info("SOC_IFC_REG_CBS",
                                  $sformatf("post_predict called with kind [%p] has no effect due to valid PAUSER [0x%x] used and LOCK [%0d]. value: 0x%x previous: 0x%x",
                                            kind,
                                            adapter.bus2reg_user_obj.get_addr_user(),
                                            rm.CPTRA_TRNG_PAUSER_LOCK.LOCK.get_mirrored_value(),
                                            value,
                                            previous),
                                  UVM_FULL)
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
