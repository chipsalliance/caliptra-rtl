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

class soc_ifc_reg_cbs_mbox_csr_tap_mode_enabled extends soc_ifc_reg_cbs_mbox_csr;

    `uvm_object_utils(soc_ifc_reg_cbs_mbox_csr_tap_mode_enabled)

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
        mbox_csr_ext rm; /* mbox_csr_rm */
        uvm_reg_block blk = fld.get_parent().get_parent(); /* mbox_csr_rm */
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")
        if (map.get_name() == this.AHB_map_name) begin
            `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] on map [%s] has no effect on register field %s", kind, map.get_name(), fld.get_full_name()), UVM_FULL)
        end
        else if (map.get_name() == this.AXI_map_name) begin
            case (kind) inside
                UVM_PREDICT_WRITE: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict blocked write attempt to reg field %s on map %s. value: 0x%x previous: 0x%x", fld.get_full_name(), map.get_name(), value, previous), UVM_LOW)
                    value = previous;
                end
                default: begin
                    `uvm_info("SOC_IFC_REG_CBS", $sformatf("post_predict called with kind [%p] on map [%s] has no effect on register field %s. value: 0x%x previous: 0x%x", kind, map.get_name(), fld.get_full_name(), value, previous), UVM_FULL)
                end
            endcase
        end
        else begin
            `uvm_error("SOC_IFC_REG_CBS", {"post_predict called through unsupported reg map! ", map.get_name()})
        end
    endfunction

endclass
