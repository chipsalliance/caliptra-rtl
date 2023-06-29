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

// Callback to add to all register fields.
// This callback is used to sample coverage after every prediction
// against the register field it is called on.
// Expected to be run after any other post_predict callbacks complete

class soc_ifc_reg_cbs_sample extends uvm_reg_cbs;

    `uvm_object_utils(soc_ifc_reg_cbs_sample)

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
        uvm_reg parent;
        uvm_reg_data_t data;
        uvm_reg_data_t mask;
        bit is_read;
        parent = fld.get_parent();
        is_read = kind == UVM_PREDICT_READ;
        mask = (1 << fld.get_n_bits()) - 1;
        mask <<= fld.get_lsb_pos();
        mask = ~mask;
        data = (parent.get_mirrored_value() & mask) | (value << fld.get_lsb_pos());
        // Only sample coverage for the field that is being modified.
        // Since post-predict is called independently for every field in a register
        // by the reg predictor, this ensures that coverage is only captured for
        // the register with the new value.
        if (value != previous) begin
            parent.XsampleX(data, -1, is_read, map);
            `uvm_info("SOC_IFC_REG_SAMPLE_CBS", $sformatf("post_predict called with kind [%p] path [%p] map [%s] on fld [%s] to sample coverage", kind, path, map.get_name(), fld.get_full_name()), UVM_DEBUG)
        end
        else begin
            `uvm_info("SOC_IFC_REG_SAMPLE_CBS", $sformatf("post_predict called with kind [%p] path [%p] map [%s] on fld [%s] does not result in coverage sampling due to no value change", kind, path, map.get_name(), fld.get_full_name()), UVM_DEBUG)
        end
    endfunction

endclass
