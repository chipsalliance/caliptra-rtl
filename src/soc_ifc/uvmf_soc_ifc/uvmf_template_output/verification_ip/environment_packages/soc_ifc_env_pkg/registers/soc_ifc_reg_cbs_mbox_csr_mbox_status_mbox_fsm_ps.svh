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

class soc_ifc_reg_cbs_mbox_csr_mbox_status_mbox_fsm_ps extends soc_ifc_reg_cbs_mbox_csr;

    `uvm_object_utils(soc_ifc_reg_cbs_mbox_csr_mbox_status_mbox_fsm_ps)

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
        mbox_fsm_state_e new_ps;
        new_ps = mbox_fsm_state_e'(value);
        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Prediction on mbox_status updates mbox_fsm_ps mirror to %p", new_ps), UVM_DEBUG)
    endfunction

endclass
