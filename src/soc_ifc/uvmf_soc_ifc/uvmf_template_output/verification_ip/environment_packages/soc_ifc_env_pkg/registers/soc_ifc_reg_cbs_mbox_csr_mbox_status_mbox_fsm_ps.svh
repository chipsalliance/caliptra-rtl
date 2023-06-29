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

// Reg predictions that will be scheduled on mbox_fsm_ps state change
class soc_ifc_reg_delay_job_mbox_csr_mbox_status_mbox_fsm_ps extends soc_ifc_reg_delay_job;
    `uvm_object_utils( soc_ifc_reg_delay_job_mbox_csr_mbox_status_mbox_fsm_ps )

    mbox_csr_ext rm; /* mbox_csr_rm */
    uvm_reg_block rm_top;
    uvm_reg_field intr_fld;
    virtual task do_job();
        `uvm_info("SOC_IFC_REG_DELAY_JOB", "Running delayed job for mbox_csr.mbox_status.mbox_fsm_ps", UVM_HIGH)
        rm_top = rm.get_parent();
        intr_fld = rm_top.get_block_by_name("soc_ifc_reg_rm").get_block_by_name("intr_block_rf_ext").get_field_by_name("notif_cmd_avail_sts");

        // Predict intr sts register is set
        //  - Use UVM_PREDICT_READ kind so that all the callbacks associated with
        //    notif_cmd_avail_sts are also called to detect interrupt pin assertion
        //  - Use UVM_PREDICT_READ instead of UVM_PREDICT_WRITE so that
        //    "do_predict" bypasses the access-check and does not enforce W1C
        //    behavior on this attempt to set interrupt status to 1
        intr_fld.predict(1'b1, -1, UVM_PREDICT_READ, UVM_PREDICT, rm_top.get_map_by_name("soc_ifc_AHB_map")); /* Intr reg access expected only via AHB i/f */
    endtask
endclass

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
        soc_ifc_reg_delay_job_mbox_csr_mbox_status_mbox_fsm_ps delay_job;
        mbox_csr_ext rm; /* mbox_csr_rm */
        mbox_fsm_state_e old_ps;
        mbox_fsm_state_e new_ps;
        uvm_reg_block blk = fld.get_parent().get_parent(); /* mbox_csr_rm */
        if (!$cast(rm,blk)) `uvm_fatal ("SOC_IFC_REG_CBS", "Failed to get valid class handle")

        old_ps = mbox_fsm_state_e'(previous);
        new_ps = mbox_fsm_state_e'(value);
        `uvm_info("SOC_IFC_REG_CBS", $sformatf("Prediction on mbox_status updates mbox_fsm_ps mirror to %p", new_ps), UVM_DEBUG)

        // State change results in notification interrupt bit being set to uC
        // Only if the functional state signals tracker in the reg-model still reports
        // an old state (which means this is truly the first transition to MBOX_EXECUTE_UC,
        // and not some spurious transition on the reg mirror after the RTL has already
        // made the state transition).
        if (old_ps != new_ps && new_ps == MBOX_EXECUTE_UC && (rm.mbox_fn_state_sigs.soc_data_stage || rm.mbox_fn_state_sigs.soc_receive_stage)) begin
            delay_job = soc_ifc_reg_delay_job_mbox_csr_mbox_status_mbox_fsm_ps::type_id::create("delay_job");
            delay_job.rm = rm;
            delay_job.set_delay_cycles(0);
            delay_jobs.push_back(delay_job);
            `uvm_info("SOC_IFC_REG_CBS", $sformatf("Access to mbox_status.mbox_fsm_ps on map [%s] with value [%x] predicts a state change. Delay job is queued to update DUT model.", map.get_name(), value), UVM_HIGH)
        end
    endfunction

endclass
