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

// Reg predictions that will be scheduled on any invalid access to trigger errors
class soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error extends soc_ifc_reg_delay_job;
    `uvm_object_utils( soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error )
    mbox_csr_ext rm; /* mbox_csr_rm */
    uvm_reg_field fld;
    mbox_fsm_state_e state_nxt;
    uvm_reg_map map;
    mbox_protocol_error_t error = '{default: 1'b0};
    virtual task do_job();
        if (fld == null || map == null || rm == null)
            `uvm_fatal("SOC_IFC_REG_DELAY_JOB", "Missing handle for fld, map, or rm")

        `uvm_info("SOC_IFC_REG_DELAY_JOB", "Running delayed job for mbox_csr due to detected protocol error", UVM_HIGH)
        if (error.axs_without_lock && (rm.mbox_lock.lock.get_mirrored_value() || !rm.mbox_fn_state_sigs.mbox_idle)) begin
            `uvm_fatal("SOC_IFC_REG_DELAY_JOB", "no_lock mbox error while mbox is locked or not-idle! This shouldn't happen and I haven't thought of how to deal with this yet! FIXME!")
        end
        else if (error.axs_without_lock) begin
            uvm_reg_block top;
            uvm_reg_field intr_fld;
            uvm_reg_field non_fatal_fld;

            top           = rm.get_parent();
            intr_fld      = top.get_block_by_name("soc_ifc_reg_rm").get_block_by_name("intr_block_rf_ext").get_field_by_name("error_cmd_fail_sts");
            non_fatal_fld = top.get_block_by_name("soc_ifc_reg_rm").get_reg_by_name("CPTRA_HW_ERROR_NON_FATAL").get_field_by_name("mbox_prot_no_lock");

            intr_fld     .predict(1'b1, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map.get_parent().get_map_by_name("soc_ifc_AHB_map")));
            non_fatal_fld.predict(1'b1, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));

            `uvm_info("SOC_IFC_REG_DELAY_JOB", $sformatf("delay_job scheduled for access through map [%p] on [%s] results in Access Without Lock Error, and no state change. Functional state tracker: [%p] mbox_fsm_ps transition (ignored) [%p]", map.get_name(), fld.get_full_name(), rm.mbox_fn_state_sigs, state_nxt), UVM_FULL)
        end
        else if (error.axs_incorrect_order && rm.mbox_lock.lock.get_mirrored_value() && !rm.mbox_unlock.unlock.get_mirrored_value()) begin
            uvm_reg_block top;
            uvm_reg_field intr_fld;
            uvm_reg_field non_fatal_fld;

            top           = rm.get_parent();
            intr_fld      = top.get_block_by_name("soc_ifc_reg_rm").get_block_by_name("intr_block_rf_ext").get_field_by_name("error_cmd_fail_sts");
            non_fatal_fld = top.get_block_by_name("soc_ifc_reg_rm").get_reg_by_name("CPTRA_HW_ERROR_NON_FATAL").get_field_by_name("mbox_prot_ooo");

            intr_fld     .predict(1'b1, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map.get_parent().get_map_by_name("soc_ifc_AHB_map")));
            non_fatal_fld.predict(1'b1, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));

            rm.mbox_status.mbox_fsm_ps.predict(state_nxt, .kind(UVM_PREDICT_READ), .path(UVM_PREDICT), .map(map));
            `uvm_info("SOC_IFC_REG_DELAY_JOB", $sformatf("delay_job scheduled for access through map [%p] on [%s] results in state transition. Functional state tracker: [%p] mbox_fsm_ps transition [%p]", map.get_name(), fld.get_full_name(), rm.mbox_fn_state_sigs, state_nxt), UVM_FULL)
        end
    endtask
endclass
