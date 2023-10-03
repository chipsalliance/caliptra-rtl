//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: Sequence to initialize Caliptra SOC_IFC interrupts
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_cptra_init_interrupts_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


  `uvm_object_utils( soc_ifc_env_cptra_init_interrupts_sequence );


  uvm_status_e reg_sts;

  function new(string name = "" );
    super.new(name);

  endfunction

  virtual task body();

    uvm_reg_data_t data;
    uvm_reg_field flds[$];
    int sts_rsp_count = 0;
    reg_model = configuration.soc_ifc_rm;

    if (cptra_status_agent_rsp_seq == null)
        `uvm_fatal("CPTRA_INIT_INTR", "SOC_IFC ENV caliptra reset wait sequence expected a handle to the cptra status agent responder sequence (from bench-level sequence) but got null!")
    fork
        forever begin
            @(cptra_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    // Clear debug locked interrupt 
    data = (uvm_reg_data_t'(1) << reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_debug_locked_sts.get_lsb_pos());
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);

    // Interrupt Enable (Global)
    data = (uvm_reg_data_t'(1) << reg_model.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.error_en.get_lsb_pos()) |
           (uvm_reg_data_t'(1) << reg_model.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_lsb_pos());
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("CPTRA_INIT_INTR", $sformatf("Register access failed (%s)", "global_intr_en_r"))

    // Interrupt Enable (Errors)
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.error_intr_en_r.get_fields(flds);
    data = 0;
    foreach (flds[ii]) data |= (uvm_reg_data_t'(1) << flds[ii].get_lsb_pos());
    flds.delete();
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.error_intr_en_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("CPTRA_INIT_INTR", $sformatf("Register access failed (%s)", "error_intr_en_r"))

    // Interrupt Enable (Notifications)
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_intr_en_r.get_fields(flds);
    data = 0;
    foreach (flds[ii]) data |= (uvm_reg_data_t'(1) << flds[ii].get_lsb_pos());
    flds.delete();
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_intr_en_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("CPTRA_INIT_INTR", $sformatf("Register access failed (%s)", "notif_intr_en_r"))

  endtask

endclass
