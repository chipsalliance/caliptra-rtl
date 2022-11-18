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
// DESCRIPTION: This class records soc_ifc_status transaction information using
//       a covergroup named soc_ifc_status_transaction_cg.  An instance of this
//       coverage component is instantiated in the uvmf_parameterized_agent
//       if the has_coverage flag is set.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_status_transaction_coverage  extends uvm_subscriber #(.T(soc_ifc_status_transaction ));

  `uvm_component_utils( soc_ifc_status_transaction_coverage )

  T coverage_trans;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  // ****************************************************************************
  covergroup soc_ifc_status_transaction_cg;
    // pragma uvmf custom covergroup begin
    // UVMF_CHANGE_ME : Add coverage bins, crosses, exclusions, etc. according to coverage needs.
    option.auto_bin_max=1024;
    option.per_instance=1;
    soc_ifc_err_intr_pending: coverpoint coverage_trans.soc_ifc_err_intr_pending;
    soc_ifc_notif_intr_pending: coverpoint coverage_trans.soc_ifc_notif_intr_pending;
    sha_err_intr_pending: coverpoint coverage_trans.sha_err_intr_pending;
    sha_notif_intr_pending: coverpoint coverage_trans.sha_notif_intr_pending;
    uc_rst_asserted: coverpoint coverage_trans.uc_rst_asserted;
    ready_for_fuses: coverpoint coverage_trans.ready_for_fuses;
    ready_for_fw_push: coverpoint coverage_trans.ready_for_fw_push;
    ready_for_runtime: coverpoint coverage_trans.ready_for_runtime;
    mailbox_data_avail: coverpoint coverage_trans.mailbox_data_avail;
    mailbox_flow_done: coverpoint coverage_trans.mailbox_flow_done;
    generic_output_val: coverpoint coverage_trans.generic_output_val;
    cptra_obf_key_reg: coverpoint coverage_trans.cptra_obf_key_reg;
    obf_field_entropy: coverpoint coverage_trans.obf_field_entropy;
    obf_uds_seed: coverpoint coverage_trans.obf_uds_seed;
    iccm_locked: coverpoint coverage_trans.iccm_locked;
    // pragma uvmf custom covergroup end
  endgroup

  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new(string name="", uvm_component parent=null);
    super.new(name,parent);
    soc_ifc_status_transaction_cg=new;
    `uvm_warning("COVERAGE_MODEL_REVIEW", "A covergroup has been constructed which may need review because of either generation or re-generation with merging.  Please note that transaction variables added as a result of re-generation and merging are not automatically added to the covergroup.  Remove this warning after the covergroup has been reviewed.")
  endfunction

  // ****************************************************************************
  // FUNCTION : build_phase()
  // This function is the standard UVM build_phase.
  //
  function void build_phase(uvm_phase phase);
    soc_ifc_status_transaction_cg.set_inst_name($sformatf("soc_ifc_status_transaction_cg_%s",get_full_name()));
  endfunction

  // ****************************************************************************
  // FUNCTION: write (T t)
  // This function is automatically executed when a transaction arrives on the
  // analysis_export.  It copies values from the variables in the transaction 
  // to local variables used to collect functional coverage.  
  //
  virtual function void write (T t);
    `uvm_info("COV","Received transaction",UVM_HIGH);
    coverage_trans = t;
    soc_ifc_status_transaction_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

