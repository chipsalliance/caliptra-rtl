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
// DESCRIPTION: This class records ss_mode_ctrl transaction information using
//       a covergroup named ss_mode_ctrl_transaction_cg.  An instance of this
//       coverage component is instantiated in the uvmf_parameterized_agent
//       if the has_coverage flag is set.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class ss_mode_ctrl_transaction_coverage  extends uvm_subscriber #(.T(ss_mode_ctrl_transaction ));

  `uvm_component_utils( ss_mode_ctrl_transaction_coverage )

  T coverage_trans;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  // ****************************************************************************
  covergroup ss_mode_ctrl_transaction_cg;
    // pragma uvmf custom covergroup begin
    // UVMF_CHANGE_ME : Add coverage bins, crosses, exclusions, etc. according to coverage needs.
    option.auto_bin_max=1024;
    option.per_instance=1;
    strap_ss_caliptra_base_addr: coverpoint coverage_trans.strap_ss_caliptra_base_addr;
    strap_ss_mci_base_addr: coverpoint coverage_trans.strap_ss_mci_base_addr;
    strap_ss_recovery_ifc_base_addr: coverpoint coverage_trans.strap_ss_recovery_ifc_base_addr;
    strap_ss_external_staging_area_base_addr: coverpoint coverage_trans.strap_ss_external_staging_area_base_addr;
    strap_ss_otp_fc_base_addr: coverpoint coverage_trans.strap_ss_otp_fc_base_addr;
    strap_ss_uds_seed_base_addr: coverpoint coverage_trans.strap_ss_uds_seed_base_addr;
    strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset: coverpoint coverage_trans.strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset;
    strap_ss_num_of_prod_debug_unlock_auth_pk_hashes: coverpoint coverage_trans.strap_ss_num_of_prod_debug_unlock_auth_pk_hashes;
    strap_ss_strap_generic_0: coverpoint coverage_trans.strap_ss_strap_generic_0;
    strap_ss_strap_generic_1: coverpoint coverage_trans.strap_ss_strap_generic_1;
    strap_ss_strap_generic_2: coverpoint coverage_trans.strap_ss_strap_generic_2;
    strap_ss_strap_generic_3: coverpoint coverage_trans.strap_ss_strap_generic_3;
    strap_ss_caliptra_dma_axi_user: coverpoint coverage_trans.strap_ss_caliptra_dma_axi_user;
    ss_debug_intent: coverpoint coverage_trans.ss_debug_intent;
    // pragma uvmf custom covergroup end
  endgroup

  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new(string name="", uvm_component parent=null);
    super.new(name,parent);
    ss_mode_ctrl_transaction_cg=new;
  endfunction

  // ****************************************************************************
  // FUNCTION : build_phase()
  // This function is the standard UVM build_phase.
  //
  function void build_phase(uvm_phase phase);
    ss_mode_ctrl_transaction_cg.set_inst_name($sformatf("ss_mode_ctrl_transaction_cg_%s",get_full_name()));
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
    ss_mode_ctrl_transaction_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

