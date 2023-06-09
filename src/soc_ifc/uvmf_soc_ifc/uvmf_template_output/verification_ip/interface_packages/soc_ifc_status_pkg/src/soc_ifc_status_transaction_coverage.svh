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
covergroup soc_ifc_status_transaction_bit_cg with function sample(input bit val);
  option.per_instance = 1;
  ea_bit: coverpoint val;
endgroup

class soc_ifc_status_transaction_coverage  extends uvm_subscriber #(.T(soc_ifc_status_transaction ));

  `uvm_component_utils( soc_ifc_status_transaction_coverage )

  T coverage_trans;

  // pragma uvmf custom class_item_additional begin
  soc_ifc_status_transaction_bit_cg  generic_output_val_bit_cg[63:0]                          ;
  // pragma uvmf custom class_item_additional end
  
  // ****************************************************************************
  covergroup soc_ifc_status_transaction_cg;
    // pragma uvmf custom covergroup begin
    // UVMF_CHANGE_ME : Add coverage bins, crosses, exclusions, etc. according to coverage needs.
    option.auto_bin_max=1024;
    option.per_instance=1;
    ready_for_fuses: coverpoint coverage_trans.ready_for_fuses;
    ready_for_fw_push: coverpoint coverage_trans.ready_for_fw_push;
    ready_for_runtime: coverpoint coverage_trans.ready_for_runtime;
    mailbox_data_avail: coverpoint coverage_trans.mailbox_data_avail;
    mailbox_flow_done: coverpoint coverage_trans.mailbox_flow_done;
    cptra_error_fatal_intr_pending: coverpoint coverage_trans.cptra_error_fatal_intr_pending;
    cptra_error_non_fatal_intr_pending: coverpoint coverage_trans.cptra_error_non_fatal_intr_pending;
    trng_req_pending: coverpoint coverage_trans.trng_req_pending;
    generic_output_val: coverpoint coverage_trans.generic_output_val {
        bins byte_none = {64'h0000_0000_0000_0000};
        bins byte_0    = {[0:$]} with ($countones(item[ 7: 0] > 0));
        bins byte_1    = {[0:$]} with ($countones(item[15: 8] > 0));
        bins byte_2    = {[0:$]} with ($countones(item[23:16] > 0));
        bins byte_3    = {[0:$]} with ($countones(item[31:24] > 0));
        bins byte_4    = {[0:$]} with ($countones(item[39:32] > 0));
        bins byte_5    = {[0:$]} with ($countones(item[47:40] > 0));
        bins byte_6    = {[0:$]} with ($countones(item[55:48] > 0));
        bins byte_7    = {[0:$]} with ($countones(item[63:56] > 0));
    }

    cross_err : cross cptra_error_fatal_intr_pending, cptra_error_non_fatal_intr_pending;
    cross_req : cross mailbox_data_avail, trng_req_pending;
    // pragma uvmf custom covergroup end
  endgroup

  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new(string name="", uvm_component parent=null);
    super.new(name,parent);
    soc_ifc_status_transaction_cg=new;
    foreach (coverage_trans.generic_output_val[bt]) generic_output_val_bit_cg[bt] = new;
  endfunction

  // ****************************************************************************
  // FUNCTION : build_phase()
  // This function is the standard UVM build_phase.
  //
  function void build_phase(uvm_phase phase);
    soc_ifc_status_transaction_cg.set_inst_name($sformatf("soc_ifc_status_transaction_cg_%s",get_full_name()));
    foreach (coverage_trans.generic_output_val[bt]) generic_output_val_bit_cg[bt].set_inst_name($sformatf("generic_output_val_bit_cg_%d_%s", bt, get_full_name()));
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
    foreach (coverage_trans.generic_output_val[bt]) generic_output_val_bit_cg[bt].sample(coverage_trans.generic_output_val[bt]);
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

