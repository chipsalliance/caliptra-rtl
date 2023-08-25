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
// DESCRIPTION: This class records mbox_sram transaction information using
//       a covergroup named mbox_sram_transaction_cg.  An instance of this
//       coverage component is instantiated in the uvmf_parameterized_agent
//       if the has_coverage flag is set.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
covergroup mbox_sram_transaction_bit_cg with function sample(input bit val);
  option.per_instance = 1;
  ea_bit: coverpoint val;
endgroup

class mbox_sram_transaction_coverage  extends uvm_subscriber #(.T(mbox_sram_transaction ));

  `uvm_component_utils( mbox_sram_transaction_coverage )

  T coverage_trans;

  // pragma uvmf custom class_item_additional begin
  mbox_sram_transaction_bit_cg address_bit_cg[MBOX_ADDR_W];
  mbox_sram_transaction_bit_cg data_bit_cg[MBOX_DATA_W];
  mbox_sram_transaction_bit_cg data_ecc_bit_cg[MBOX_ECC_DATA_W];
  // pragma uvmf custom class_item_additional end
  
  // ****************************************************************************
  covergroup mbox_sram_transaction_cg;
    // pragma uvmf custom covergroup begin
    // UVMF_CHANGE_ME : Add coverage bins, crosses, exclusions, etc. according to coverage needs.
    option.auto_bin_max=1024;
    option.per_instance=1;
    is_read: coverpoint coverage_trans.is_read;
    address: coverpoint coverage_trans.address;
    data: coverpoint coverage_trans.data;
    data_ecc: coverpoint coverage_trans.data_ecc;
    ecc_single_bit_error: coverpoint coverage_trans.ecc_single_bit_error;
    ecc_double_bit_error: coverpoint coverage_trans.ecc_double_bit_error;
    // TODO add checks for ecc single/double errors, address='0, address='1, address alignment cases
    // TODO add cross for read transaction, write transaction
    // pragma uvmf custom covergroup end
  endgroup

  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new(string name="", uvm_component parent=null);
    super.new(name,parent);
    mbox_sram_transaction_cg=new;
    foreach (coverage_trans.address[bt]) address_bit_cg[bt] = new;
    foreach (coverage_trans.data[bt]) data_bit_cg[bt] = new;
    foreach (coverage_trans.data_ecc[bt]) data_ecc_bit_cg[bt] = new;
  endfunction

  // ****************************************************************************
  // FUNCTION : build_phase()
  // This function is the standard UVM build_phase.
  //
  function void build_phase(uvm_phase phase);
    mbox_sram_transaction_cg.set_inst_name($sformatf("mbox_sram_transaction_cg_%s",get_full_name()));
    foreach (coverage_trans.address[bt])  address_bit_cg[bt].set_inst_name($sformatf("address_bit_cg_%d_%s", bt, get_full_name()));
    foreach (coverage_trans.data[bt])     data_bit_cg[bt].set_inst_name($sformatf("data_bit_cg_%d_%s", bt, get_full_name()));
    foreach (coverage_trans.data_ecc[bt]) data_ecc_bit_cg[bt].set_inst_name($sformatf("data_ecc_bit_cg_%d_%s", bt, get_full_name()));
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
    mbox_sram_transaction_cg.sample();
    foreach (coverage_trans.address [bt]) address_bit_cg [bt].sample(coverage_trans.address [bt]);
    foreach (coverage_trans.data    [bt]) data_bit_cg    [bt].sample(coverage_trans.data    [bt]);
    foreach (coverage_trans.data_ecc[bt]) data_ecc_bit_cg[bt].sample(coverage_trans.data_ecc[bt]);
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

