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
// DESCRIPTION: This class records kv_write transaction information using
//       a covergroup named kv_write_transaction_cg.  An instance of this
//       coverage component is instantiated in the uvmf_parameterized_agent
//       if the has_coverage flag is set.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

covergroup data_bit_cg(input logic data_bit);
  option.per_instance = 1;
  value: coverpoint data_bit;
  transition:  coverpoint data_bit {
    bins bin01 = (0 => 1); 
    bins bin10 = (1 => 0);
  }
endgroup

class kv_write_transaction_coverage #(
      string KV_WRITE_REQUESTOR = "HMAC"
      )
 extends uvm_subscriber #(.T(kv_write_transaction #(
                                            .KV_WRITE_REQUESTOR(KV_WRITE_REQUESTOR)
                                            )
));

  `uvm_component_param_utils( kv_write_transaction_coverage #(
                              KV_WRITE_REQUESTOR
                              )
)

  T coverage_trans;
  

  // pragma uvmf custom class_item_additional begin
  // wr_data_bit1 wr_data_bits1[32];
  // wr_data_bit0 wr_data_bits0[32];
  data_bit_cg wr_data_bus[KV_DATA_W];
  data_bit_cg dest_valid_bus[KV_NUM_READ];
    
  // pragma uvmf custom class_item_additional end
  
  // ****************************************************************************
  covergroup kv_write_transaction_cg;
    // pragma uvmf custom covergroup begin
    // UVMF_CHANGE_ME : Add coverage bins, crosses, exclusions, etc. according to coverage needs.
    option.auto_bin_max=1024;
    option.per_instance=1;
    write_en: coverpoint coverage_trans.write_en;
    write_entry: coverpoint coverage_trans.write_entry;
    write_offset: coverpoint coverage_trans.write_offset {
      illegal_bins wr_offset_12_15 = {['d12:'d15]};
    }
    error: coverpoint coverage_trans.error;
    // pragma uvmf custom covergroup end
  endgroup

  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new(string name="", uvm_component parent=null);
    super.new(name,parent);
    kv_write_transaction_cg=new;
    // key_ctrl_cg = new;
    //`uvm_warning("COVERAGE_MODEL_REVIEW", "A covergroup has been constructed which may need review because of either generation or re-generation with merging.  Please note that transaction variables added as a result of re-generation and merging are not automatically added to the covergroup.  Remove this warning after the covergroup has been reviewed.")
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
    // foreach (wr_data_bits1[i]) wr_data_bits1[i] = new(1'b1 << i, coverage_trans.write_data);
    // foreach(wr_data_bits1[i]) wr_data_bits1[i].set_inst_name($sformatf("wr_data_bits1[%0d]_%s",i,get_full_name()));

    // foreach (wr_data_bits0[i]) wr_data_bits0[i] = new(1'b1 << i, coverage_trans.write_data);
    // foreach(wr_data_bits0[i]) wr_data_bits0[i].set_inst_name($sformatf("wr_data_bits0[%0d]_%s",i,get_full_name()));

    foreach(wr_data_bus[i]) wr_data_bus[i] = new(coverage_trans.write_data[i]);
    foreach(wr_data_bus[i]) wr_data_bus[i].set_inst_name($sformatf("wr_data_bus[%0d]_%s",i,get_full_name()));

    foreach(dest_valid_bus[i]) dest_valid_bus[i] = new(coverage_trans.write_dest_valid[i]);
    foreach(dest_valid_bus[i]) dest_valid_bus[i].set_inst_name($sformatf("dest_valid_bus[%0d]_%s",i,get_full_name()));

    kv_write_transaction_cg.sample();
    //foreach(wr_data_bits1[i]) wr_data_bits1[i].sample();
    //foreach(wr_data_bits0[i]) wr_data_bits0[i].sample();
    foreach(wr_data_bus[i]) wr_data_bus[i].sample();
    foreach(dest_valid_bus[i]) dest_valid_bus[i].sample();
    // key_ctrl_cg.sample();
  endfunction

  // ****************************************************************************
  // FUNCTION : build_phase()
  // This function is the standard UVM build_phase.
  //
  function void build_phase(uvm_phase phase);
    kv_write_transaction_cg.set_inst_name($sformatf("kv_write_transaction_cg_%s",get_full_name()));
    // key_ctrl_cg.set_inst_name($sformatf("key_ctrl_cg_%s", get_full_name()));
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

