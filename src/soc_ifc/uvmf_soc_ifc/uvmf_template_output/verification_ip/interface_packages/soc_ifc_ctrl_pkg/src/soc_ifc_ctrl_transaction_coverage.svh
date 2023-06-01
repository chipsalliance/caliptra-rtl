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
// DESCRIPTION: This class records soc_ifc_ctrl transaction information using
//       a covergroup named soc_ifc_ctrl_transaction_cg.  An instance of this
//       coverage component is instantiated in the uvmf_parameterized_agent
//       if the has_coverage flag is set.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
covergroup soc_ifc_ctrl_transaction_bit_cg with function sample(input bit val);
  option.per_instance = 1;
  ea_bit: coverpoint val;
endgroup

class soc_ifc_ctrl_transaction_coverage  extends uvm_subscriber #(.T(soc_ifc_ctrl_transaction ));

  `uvm_component_utils( soc_ifc_ctrl_transaction_coverage )

  T coverage_trans;

  // pragma uvmf custom class_item_additional begin
  soc_ifc_ctrl_transaction_bit_cg cptra_obf_key_rand_bit_cg[`CLP_OBF_KEY_DWORDS-1:0] [31:0];
  soc_ifc_ctrl_transaction_bit_cg  generic_input_val_bit_cg[63:0]                          ;
  // pragma uvmf custom class_item_additional end
  
  // ****************************************************************************
  covergroup soc_ifc_ctrl_transaction_cg;
    // pragma uvmf custom covergroup begin
    // UVMF_CHANGE_ME : Add coverage bins, crosses, exclusions, etc. according to coverage needs.
    option.auto_bin_max=1024;
    option.per_instance=1;
    cptra_obf_key_rand: coverpoint coverage_trans.cptra_obf_key_rand {
        bins zero_key  = {0};
        bins rand_key  = {[1:{`CLP_OBF_KEY_DWORDS{32'hFFFF_FFFF}}-1]};
        bins ones_key  = {{`CLP_OBF_KEY_DWORDS{32'hFFFF_FFFF}}};
    }
    set_pwrgood: coverpoint coverage_trans.set_pwrgood;
    assert_rst: coverpoint coverage_trans.assert_rst;
    wait_cycles: coverpoint coverage_trans.wait_cycles {
        bins zero_wait  = {0};
        bins one_wait   = {1};
        bins small_wait = {[2:255]};
        bins med_wait   = {[256:1023]};
        bins large_wait = {[1024:65535]};
        bins max_wait   = {[65536:$]};
    }
    security_state: coverpoint coverage_trans.security_state;
    set_bootfsm_breakpoint: coverpoint coverage_trans.set_bootfsm_breakpoint;
    generic_input_val: coverpoint coverage_trans.generic_input_val {
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

    cross_rst : cross set_pwrgood, assert_rst;
    cross_brk : cross assert_rst, set_bootfsm_breakpoint {
        bins brkpoint_while_rst = binsof (set_bootfsm_breakpoint) with (assert_rst == 1);
    }
    // pragma uvmf custom covergroup end
  endgroup

  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new(string name="", uvm_component parent=null);
    super.new(name,parent);
    soc_ifc_ctrl_transaction_cg=new;
    foreach (coverage_trans.cptra_obf_key_rand[dw,bt]) cptra_obf_key_rand_bit_cg[dw][bt] = new;
    foreach (coverage_trans.generic_input_val[bt]     ) generic_input_val_bit_cg[bt]     = new;
  endfunction

  // ****************************************************************************
  // FUNCTION : build_phase()
  // This function is the standard UVM build_phase.
  //
  function void build_phase(uvm_phase phase);
    soc_ifc_ctrl_transaction_cg.set_inst_name($sformatf("soc_ifc_ctrl_transaction_cg_%s",get_full_name()));
    foreach (coverage_trans.cptra_obf_key_rand[dw,bt]) cptra_obf_key_rand_bit_cg[dw][bt].set_inst_name($sformatf("cptra_obf_key_rand_bit_cg_%d_%d_%s",dw, bt, get_full_name()));
    foreach (coverage_trans. generic_input_val[bt])     generic_input_val_bit_cg[bt]    .set_inst_name($sformatf( "generic_input_val_bit_cg_%d_%s",       bt, get_full_name()));
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
    soc_ifc_ctrl_transaction_cg.sample();
    foreach (coverage_trans.cptra_obf_key_rand[dw,bt]) cptra_obf_key_rand_bit_cg[dw][bt].sample(coverage_trans.cptra_obf_key_rand[dw][bt]);
    foreach (coverage_trans. generic_input_val[bt])     generic_input_val_bit_cg[bt]    .sample(coverage_trans.generic_input_val[bt]);
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

