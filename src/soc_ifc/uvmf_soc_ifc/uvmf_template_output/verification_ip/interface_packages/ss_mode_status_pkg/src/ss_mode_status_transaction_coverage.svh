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
// DESCRIPTION: This class records ss_mode_status transaction information using
//       a covergroup named ss_mode_status_transaction_cg.  An instance of this
//       coverage component is instantiated in the uvmf_parameterized_agent
//       if the has_coverage flag is set.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
covergroup ss_mode_status_transaction_bit_cg with function sample(input bit val);
  option.per_instance = 1;
  ea_bit: coverpoint val;
endgroup

class ss_mode_status_transaction_coverage  extends uvm_subscriber #(.T(ss_mode_status_transaction ));

  `uvm_component_utils( ss_mode_status_transaction_coverage )

  T coverage_trans;

  // pragma uvmf custom class_item_additional begin
  ss_mode_status_transaction_bit_cg ss_soc_dbg_unlock_level_cg[63:0];
  ss_mode_status_transaction_bit_cg ss_generic_fw_exec_ctrl_cg[127:0];
  // pragma uvmf custom class_item_additional end
  
  // ****************************************************************************
  covergroup ss_mode_status_transaction_cg;
    // pragma uvmf custom covergroup begin
    // UVMF_CHANGE_ME : Add coverage bins, crosses, exclusions, etc. according to coverage needs.
    option.auto_bin_max=1024;
    option.per_instance=1;
    cptra_ss_debug_intent: coverpoint coverage_trans.cptra_ss_debug_intent;
    cptra_ss_debug_intent_transition: coverpoint coverage_trans.cptra_ss_debug_intent {
        bins rise = (0 => 1);
        bins fall = (1 => 0);
    }
    ss_dbg_manuf_enable: coverpoint coverage_trans.ss_dbg_manuf_enable;
    ss_dbg_manuf_enable_transition: coverpoint coverage_trans.ss_dbg_manuf_enable {
        bins rise = (0 => 1);
        bins fall = (1 => 0);
    }
    ss_soc_dbg_unlock_level: coverpoint coverage_trans.ss_soc_dbg_unlock_level;
    ss_generic_fw_exec_ctrl: coverpoint coverage_trans.ss_generic_fw_exec_ctrl;
    // pragma uvmf custom covergroup end
  endgroup

  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new(string name="", uvm_component parent=null);
    super.new(name,parent);
    ss_mode_status_transaction_cg=new;
    foreach (coverage_trans.ss_soc_dbg_unlock_level[bt]) ss_soc_dbg_unlock_level_cg[bt] = new;
    foreach (coverage_trans.ss_generic_fw_exec_ctrl[bt]) ss_generic_fw_exec_ctrl_cg[bt] = new;
  endfunction

  // ****************************************************************************
  // FUNCTION : build_phase()
  // This function is the standard UVM build_phase.
  //
  function void build_phase(uvm_phase phase);
    ss_mode_status_transaction_cg.set_inst_name($sformatf("ss_mode_status_transaction_cg_%s",get_full_name()));
    foreach (coverage_trans.ss_soc_dbg_unlock_level[bt]) ss_soc_dbg_unlock_level_cg[bt].set_inst_name($sformat("ss_soc_dbg_unlock_level_cg_%d_%s",bt,get_full_name()));
    foreach (coverage_trans.ss_generic_fw_exec_ctrl[bt]) ss_generic_fw_exec_ctrl_cg[bt].set_inst_name($sformat("ss_generic_fw_exec_ctrl_cg_%d_%s",bt,get_full_name()));
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
    ss_mode_status_transaction_cg.sample();
    foreach (coverage_trans.ss_soc_dbg_unlock_level[bt]) ss_soc_dbg_unlock_level_cg[bt].sample(coverage_trans.ss_soc_dbg_unlock_level[bt]);
    foreach (coverage_trans.ss_generic_fw_exec_ctrl[bt]) ss_generic_fw_exec_ctrl_cg[bt].sample(coverage_trans.ss_generic_fw_exec_ctrl[bt]);
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

