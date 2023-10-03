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
// DESCRIPTION: This class records cptra_status transaction information using
//       a covergroup named cptra_status_transaction_cg.  An instance of this
//       coverage component is instantiated in the uvmf_parameterized_agent
//       if the has_coverage flag is set.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
covergroup cptra_status_transaction_bit_cg with function sample(input bit val);
  option.per_instance = 1;
  ea_bit: coverpoint val;
endgroup

class cptra_status_transaction_coverage  extends uvm_subscriber #(.T(cptra_status_transaction ));

  `uvm_component_utils( cptra_status_transaction_coverage )

  T coverage_trans;

  // pragma uvmf custom class_item_additional begin
  cptra_status_transaction_bit_cg cptra_obf_key_reg_bit_cg[`CLP_OBF_KEY_DWORDS-1:0] [31:0];
  cptra_status_transaction_bit_cg obf_field_entropy_bit_cg[`CLP_OBF_FE_DWORDS -1:0] [31:0];
  cptra_status_transaction_bit_cg obf_uds_seed_bit_cg     [`CLP_OBF_UDS_DWORDS-1:0] [31:0];
  // pragma uvmf custom class_item_additional end
  
  // ****************************************************************************
  covergroup cptra_status_transaction_cg;
    // pragma uvmf custom covergroup begin
    // UVMF_CHANGE_ME : Add coverage bins, crosses, exclusions, etc. according to coverage needs.
    option.auto_bin_max=1024;
    option.per_instance=1;
    soc_ifc_err_intr_pending: coverpoint coverage_trans.soc_ifc_err_intr_pending;
    soc_ifc_err_intr_transition: coverpoint coverage_trans.soc_ifc_err_intr_pending {
        bins rise = (0 => 1);
        bins fall = (1 => 0);
    }
    soc_ifc_notif_intr_pending: coverpoint coverage_trans.soc_ifc_notif_intr_pending;
    soc_ifc_notif_intr_transition: coverpoint coverage_trans.soc_ifc_notif_intr_pending {
        bins rise = (0 => 1);
        bins fall = (1 => 0);
    }
    sha_err_intr_pending: coverpoint coverage_trans.sha_err_intr_pending;
    sha_err_intr_transition: coverpoint coverage_trans.sha_err_intr_pending {
        bins rise = (0 => 1);
        bins fall = (1 => 0);
    }
    sha_notif_intr_pending: coverpoint coverage_trans.sha_notif_intr_pending;
    sha_notif_intr_transition: coverpoint coverage_trans.sha_notif_intr_pending {
        bins rise = (0 => 1);
        bins fall = (1 => 0);
    }
    timer_intr_pending: coverpoint coverage_trans.timer_intr_pending;
    timer_intr_transition: coverpoint coverage_trans.timer_intr_pending {
        bins rise = (0 => 1);
        bins fall = (1 => 0);
    }
    noncore_rst_asserted: coverpoint coverage_trans.noncore_rst_asserted;
    noncore_rst_transition: coverpoint coverage_trans.noncore_rst_asserted {
        bins rise = (0 => 1);
        bins fall = (1 => 0);
    }
    uc_rst_asserted: coverpoint coverage_trans.uc_rst_asserted;
    uc_rst_transition: coverpoint coverage_trans.uc_rst_asserted {
        bins rise = (0 => 1);
        bins fall = (1 => 0);
    }
    fw_update_rst_window: coverpoint coverage_trans.fw_update_rst_window;
    fw_update_rst_window_transition: coverpoint coverage_trans.fw_update_rst_window {
        bins rise = (0 => 1);
        bins fall = (1 => 0);
    }
    cptra_obf_key_reg: coverpoint coverage_trans.cptra_obf_key_reg {
        bins zero_key  = {0};
        bins rand_key  = {[1:{`CLP_OBF_KEY_DWORDS{32'hFFFF_FFFF}}-1]};
        bins ones_key  = {{`CLP_OBF_KEY_DWORDS{32'hFFFF_FFFF}}};
    }
    obf_field_entropy: coverpoint coverage_trans.obf_field_entropy {
        bins zero_fe  = {0};
        bins rand_fe  = {[1:{`CLP_OBF_FE_DWORDS{32'hFFFF_FFFF}}-1]};
        bins ones_fe  = {{`CLP_OBF_FE_DWORDS{32'hFFFF_FFFF}}};
    }
    obf_uds_seed: coverpoint coverage_trans.obf_uds_seed {
        bins zero_uds  = {0};
        bins rand_uds  = {[1:{`CLP_OBF_UDS_DWORDS{32'hFFFF_FFFF}}-1]};
        bins ones_uds  = {{`CLP_OBF_UDS_DWORDS{32'hFFFF_FFFF}}};
    }
    nmi_vector: coverpoint coverage_trans.nmi_vector {
                 bins zero = {32'h0};
        wildcard bins rom  = {32'h0000_????};
        wildcard bins iccm = {32'h400?_????};
        wildcard bins set  = (32'h0000_0000 => 32'h400?_????);
        wildcard bins clr  = (32'h400?_???? => 32'h0000_0000);
    }
    nmi_intr_pending: coverpoint coverage_trans.nmi_intr_pending;
    nmi_intr_transition: coverpoint coverage_trans.nmi_intr_pending {
        bins rise = (0 => 1);
        bins fall = (1 => 0);
    }
    iccm_locked: coverpoint coverage_trans.iccm_locked;
    iccm_locked_transition: coverpoint coverage_trans.iccm_locked {
        bins rise = (0 => 1);
        bins fall = (1 => 0);
    }
    // pragma uvmf custom covergroup end
  endgroup

  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new(string name="", uvm_component parent=null);
    super.new(name,parent);
    cptra_status_transaction_cg=new;
    foreach (coverage_trans.cptra_obf_key_reg[dw,bt]) cptra_obf_key_reg_bit_cg[dw][bt] = new;
    foreach (coverage_trans.obf_field_entropy[dw,bt]) obf_field_entropy_bit_cg[dw][bt] = new;
    foreach (coverage_trans.obf_uds_seed     [dw,bt]) obf_uds_seed_bit_cg     [dw][bt] = new;
  endfunction

  // ****************************************************************************
  // FUNCTION : build_phase()
  // This function is the standard UVM build_phase.
  //
  function void build_phase(uvm_phase phase);
    cptra_status_transaction_cg.set_inst_name($sformatf("cptra_status_transaction_cg_%s",get_full_name()));
    foreach (coverage_trans.cptra_obf_key_reg[dw,bt]) cptra_obf_key_reg_bit_cg[dw][bt].set_inst_name($sformatf("cptra_obf_key_reg_bit_cg_%d_%d_%s",dw, bt, get_full_name()));
    foreach (coverage_trans.obf_field_entropy[dw,bt]) obf_field_entropy_bit_cg[dw][bt].set_inst_name($sformatf("obf_field_entropy_bit_cg_%d_%d_%s",dw, bt, get_full_name()));
    foreach (coverage_trans.obf_uds_seed     [dw,bt]) obf_uds_seed_bit_cg     [dw][bt].set_inst_name($sformatf("obf_uds_seed_bit_cg_%d_%d_%s",dw, bt, get_full_name()));
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
    cptra_status_transaction_cg.sample();
    foreach (coverage_trans.cptra_obf_key_reg[dw,bt]) cptra_obf_key_reg_bit_cg[dw][bt].sample(coverage_trans.cptra_obf_key_reg[dw][bt]);
    foreach (coverage_trans.obf_field_entropy[dw,bt]) obf_field_entropy_bit_cg[dw][bt].sample(coverage_trans.obf_field_entropy[dw][bt]);
    foreach (coverage_trans.obf_uds_seed     [dw,bt]) obf_uds_seed_bit_cg     [dw][bt].sample(coverage_trans.obf_uds_seed     [dw][bt]);
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

