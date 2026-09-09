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
//----------------------------------------------------------------------
//
// DESCRIPTION: Directed RAL register-access sequence for the stash bank
//    feature (RFC #673/#694). Drives representative writes/reads to the
//    STASH_BANK_SLOT_DATA, STASH_BANK_SOC_LOCK, STASH_END_STASH,
//    STASH_BANK_CPTRA_LOCK and STASH_BANK_STATUS registers so that the
//    associated functional coverage covergroups (soc_ifc_reg_covergroups.svh
//    / soc_ifc_reg_sample.svh) get sampled via the AHB/AXI register
//    predictor + coverage subscriber. This is a coverage-closure sequence,
//    not a protocol/behavioral check (the bare-SV smoke tests
//    smoke_test_stash_bank[_negative|_cptra_lock|_rst] already cover the
//    behavioral semantics on caliptra_top_tb, but that testbench has no
//    UVM RAL model and therefore cannot exercise this coverage).
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_stash_bank_reg_access_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));

  `uvm_object_utils( soc_ifc_env_stash_bank_reg_access_sequence )

  caliptra_axi_user axi_user_obj;
  uvm_status_e reg_sts;

  // One representative dword index per stash-bank slot (26 dwords/slot).
  localparam int NUM_SLOTS       = 8;
  localparam int DWORDS_PER_SLOT = 26;

  function new(string name = "");
    super.new(name);
    axi_user_obj = new();
  endfunction

  virtual task pre_body();
    super.pre_body();
    reg_model = configuration.soc_ifc_rm;
  endtask

  virtual task body();
    int idx;
    uvm_reg_data_t reg_data;
    uvm_reg_data_t slot_data_patterns[4] = '{32'h0000_0000, 32'hFFFF_FFFF, 32'hA5A5_A5A5, 32'h0000_0000};

    `uvm_info("STASH_BANK_REG_ACCESS_SEQ", "Starting stash bank RAL coverage sequence", UVM_MEDIUM)

    // --- SoC/AXI side: populate representative slot-data dwords ---
    // Drive rise/fall bit transitions plus a mixed data pattern on the
    // first dword of every slot.
    for (int slot = 0; slot < NUM_SLOTS; slot++) begin
      idx = slot * DWORDS_PER_SLOT;
      foreach (slot_data_patterns[pi]) begin
        reg_model.soc_ifc_reg_rm.STASH_BANK_SLOT_DATA[idx].write(
            reg_sts, slot_data_patterns[pi], UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
        if (reg_sts != UVM_IS_OK)
          `uvm_error("STASH_BANK_REG_ACCESS_SEQ", $sformatf("Failed writing STASH_BANK_SLOT_DATA[%0d] = 0x%0h", idx, slot_data_patterns[pi]))
      end
    end
    // Also touch the last dword of the last slot, to exercise the far end
    // of the flattened 208-entry array.
    idx = (NUM_SLOTS - 1) * DWORDS_PER_SLOT + (DWORDS_PER_SLOT - 1);
    reg_model.soc_ifc_reg_rm.STASH_BANK_SLOT_DATA[idx].write(
        reg_sts, 32'hDEAD_BEEF, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", $sformatf("Failed writing STASH_BANK_SLOT_DATA[%0d]", idx))

    // --- SoC/AXI side: STASH_BANK_SOC_LOCK (W1S, 8 bits - one per slot) ---
    // Toggle 0 -> all-ones -> 0 to exercise both edge bins on every lock bit.
    reg_model.soc_ifc_reg_rm.STASH_BANK_SOC_LOCK.write(
        reg_sts, uvm_reg_data_t'(8'h00), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", "Failed writing STASH_BANK_SOC_LOCK = 0")
    reg_model.soc_ifc_reg_rm.STASH_BANK_SOC_LOCK.write(
        reg_sts, uvm_reg_data_t'(8'hFF), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", "Failed writing STASH_BANK_SOC_LOCK = 0xFF")
    reg_model.soc_ifc_reg_rm.STASH_BANK_SOC_LOCK.write(
        reg_sts, uvm_reg_data_t'(8'h00), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", "Failed writing STASH_BANK_SOC_LOCK = 0 (2nd)")

    // --- SoC/AXI side: STASH_END_STASH (WO, 1 bit) ---
    reg_model.soc_ifc_reg_rm.STASH_END_STASH.write(
        reg_sts, uvm_reg_data_t'(1'b0), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", "Failed writing STASH_END_STASH = 0")
    reg_model.soc_ifc_reg_rm.STASH_END_STASH.write(
        reg_sts, uvm_reg_data_t'(1'b1), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", "Failed writing STASH_END_STASH = 1")

    // --- Caliptra/AHB side: STASH_BANK_CPTRA_LOCK (WO, 1 bit, uC-only) ---
    reg_model.soc_ifc_reg_rm.STASH_BANK_CPTRA_LOCK.write(
        reg_sts, uvm_reg_data_t'(1'b0), UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", "Failed writing STASH_BANK_CPTRA_LOCK = 0")
    reg_model.soc_ifc_reg_rm.STASH_BANK_CPTRA_LOCK.write(
        reg_sts, uvm_reg_data_t'(1'b1), UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", "Failed writing STASH_BANK_CPTRA_LOCK = 1")

    // --- Read back STASH_BANK_STATUS from both sides to sample fld_cg ---
    reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.read(
        reg_sts, reg_data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", "Failed reading STASH_BANK_STATUS (AXI)")
    else
      `uvm_info("STASH_BANK_REG_ACCESS_SEQ", $sformatf("STASH_BANK_STATUS (AXI read) = 0x%0h", reg_data), UVM_MEDIUM)

    reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.read(
        reg_sts, reg_data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", "Failed reading STASH_BANK_STATUS (AHB)")
    else
      `uvm_info("STASH_BANK_REG_ACCESS_SEQ", $sformatf("STASH_BANK_STATUS (AHB read) = 0x%0h", reg_data), UVM_MEDIUM)

    `uvm_info("STASH_BANK_REG_ACCESS_SEQ", "Completed stash bank RAL coverage sequence", UVM_MEDIUM)
  endtask

endclass
