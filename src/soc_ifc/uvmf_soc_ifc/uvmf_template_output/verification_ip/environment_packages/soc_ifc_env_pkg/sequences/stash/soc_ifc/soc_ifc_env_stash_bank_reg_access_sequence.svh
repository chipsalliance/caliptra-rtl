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
// DESCRIPTION: Directed RAL register-access + data-integrity sequence for
//    the stash bank feature (RFC #673/#694). Drives the full acceptance
//    matrix documented in soc_ifc_top.sv for STASH_BANK_SLOT_DATA,
//    STASH_BANK_SOC_LOCK, STASH_END_STASH, STASH_BANK_CPTRA_LOCK and
//    STASH_BANK_STATUS - both accepted and RTL-rejected accesses - and,
//    after every single write, independently cross-checks:
//      (a) the RAL mirror immediately after the frontdoor write (this alone
//          catches a predictor bug: forwarding a write that RTL actually
//          dropped, or vice versa), and
//      (b) a fresh read-back straight from hardware (this alone catches an
//          RTL access-control bug: accepting/dropping a write it shouldn't)
//    against a ground-truth expected value this sequence tracks itself
//    (never derived from the RAL mirror), so a bug in either side is caught
//    independently instead of the two potentially masking each other.
//
//    This also drives the associated functional coverage covergroups
//    (soc_ifc_reg_covergroups.svh / soc_ifc_reg_sample.svh) via the AHB/AXI
//    register predictor + coverage subscriber, so it remains a
//    coverage-closure sequence too - now closing coverage on genuinely
//    RTL-verified state instead of (potentially) predictor-fabricated
//    state. It complements, not replaces, the bare-SV smoke tests
//    smoke_test_stash_bank[_negative|_cptra_lock|_rst], which exercise the
//    same behavioral semantics on caliptra_top_tb (a testbench with no UVM
//    RAL model, so it cannot exercise this coverage or mirror-vs-RTL check).
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_stash_bank_reg_access_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));

  `uvm_object_utils( soc_ifc_env_stash_bank_reg_access_sequence )

  caliptra_axi_user valid_axi_user;
  caliptra_axi_user bad_axi_user;
  uvm_status_e reg_sts;

  // One representative dword index per stash-bank slot (26 dwords/slot).
  localparam int NUM_SLOTS       = 8;
  localparam int DWORDS_PER_SLOT = 26;

  // Independent expected-state model, bookkept entirely by this sequence
  // (never read back from the RAL mirror), used as the single ground truth
  // that both the mirror and a fresh hardware read are compared against.
  uvm_reg_data_t expected_slot_data[int];
  bit [7:0]      expected_soc_lock   = 8'h00;
  bit            expected_end_stash  = 1'b0;
  bit            expected_cptra_lock = 1'b0;

  function new(string name = "");
    super.new(name);
    valid_axi_user = new();
    // Default addr_user ('1) matches the unprogrammed/default MBOX_PAUSER
    // entry (mbox_valid_users[] falls back to CPTRA_DEF_MBOX_VALID_AXI_USER,
    // whose reset value is all-ones), so this is a legitimate mailbox user
    // for any test that hasn't reprogrammed/locked the valid-user table.
    bad_axi_user = new();
    // Guaranteed not to collide with any programmed valid_mbox_users[] entry.
    bad_axi_user.set_addr_user(32'hCAFE_BABE);
  endfunction

  virtual task pre_body();
    super.pre_body();
    reg_model = configuration.soc_ifc_rm;
  endtask

  //--------------------------------------------------------------------
  // check_slot_write: write STASH_BANK_SLOT_DATA[idx] via AXI with the
  // given user, then verify both the RAL mirror (predictor correctness)
  // and a fresh AXI read-back (RTL correctness) against the expected
  // value this sequence is tracking. On expect_accept=0, the expected
  // value is left unchanged, so the checks assert the write had no effect.
  //--------------------------------------------------------------------
  virtual task check_slot_write(int idx, uvm_reg_data_t wdata, caliptra_axi_user user,
                                 bit expect_accept, string scenario);
    uvm_reg_data_t mirror_val, hw_val;

    reg_model.soc_ifc_reg_rm.STASH_BANK_SLOT_DATA[idx].write(
        reg_sts, wdata, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(user));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] Bus transfer failed writing STASH_BANK_SLOT_DATA[%0d] = 0x%0h",
                           scenario, idx, wdata))

    if (expect_accept) expected_slot_data[idx] = wdata;
    // Note: an unwritten key in expected_slot_data[] reads as the default
    // value (0), matching the field's reset value, so no special-casing is
    // needed for slots this sequence never wrote before.

    mirror_val = reg_model.soc_ifc_reg_rm.STASH_BANK_SLOT_DATA[idx].data.get_mirrored_value();
    if (mirror_val !== expected_slot_data[idx])
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] PREDICTOR MISMATCH: RAL mirror for STASH_BANK_SLOT_DATA[%0d] = 0x%0h after write(0x%0h, expect_accept=%0d); expected mirror 0x%0h",
                           scenario, idx, mirror_val, wdata, expect_accept, expected_slot_data[idx]))

    reg_model.soc_ifc_reg_rm.STASH_BANK_SLOT_DATA[idx].read(
        reg_sts, hw_val, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(valid_axi_user));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] Bus transfer failed reading back STASH_BANK_SLOT_DATA[%0d]", scenario, idx))
    if (hw_val !== expected_slot_data[idx])
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] RTL MISMATCH: hardware read of STASH_BANK_SLOT_DATA[%0d] = 0x%0h after write(0x%0h, expect_accept=%0d); expected 0x%0h",
                           scenario, idx, hw_val, wdata, expect_accept, expected_slot_data[idx]))
    else
      `uvm_info("STASH_BANK_REG_ACCESS_SEQ",
                $sformatf("[%s] OK: STASH_BANK_SLOT_DATA[%0d] write(0x%0h, expect_accept=%0d) -> mirror=0x%0h hw=0x%0h (both match expected 0x%0h)",
                          scenario, idx, wdata, expect_accept, mirror_val, hw_val, expected_slot_data[idx]), UVM_MEDIUM)
  endtask

  //--------------------------------------------------------------------
  // check_slot_write_ahb: attempt an AHB write to STASH_BANK_SLOT_DATA[idx]
  // (always expected to be dropped - Caliptra Access: RO), then verify
  // both the mirror and a fresh AHB read-back are unchanged.
  //--------------------------------------------------------------------
  virtual task check_slot_write_ahb(int idx, uvm_reg_data_t wdata, string scenario);
    uvm_reg_data_t mirror_val, hw_val;

    reg_model.soc_ifc_reg_rm.STASH_BANK_SLOT_DATA[idx].write(
        reg_sts, wdata, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] Bus transfer failed writing STASH_BANK_SLOT_DATA[%0d] via AHB", scenario, idx))

    mirror_val = reg_model.soc_ifc_reg_rm.STASH_BANK_SLOT_DATA[idx].data.get_mirrored_value();
    if (mirror_val !== expected_slot_data[idx])
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] PREDICTOR MISMATCH: RAL mirror for STASH_BANK_SLOT_DATA[%0d] = 0x%0h after AHB write attempt; expected unchanged 0x%0h",
                           scenario, idx, mirror_val, expected_slot_data[idx]))

    reg_model.soc_ifc_reg_rm.STASH_BANK_SLOT_DATA[idx].read(
        reg_sts, hw_val, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] Bus transfer failed reading back STASH_BANK_SLOT_DATA[%0d] via AHB", scenario, idx))
    if (hw_val !== expected_slot_data[idx])
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] RTL MISMATCH: AHB read of STASH_BANK_SLOT_DATA[%0d] = 0x%0h; expected unchanged 0x%0h (AHB write must be dropped - Caliptra Access: RO)",
                           scenario, idx, hw_val, expected_slot_data[idx]))
    else
      `uvm_info("STASH_BANK_REG_ACCESS_SEQ",
                $sformatf("[%s] OK: AHB write to STASH_BANK_SLOT_DATA[%0d] correctly dropped", scenario, idx), UVM_MEDIUM)
  endtask

  //--------------------------------------------------------------------
  // check_soc_lock_write: write STASH_BANK_SOC_LOCK (W1S) via AXI, then
  // verify both the mirror and STASH_BANK_STATUS.slot_locked (the only
  // observable view of this write-only register) against expected state.
  //--------------------------------------------------------------------
  virtual task check_soc_lock_write(bit [7:0] wbits, caliptra_axi_user user,
                                     bit expect_accept, string scenario);
    uvm_reg_data_t mirror_val, hw_status;

    reg_model.soc_ifc_reg_rm.STASH_BANK_SOC_LOCK.write(
        reg_sts, uvm_reg_data_t'(wbits), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(user));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] Bus transfer failed writing STASH_BANK_SOC_LOCK = 0x%0h", scenario, wbits))

    if (expect_accept) expected_soc_lock |= wbits; // W1S: only ever sets bits

    mirror_val = reg_model.soc_ifc_reg_rm.STASH_BANK_SOC_LOCK.lock.get_mirrored_value();
    if (mirror_val[7:0] !== expected_soc_lock)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] PREDICTOR MISMATCH: STASH_BANK_SOC_LOCK mirror = 0x%0h; expected 0x%0h",
                           scenario, mirror_val[7:0], expected_soc_lock))

    reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.read(
        reg_sts, hw_status, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(valid_axi_user));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", $sformatf("[%s] Bus transfer failed reading STASH_BANK_STATUS", scenario))
    if (reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.slot_locked.get_mirrored_value()[7:0] !== expected_soc_lock)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] RTL MISMATCH: STASH_BANK_STATUS.slot_locked = 0x%0h; expected 0x%0h",
                           scenario, reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.slot_locked.get_mirrored_value()[7:0], expected_soc_lock))
    else
      `uvm_info("STASH_BANK_REG_ACCESS_SEQ",
                $sformatf("[%s] OK: STASH_BANK_SOC_LOCK write(0x%0h, expect_accept=%0d) -> slot_locked now 0x%0h",
                          scenario, wbits, expect_accept, expected_soc_lock), UVM_MEDIUM)
  endtask

  //--------------------------------------------------------------------
  // check_soc_lock_write_ahb: attempt an AHB write to STASH_BANK_SOC_LOCK
  // (always expected to be dropped - no Caliptra access), then verify both
  // the mirror and STASH_BANK_STATUS.slot_locked (read via AHB) unchanged.
  //--------------------------------------------------------------------
  virtual task check_soc_lock_write_ahb(bit [7:0] wbits, string scenario);
    uvm_reg_data_t mirror_val, hw_status;

    reg_model.soc_ifc_reg_rm.STASH_BANK_SOC_LOCK.write(
        reg_sts, uvm_reg_data_t'(wbits), UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] Bus transfer failed writing STASH_BANK_SOC_LOCK via AHB", scenario))

    mirror_val = reg_model.soc_ifc_reg_rm.STASH_BANK_SOC_LOCK.lock.get_mirrored_value();
    if (mirror_val[7:0] !== expected_soc_lock)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] PREDICTOR MISMATCH: STASH_BANK_SOC_LOCK mirror = 0x%0h after AHB write attempt; expected unchanged 0x%0h",
                           scenario, mirror_val[7:0], expected_soc_lock))

    reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.read(
        reg_sts, hw_status, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", $sformatf("[%s] Bus transfer failed reading STASH_BANK_STATUS via AHB", scenario))
    if (reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.slot_locked.get_mirrored_value()[7:0] !== expected_soc_lock)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] RTL MISMATCH: STASH_BANK_STATUS.slot_locked (AHB) = 0x%0h; expected unchanged 0x%0h",
                           scenario, reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.slot_locked.get_mirrored_value()[7:0], expected_soc_lock))
    else
      `uvm_info("STASH_BANK_REG_ACCESS_SEQ",
                $sformatf("[%s] OK: AHB write to STASH_BANK_SOC_LOCK correctly dropped", scenario), UVM_MEDIUM)
  endtask

  //--------------------------------------------------------------------
  // check_end_stash_write: write STASH_END_STASH (W1S) via AXI, then
  // verify both the mirror and STASH_BANK_STATUS.end_stash.
  //--------------------------------------------------------------------
  virtual task check_end_stash_write(caliptra_axi_user user, bit expect_accept, string scenario);
    uvm_reg_data_t mirror_val, hw_status;

    reg_model.soc_ifc_reg_rm.STASH_END_STASH.write(
        reg_sts, uvm_reg_data_t'(1'b1), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(user));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", $sformatf("[%s] Bus transfer failed writing STASH_END_STASH", scenario))

    if (expect_accept) expected_end_stash = 1'b1;

    mirror_val = reg_model.soc_ifc_reg_rm.STASH_END_STASH.end_stash.get_mirrored_value();
    if (mirror_val[0] !== expected_end_stash)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] PREDICTOR MISMATCH: STASH_END_STASH mirror = %0d; expected %0d",
                           scenario, mirror_val[0], expected_end_stash))

    reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.read(
        reg_sts, hw_status, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(valid_axi_user));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", $sformatf("[%s] Bus transfer failed reading STASH_BANK_STATUS", scenario))
    if (reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.end_stash.get_mirrored_value()[0] !== expected_end_stash)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] RTL MISMATCH: STASH_BANK_STATUS.end_stash = %0d; expected %0d",
                           scenario, reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.end_stash.get_mirrored_value()[0], expected_end_stash))
    else
      `uvm_info("STASH_BANK_REG_ACCESS_SEQ",
                $sformatf("[%s] OK: STASH_END_STASH write(expect_accept=%0d) -> end_stash now %0d",
                          scenario, expect_accept, expected_end_stash), UVM_MEDIUM)
  endtask

  //--------------------------------------------------------------------
  // check_cptra_lock_write: write STASH_BANK_CPTRA_LOCK (W1S) via either
  // the AXI map (always expected to be dropped) or the AHB map (always
  // expected to succeed), then verify both the mirror and
  // STASH_BANK_STATUS.cptra_lock (read via AHB, which always has access).
  //--------------------------------------------------------------------
  virtual task check_cptra_lock_write(uvm_reg_map map, caliptra_axi_user user,
                                       bit expect_accept, string scenario);
    uvm_reg_data_t mirror_val, hw_status;

    if (map == reg_model.soc_ifc_AXI_map)
      reg_model.soc_ifc_reg_rm.STASH_BANK_CPTRA_LOCK.write(
          reg_sts, uvm_reg_data_t'(1'b1), UVM_FRONTDOOR, map, this, .extension(user));
    else
      reg_model.soc_ifc_reg_rm.STASH_BANK_CPTRA_LOCK.write(
          reg_sts, uvm_reg_data_t'(1'b1), UVM_FRONTDOOR, map, this);
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] Bus transfer failed writing STASH_BANK_CPTRA_LOCK via %s", scenario, map.get_name()))

    if (expect_accept) expected_cptra_lock = 1'b1;

    mirror_val = reg_model.soc_ifc_reg_rm.STASH_BANK_CPTRA_LOCK.cptra_lock.get_mirrored_value();
    if (mirror_val[0] !== expected_cptra_lock)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] PREDICTOR MISMATCH: STASH_BANK_CPTRA_LOCK mirror = %0d; expected %0d",
                           scenario, mirror_val[0], expected_cptra_lock))

    reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.read(
        reg_sts, hw_status, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", $sformatf("[%s] Bus transfer failed reading STASH_BANK_STATUS via AHB", scenario))
    if (reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.cptra_lock.get_mirrored_value()[0] !== expected_cptra_lock)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 $sformatf("[%s] RTL MISMATCH: STASH_BANK_STATUS.cptra_lock = %0d; expected %0d",
                           scenario, reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.cptra_lock.get_mirrored_value()[0], expected_cptra_lock))
    else
      `uvm_info("STASH_BANK_REG_ACCESS_SEQ",
                $sformatf("[%s] OK: STASH_BANK_CPTRA_LOCK write via %s (expect_accept=%0d) -> cptra_lock now %0d",
                          scenario, map.get_name(), expect_accept, expected_cptra_lock), UVM_MEDIUM)
  endtask

  virtual task body();
    int idx0;
    int idx_mid;
    int idx_last;
    int idx_slot1;
    uvm_reg_data_t slot_data_patterns[4] = '{32'h0000_0000, 32'hFFFF_FFFF, 32'hA5A5_A5A5, 32'h0000_0000};
    uvm_reg_data_t status_junk;

    `uvm_info("STASH_BANK_REG_ACCESS_SEQ", "Starting stash bank RAL data-integrity + coverage sequence", UVM_MEDIUM)

    idx0 = 0; // slot 0, dword 0

    // CALIPTRA_MODE_SUBSYSTEM builds implement slot 0 only (slots 1..7 are
    // permanently write-disabled regardless of PAUSER/lock state) - keep
    // the "other slot" indices inside slot 0 in that case so scenarios that
    // expect an *accepted* write still exercise real, implemented storage.
    if (configuration.subsystem_mode) begin
      idx_mid   = DWORDS_PER_SLOT - 1;  // slot 0, last dword
      idx_last  = DWORDS_PER_SLOT - 1;
      idx_slot1 = DWORDS_PER_SLOT - 1;  // rejection-only scenario; slot doesn't matter
    end
    else begin
      idx_mid   = 3 * DWORDS_PER_SLOT;                              // slot 3, dword 0
      idx_last  = (NUM_SLOTS - 1) * DWORDS_PER_SLOT + (DWORDS_PER_SLOT - 1); // slot 7, dword 25
      idx_slot1 = 1 * DWORDS_PER_SLOT;                              // slot 1, dword 0
    end

    // --- Scenario 1: normal writes, valid PAUSER, unlocked, pre-END_STASH.
    // Drives rise/fall/mixed-pattern coverage on slot 0 dword 0 and the far
    // end of the flattened array, verifying content integrity (mirror + RTL)
    // after every write.
    foreach (slot_data_patterns[pi])
      check_slot_write(idx0, slot_data_patterns[pi], valid_axi_user, 1'b1, "normal-write");
    check_slot_write(idx_last, 32'hDEAD_BEEF, valid_axi_user, 1'b1, "normal-write-last-dword");

    // --- Scenario 2: invalid PAUSER on a still-unlocked slot -> dropped;
    // the slot must retain its last successfully-written value.
    check_slot_write(idx0, 32'hBAAD_F00D, bad_axi_user, 1'b0, "invalid-pauser");

    // --- Scenario 3: AHB write attempt to the SoC/AXI-only SLOT_DATA
    // register -> dropped (Caliptra Access: RO). Exercises the AHB-side
    // predictor fix directly.
    check_slot_write_ahb(idx0, 32'h1234_5678, "ahb-write-rejected");

    // --- Scenario 4: lock slot 0 (STASH_BANK_SOC_LOCK bit 0), then verify a
    // further valid-PAUSER write to that now-locked slot is dropped.
    check_soc_lock_write(8'h01, valid_axi_user, 1'b1, "soc-lock-slot0");
    check_slot_write(idx0, 32'hFACE_FEED, valid_axi_user, 1'b0, "write-after-lock");

    // --- Scenario 5: STASH_BANK_SOC_LOCK itself is rejected under an
    // invalid PAUSER and under an AHB write attempt; slot_locked unchanged.
    check_soc_lock_write(8'hFF, bad_axi_user, 1'b0, "soc-lock-bad-pauser");
    check_soc_lock_write_ahb(8'hFF, "soc-lock-ahb-write");

    // --- Scenario 6: STASH_END_STASH. An invalid-PAUSER attempt must be
    // dropped; a valid-PAUSER write must succeed and then block further
    // slot writes AND further STASH_BANK_SOC_LOCK writes bank-wide.
    check_end_stash_write(bad_axi_user, 1'b0, "end-stash-bad-pauser");
    check_end_stash_write(valid_axi_user, 1'b1, "end-stash-set");
    check_slot_write(idx_mid, 32'hC0FF_EE00, valid_axi_user, 1'b0, "write-after-end-stash");
    check_soc_lock_write(8'h80, valid_axi_user, 1'b0, "soc-lock-after-end-stash");

    // --- Scenario 7: STASH_BANK_CPTRA_LOCK. A SoC/AXI write attempt must be
    // dropped; the Caliptra/AHB write must succeed and then permanently
    // block ALL further SoC-side stash writes bank-wide (re-verified here
    // against a slot/lock-bit not yet touched by scenario 6's END_STASH).
    check_cptra_lock_write(reg_model.soc_ifc_AXI_map, bad_axi_user, 1'b0, "cptra-lock-axi-attempt");
    check_cptra_lock_write(reg_model.soc_ifc_AHB_map, valid_axi_user, 1'b1, "cptra-lock-ahb-set");
    check_slot_write(idx_slot1, 32'h5555_5555, valid_axi_user, 1'b0, "write-after-cptra-lock");
    check_soc_lock_write(8'h02, valid_axi_user, 1'b0, "soc-lock-after-cptra-lock");

    // --- Scenario 8: STASH_BANK_STATUS is RO; a write attempt from the
    // SoC/AXI side must have no effect on any of its mirrored lock state.
    reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.write(
        reg_sts, uvm_reg_data_t'(32'hFFFF_FFFF), UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(valid_axi_user));
    // Not asserting on reg_sts here: some environments return a bus-level
    // error response for a write to a read-only register; either response
    // is acceptable as long as no state actually changed (checked below).
    reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.read(
        reg_sts, status_junk, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(valid_axi_user));
    if (reg_sts != UVM_IS_OK)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ", "[status-ro-write] Bus transfer failed reading STASH_BANK_STATUS")
    if (reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.slot_locked.get_mirrored_value()[7:0] !== expected_soc_lock ||
        reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.end_stash.get_mirrored_value()[0]     !== expected_end_stash ||
        reg_model.soc_ifc_reg_rm.STASH_BANK_STATUS.cptra_lock.get_mirrored_value()[0]    !== expected_cptra_lock)
      `uvm_error("STASH_BANK_REG_ACCESS_SEQ",
                 "[status-ro-write] MISMATCH: STASH_BANK_STATUS lock state changed after a write attempt to this RO register")
    else
      `uvm_info("STASH_BANK_REG_ACCESS_SEQ", "[status-ro-write] OK: write to RO STASH_BANK_STATUS had no effect", UVM_MEDIUM)

    `uvm_info("STASH_BANK_REG_ACCESS_SEQ", "Completed stash bank RAL data-integrity + coverage sequence", UVM_MEDIUM)
  endtask

endclass
