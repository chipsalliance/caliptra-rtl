//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// Description: HMAC_save_restore_test
//   Factory-overrides HMAC_bench_sequence_base with
//   HMAC_save_restore_sequence to exercise CTRL.RESTORE: save the
//   intermediate TAG, on-the-fly reset, write the TAG back, finish
//   the second block, and verify the final TAG matches a clean
//   single-shot reference.
//----------------------------------------------------------------------

class HMAC_save_restore_test extends test_top;

  `uvm_component_utils(HMAC_save_restore_test)

  function new(string name = "HMAC_save_restore_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    HMAC_bench_sequence_base::type_id::set_type_override(
      HMAC_save_restore_sequence::get_type());
    super.build_phase(phase);
  endfunction

endclass
