//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// Description: HMAC_otf_reset_test
//   Factory-overrides HMAC_bench_sequence_base with
//   HMAC_otf_reset_sequence to exercise mid-operation reset recovery.
//----------------------------------------------------------------------

class HMAC_otf_reset_test extends test_top;

  `uvm_component_utils(HMAC_otf_reset_test)

  function new(string name = "HMAC_otf_reset_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    HMAC_bench_sequence_base::type_id::set_type_override(
      HMAC_otf_reset_sequence::get_type());
    super.build_phase(phase);
  endfunction

endclass
