//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// Description: HMAC256_random_test
//   Replacement for the uvmf_2022 HMAC256_random_test. Factory-overrides
//   HMAC256_bench_sequence_base with HMAC256_random_sequence so the bench
//   runs our randomized HMAC256 stimulus instead of the default template.
//----------------------------------------------------------------------

class HMAC256_random_test extends test_top;

  `uvm_component_utils(HMAC256_random_test)

  function new(string name = "HMAC256_random_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    HMAC256_bench_sequence_base::type_id::set_type_override(
      HMAC256_random_sequence::get_type());
    super.build_phase(phase);
  endfunction

endclass
