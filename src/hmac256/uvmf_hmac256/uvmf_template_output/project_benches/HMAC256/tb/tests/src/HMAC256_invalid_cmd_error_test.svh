//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// Description: HMAC256_invalid_cmd_error_test
//   Factory-overrides HMAC256_bench_sequence_base with
//   HMAC256_invalid_cmd_error_sequence so the bench exercises both
//   LAST-alone and RESTORE-alone illegal commands.
//----------------------------------------------------------------------

class HMAC256_invalid_cmd_error_test extends test_top;

  `uvm_component_utils(HMAC256_invalid_cmd_error_test)

  function new(string name = "HMAC256_invalid_cmd_error_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    HMAC256_bench_sequence_base::type_id::set_type_override(
      HMAC256_invalid_cmd_error_sequence::get_type());
    super.build_phase(phase);
  endfunction

endclass
