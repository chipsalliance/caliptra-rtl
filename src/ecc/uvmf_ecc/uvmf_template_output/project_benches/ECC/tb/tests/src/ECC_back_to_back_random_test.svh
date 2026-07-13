//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// ECC_back_to_back_random_test -- factory override.
//----------------------------------------------------------------------

`ifndef __ECC_BACK_TO_BACK_RANDOM_TEST
`define __ECC_BACK_TO_BACK_RANDOM_TEST

`include "uvm_macros.svh"

class ECC_back_to_back_random_test extends ECC_random_test_base;

  `uvm_component_utils(ECC_back_to_back_random_test)

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    ECC_bench_sequence_base::type_id::set_type_override(
        ECC_back_to_back_random_sequence #(64,32)::get_type());
    super.build_phase(phase);
  endfunction : build_phase

endclass : ECC_back_to_back_random_test

`endif
