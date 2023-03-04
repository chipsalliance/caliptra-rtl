//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: This file contains the top level sequence used in  example_derived_test.
// It is an example of a sequence that is extended from %(benchName)_bench_sequence_base
// and can override %(benchName)_bench_sequence_base.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class example_derived_test_sequence extends ECC_bench_sequence_base;

  `uvm_object_utils( example_derived_test_sequence );

  function new(string name = "" );
    super.new(name);
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

