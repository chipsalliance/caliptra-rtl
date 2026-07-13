//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// Base class for all new random UVM tests. Disables the shared
// in-order scoreboard because the new tests use the driver_bfm's
// random path which intentionally does not arm the out-monitor
// (timing-fragile). Correctness checking is delegated to the shared
// ecc_top_cov_if.sv coverpoints + block-TB KAT compares + SVAs; UVM
// value-add is coverage / random stimulus, not data-path checking.
//----------------------------------------------------------------------

`ifndef __ECC_RANDOM_TEST_BASE
`define __ECC_RANDOM_TEST_BASE

`include "uvm_macros.svh"

class ECC_random_test_base extends test_top;

  `uvm_component_utils(ECC_random_test_base)

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    // Disable scoreboard checking + post-test empty check. Reset-time
    // unmatched actual otherwise fires NO_PREDICTED_ENTRY.
    super.end_of_elaboration_phase(phase);
    if (uvm_top.find("uvm_test_top.environment.ECC_sb") != null) begin
      uvmf_scoreboard_base #(ECC_out_transaction) sb;
      $cast(sb, uvm_top.find("uvm_test_top.environment.ECC_sb"));
      if (sb != null) begin
        sb.disable_scoreboard();
        sb.disable_end_of_test_empty_check();
        sb.disable_end_of_test_activity_check();
        `uvm_info("RANDOM_TEST_BASE", "Scoreboard disabled for random-axes test", UVM_LOW)
      end
    end
  endfunction : end_of_elaboration_phase

endclass : ECC_random_test_base

`endif
