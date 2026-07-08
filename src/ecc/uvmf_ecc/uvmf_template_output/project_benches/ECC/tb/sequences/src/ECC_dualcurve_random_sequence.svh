//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// Random legal (curve x op x rand_k_en) mix. Closes cmd_x_curve_cp,
// sign_illegal_matrix_cp[legal cells], and curve_transition_cp (all
// four prev->curr combinations). Never fires an error gate.
//----------------------------------------------------------------------

`ifndef __ECC_DUALCURVE_RANDOM_SEQUENCE
`define __ECC_DUALCURVE_RANDOM_SEQUENCE

`include "uvm_macros.svh"

class ECC_dualcurve_random_sequence #(int AHB_DATA_WIDTH = 64,
                                      int AHB_ADDR_WIDTH = 32
                                      ) extends ECC_bench_sequence_base;

  `uvm_object_utils(ECC_dualcurve_random_sequence)

  typedef ECC_in_random_multiaxis_sequence #(AHB_DATA_WIDTH, AHB_ADDR_WIDTH) axis_seq_t;
  axis_seq_t axis_s;

  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual task body();
    fork
      ECC_in_agent_config.wait_for_reset();
      ECC_out_agent_config.wait_for_reset();
    join

    // 20 transactions with err_mode pinned to NONE and pollute_upper=1 to
    // guarantee routing through the random path (never the legacy KAT-
    // compare path). Everything else is free within the legality
    // constraints in the transaction.
    repeat (20) begin
      axis_s = axis_seq_t::type_id::create("axis_s");
      axis_s.pin_err_mode  = 1'b1;
      axis_s.bias_err_mode = ERR_NONE;
      axis_s.pin_test      = 1'b1;
      axis_s.bias_test     = ecc_normal_test;
      axis_s.pin_pollute   = 1'b1;
      axis_s.bias_pollute_upper = 1'b1;
      axis_s.start(ECC_in_agent_sequencer);
    end

    fork
      ECC_in_agent_config.wait_for_num_clocks(400);
      ECC_out_agent_config.wait_for_num_clocks(400);
    join
    $display("* TESTCASE PASSED");
  endtask

endclass : ECC_dualcurve_random_sequence

`endif
