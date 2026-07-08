//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// Back-to-back P-256 random with per-op upper-4-dword pollution.
// Targets the steady-state P-256 per-op scrub pulse
// (scrub_x_cmd_cp / curve_sel_to_p256_pulse_cp) across every legal
// cmd. Extends smoke_test_ecc_p256_back_to_back (SIGN-only) to all ops.
//----------------------------------------------------------------------

`ifndef __ECC_BACK_TO_BACK_RANDOM_SEQUENCE
`define __ECC_BACK_TO_BACK_RANDOM_SEQUENCE

`include "uvm_macros.svh"

class ECC_back_to_back_random_sequence #(int AHB_DATA_WIDTH = 64,
                                         int AHB_ADDR_WIDTH = 32
                                         ) extends ECC_bench_sequence_base;

  `uvm_object_utils(ECC_back_to_back_random_sequence)

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

    // 40 P-256 transactions with random op. Curve pinned to P-256 so
    // we stress the P-256 scrub pulse; pollute_upper always on so the
    // BFM's P-256 upper-word pollution actively tests the scrub logic.
    repeat (40) begin
      axis_s = axis_seq_t::type_id::create($sformatf("axis_s_%0d", $urandom));
      axis_s.pin_test       = 1'b1;
      axis_s.bias_test      = ecc_normal_test;
      axis_s.pin_err_mode   = 1'b1;
      axis_s.bias_err_mode  = ERR_NONE;
      axis_s.pin_curve      = 1'b1;
      axis_s.bias_curve     = ecc_curve_p256;
      axis_s.pin_pollute    = 1'b1;
      axis_s.bias_pollute_upper = 1'b1;
      axis_s.start(ECC_in_agent_sequencer);
    end

    fork
      ECC_in_agent_config.wait_for_num_clocks(400);
      ECC_out_agent_config.wait_for_num_clocks(400);
    join
    $display("* TESTCASE PASSED");
  endtask

endclass : ECC_back_to_back_random_sequence

`endif
