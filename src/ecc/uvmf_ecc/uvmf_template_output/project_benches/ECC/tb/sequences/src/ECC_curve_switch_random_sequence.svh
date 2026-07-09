//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// Rapid curve-switch mix. Alternates curve+rand_k_en on every legal
// transaction to close curve_transition_cp {01, 10, 11, 00}, the
// scrub_x_cmd_cp per-op P-256 scrub pulse, and the RAND_K_EN latched
// vs hwif combinational gate cells. Never fires an error gate.
//----------------------------------------------------------------------

`ifndef __ECC_CURVE_SWITCH_RANDOM_SEQUENCE
`define __ECC_CURVE_SWITCH_RANDOM_SEQUENCE

`include "uvm_macros.svh"

class ECC_curve_switch_random_sequence #(int AHB_DATA_WIDTH = 64,
                                         int AHB_ADDR_WIDTH = 32
                                         ) extends ECC_bench_sequence_base;

  `uvm_object_utils(ECC_curve_switch_random_sequence)

  typedef ECC_in_random_multiaxis_sequence #(AHB_DATA_WIDTH, AHB_ADDR_WIDTH) axis_seq_t;
  axis_seq_t axis_s;

  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual task body();
    ecc_in_curve_e cur_curve;

    fork
      ECC_in_agent_config.wait_for_reset();
      ECC_out_agent_config.wait_for_reset();
    join

    // 60 transactions. Alternate curve every transaction so
    // curve_transition_cp {01, 10} fire. Op is free, rand_k_en is only
    // legal for SIGN so let the constraint solver pick. pollute_upper=1
    // forces routing through the random path (no legacy monitor).
    cur_curve = ecc_curve_p384;
    repeat (60) begin
      axis_s = axis_seq_t::type_id::create($sformatf("axis_s_%0d", $urandom));
      axis_s.pin_test      = 1'b1;
      axis_s.bias_test     = ecc_normal_test;
      axis_s.pin_err_mode  = 1'b1;
      axis_s.bias_err_mode = ERR_NONE;
      axis_s.pin_curve     = 1'b1;
      axis_s.bias_curve    = cur_curve;
      axis_s.pin_pollute   = 1'b1;
      axis_s.bias_pollute_upper = 1'b1;
      // PCR_SIGN needs a PCR data source; UVMF env stubs it. Legal
      // PCR SIGN would hang. Coverage handled by illegal_mode test.
      axis_s.pin_pcr_sign  = 1'b1;
      axis_s.bias_pcr_sign = 1'b0;
      axis_s.start(ECC_in_agent_sequencer);
      cur_curve = (cur_curve == ecc_curve_p384) ? ecc_curve_p256 : ecc_curve_p384;
    end

    // Trailing pairs of same-curve transactions to also hit
    // curve_transition_cp {00, 11}.
    for (int i = 0; i < 4; i++) begin
      axis_s = axis_seq_t::type_id::create($sformatf("axis_s_stay_%0d", i));
      axis_s.pin_test      = 1'b1; axis_s.bias_test     = ecc_normal_test;
      axis_s.pin_err_mode  = 1'b1; axis_s.bias_err_mode = ERR_NONE;
      axis_s.pin_curve     = 1'b1;
      axis_s.bias_curve    = (i < 2) ? ecc_curve_p384 : ecc_curve_p256;
      axis_s.pin_pollute   = 1'b1;
      axis_s.bias_pollute_upper = 1'b1;
      axis_s.pin_pcr_sign  = 1'b1;
      axis_s.bias_pcr_sign = 1'b0;
      axis_s.start(ECC_in_agent_sequencer);
    end

    fork
      ECC_in_agent_config.wait_for_num_clocks(400);
      ECC_out_agent_config.wait_for_num_clocks(400);
    join
    $display("* TESTCASE PASSED");
  endtask

endclass : ECC_curve_switch_random_sequence

`endif
