//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// Zeroize-mid-op random. Every transaction dispatches an op then fires
// ZEROIZE within N random clocks (before ready reasserts). Closes
// zeroize_ready_cp[ready=0], zeroize_x_curve_cp (both curves),
// zeroize_cmd_cp (all 4 legal cmds), zeroize_pcr_cp (PCR + non-PCR)
// bins in ecc_top_cov_if.sv.
//----------------------------------------------------------------------

`ifndef __ECC_ZEROIZE_RANDOM_SEQUENCE
`define __ECC_ZEROIZE_RANDOM_SEQUENCE

`include "uvm_macros.svh"

class ECC_zeroize_random_sequence #(int AHB_DATA_WIDTH = 64,
                                    int AHB_ADDR_WIDTH = 32
                                    ) extends ECC_bench_sequence_base;

  `uvm_object_utils(ECC_zeroize_random_sequence)

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

    // 40 transactions. err_mode pinned to NONE (zeroize + error mutually
    // exclusive per transaction constraint). zeroize_mid_op pinned to 1.
    // Curve/op/rand_k_en/pcr_sign free -> hit zeroize_x_curve_cp,
    // zeroize_cmd_cp, zeroize_pcr_cp bins across the full axis space.
    repeat (40) begin
      axis_s = axis_seq_t::type_id::create($sformatf("axis_s_%0d", $urandom));
      axis_s.pin_test           = 1'b1;
      axis_s.bias_test          = ecc_normal_test;
      axis_s.pin_err_mode       = 1'b1;
      axis_s.bias_err_mode      = ERR_NONE;
      axis_s.pin_zeroize        = 1'b1;
      axis_s.bias_zeroize_mid_op = 1'b1;
      // PCR_SIGN needs PCR data; UVMF env stubs it and PCR SIGN would hang.
      axis_s.pin_pcr_sign       = 1'b1;
      axis_s.bias_pcr_sign      = 1'b0;
      axis_s.start(ECC_in_agent_sequencer);
    end

    fork
      ECC_in_agent_config.wait_for_num_clocks(400);
      ECC_out_agent_config.wait_for_num_clocks(400);
    join
    $display("* TESTCASE PASSED");
  endtask

endclass : ECC_zeroize_random_sequence

`endif
