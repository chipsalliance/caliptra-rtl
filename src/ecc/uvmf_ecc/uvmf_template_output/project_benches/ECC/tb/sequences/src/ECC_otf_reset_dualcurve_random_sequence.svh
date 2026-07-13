//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// Random OTF reset with dual-curve mix. Extends legacy
// ECC_otf_reset_test (P-384 det only) with random curve+rand_k per
// transaction. Hits curve_transition_cp {01,10} around reset points
// and validates ERR_ECC_KV_BUS_SILENT_UNDER_P256 across resets.
//----------------------------------------------------------------------

`ifndef __ECC_OTF_RESET_DUALCURVE_RANDOM_SEQUENCE
`define __ECC_OTF_RESET_DUALCURVE_RANDOM_SEQUENCE

`include "uvm_macros.svh"

class ECC_otf_reset_dualcurve_random_sequence #(int AHB_DATA_WIDTH = 64,
                                                int AHB_ADDR_WIDTH = 32
                                                ) extends ECC_bench_sequence_base;

  `uvm_object_utils(ECC_otf_reset_dualcurve_random_sequence)

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

    // 40 OTF-reset transactions, curve + op + nondet all free.
    // pollute_upper=1 forces routing through the random path (avoids
    // the timing-fragile legacy monitor).
    repeat (40) begin
      axis_s = axis_seq_t::type_id::create($sformatf("axis_s_%0d", $urandom));
      axis_s.pin_test      = 1'b1;
      axis_s.bias_test     = ecc_otf_reset_test;
      axis_s.pin_err_mode  = 1'b1;
      axis_s.bias_err_mode = ERR_NONE;
      axis_s.pin_pollute   = 1'b1;
      axis_s.bias_pollute_upper = 1'b1;
      // PCR_SIGN needs PCR data; UVMF env stubs it and PCR SIGN would hang.
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

endclass : ECC_otf_reset_dualcurve_random_sequence

`endif
