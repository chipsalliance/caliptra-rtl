//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// Random KV slot for the KV-error paths. Sweeps kv_slot uniformly to
// close kv_read_entry_{0,1}_cp and kv_write_entry_{kg,ecdh}_cp bins
// (fw / lower / upper / slot_23) via the two KV-under-error gates
// (kv_under_p256_invalid + kv_under_rand_k_invalid).
//----------------------------------------------------------------------

`ifndef __ECC_KV_SLOT_RANDOM_SEQUENCE
`define __ECC_KV_SLOT_RANDOM_SEQUENCE

`include "uvm_macros.svh"

class ECC_kv_slot_random_sequence #(int AHB_DATA_WIDTH = 64,
                                    int AHB_ADDR_WIDTH = 32
                                    ) extends ECC_bench_sequence_base;

  `uvm_object_utils(ECC_kv_slot_random_sequence)

  typedef ECC_in_random_multiaxis_sequence #(AHB_DATA_WIDTH, AHB_ADDR_WIDTH) axis_seq_t;
  axis_seq_t axis_s;

  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual task body();
    ecc_in_err_mode_e err_choice;

    fork
      ECC_in_agent_config.wait_for_reset();
      ECC_out_agent_config.wait_for_reset();
    join

    // 40 transactions rotating kv_slot 0..23 (fw + lower/upper KV slots)
    // and alternating err_mode between the two KV gates so both read
    // and write ctrl regs are exercised across the slot space.
    for (int i = 0; i < 40; i++) begin
      err_choice = (i[0]) ? ERR_KV_P256 : ERR_KV_RAND_K;
      axis_s = axis_seq_t::type_id::create($sformatf("axis_s_%0d", i));
      axis_s.pin_test      = 1'b1;
      axis_s.bias_test     = ecc_normal_test;
      axis_s.pin_err_mode  = 1'b1;
      axis_s.bias_err_mode = err_choice;
      axis_s.pin_kv_slot   = 1'b1;
      axis_s.bias_kv_slot  = i[4:0];   // sweeps 0..31, wraps
      axis_s.start(ECC_in_agent_sequencer);
    end

    fork
      ECC_in_agent_config.wait_for_num_clocks(400);
      ECC_out_agent_config.wait_for_num_clocks(400);
    join
    $display("* TESTCASE PASSED");
  endtask

endclass : ECC_kv_slot_random_sequence

`endif
