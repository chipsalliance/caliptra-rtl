//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// Every transaction has err_mode != NONE, uniformly weighted across the
// 8-way error space. Closes illegal-1 bins of the 5 new error gates
// (pcr_sign_under_p256_invalid_cp, rand_k_pcr_sign_illegal_cp,
// rand_k_invalid_cmd_cp, kv_under_p256_invalid_cp) and the illegal cells
// of sign_illegal_matrix_cp.
//----------------------------------------------------------------------

`ifndef __ECC_ILLEGAL_MODE_RANDOM_SEQUENCE
`define __ECC_ILLEGAL_MODE_RANDOM_SEQUENCE

`include "uvm_macros.svh"

class ECC_illegal_mode_random_sequence #(int AHB_DATA_WIDTH = 64,
                                         int AHB_ADDR_WIDTH = 32
                                         ) extends ECC_bench_sequence_base;

  `uvm_object_utils(ECC_illegal_mode_random_sequence)

  typedef ECC_in_random_multiaxis_sequence #(AHB_DATA_WIDTH, AHB_ADDR_WIDTH) axis_seq_t;
  axis_seq_t axis_s;

  // Cycle through all 7 error modes (ERR_NONE excluded) with a couple
  // of reseeds per mode to sweep the "don't care" axes.
  ecc_in_err_mode_e err_list[$] = '{ERR_PCR_P256, ERR_RAND_K_PCR,
                                    ERR_RAND_K_KEYGEN, ERR_RAND_K_VERIFY,
                                    ERR_RAND_K_SHARED, ERR_KV_P256,
                                    ERR_KV_RAND_K};

  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual task body();
    fork
      ECC_in_agent_config.wait_for_reset();
      ECC_out_agent_config.wait_for_reset();
    join

    // 14 transactions = 2 * each of the 7 err_modes. Enough to hit the
    // illegal-1 bin of every gate plus its cross with error_flag.
    foreach (err_list[i]) begin
      repeat (4) begin
        axis_s = axis_seq_t::type_id::create($sformatf("axis_s_%0d_%0d", i, $urandom));
        axis_s.pin_test      = 1'b1;
        axis_s.bias_test     = ecc_normal_test;
        axis_s.pin_err_mode  = 1'b1;
        axis_s.bias_err_mode = err_list[i];
        axis_s.pin_pollute   = 1'b1;
        axis_s.bias_pollute_upper = 1'b1;
        axis_s.start(ECC_in_agent_sequencer);
      end
    end

    fork
      ECC_in_agent_config.wait_for_num_clocks(400);
      ECC_out_agent_config.wait_for_num_clocks(400);
    join
    $display("* TESTCASE PASSED");
  endtask

endclass : ECC_illegal_mode_random_sequence

`endif
