//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
//
// DESCRIPTION:
//   Shared per-transaction sequence that randomizes the new dual-curve /
//   NONDETERMINISTIC / error-injection / KV-slot axes freely (subject to the
//   built-in legality constraints in ECC_in_transaction).
//
//   Higher-level top sequences (one per new UVM test) further constrain
//   the axes via `constraint_mode(0)` + inline `randomize() with { ... }`
//   to focus on a specific coverage target.
//
//----------------------------------------------------------------------
class ECC_in_random_multiaxis_sequence #(
      int AHB_DATA_WIDTH = 64,
      int AHB_ADDR_WIDTH = 32
      )
  extends ECC_in_sequence_base #(
      .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
      .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH)
      );

  `uvm_object_param_utils(ECC_in_random_multiaxis_sequence #(
                           AHB_DATA_WIDTH,
                           AHB_ADDR_WIDTH))

  // Per-instance constraint knobs; a top-level sequence sets these
  // before start() to steer the random space.
  rand ecc_in_test_transactions bias_test;
  rand ecc_in_curve_e           bias_curve;
  rand ecc_in_op_transactions   bias_op;
  rand ecc_in_err_mode_e        bias_err_mode;
  rand bit                      bias_nondet;
  rand bit                      bias_pcr_sign;
  rand bit                      bias_kv_intf;
  rand bit                      bias_pollute_upper;
  rand bit [4:0]                bias_kv_slot;
  rand bit                      bias_zeroize_mid_op;

  // When 1'b1, the corresponding field is pinned to the bias value.
  bit pin_test         = 1'b0;
  bit pin_curve        = 1'b0;
  bit pin_op           = 1'b0;
  bit pin_err_mode     = 1'b0;
  bit pin_nondet    = 1'b0;
  bit pin_pcr_sign     = 1'b0;
  bit pin_kv_intf      = 1'b0;
  bit pin_pollute      = 1'b0;
  bit pin_kv_slot      = 1'b0;
  bit pin_zeroize      = 1'b0;

  function new(string name = "");
    super.new(name);
    bias_test            = ecc_normal_test;
    bias_curve           = ecc_curve_p384;
    bias_op              = key_sign;
    bias_err_mode        = ERR_NONE;
    bias_nondet       = 1'b0;
    bias_pcr_sign        = 1'b0;
    bias_kv_intf         = 1'b0;
    bias_pollute_upper   = 1'b0;
    bias_kv_slot         = 5'd0;
    bias_zeroize_mid_op  = 1'b0;
  endfunction

  task body();
    req = ECC_in_transaction#(
              .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
              .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH)
              )::type_id::create("req");
    start_item(req);
    if(!req.randomize() with {
      if (pin_test)      test           == local::bias_test;
      if (pin_curve)     curve          == local::bias_curve;
      if (pin_op)        op             == local::bias_op;
      if (pin_err_mode)  err_mode       == local::bias_err_mode;
      if (pin_nondet) nondet      == local::bias_nondet;
      if (pin_pcr_sign)  pcr_sign       == local::bias_pcr_sign;
      if (pin_kv_intf)   kv_intf        == local::bias_kv_intf;
      if (pin_pollute)   pollute_upper  == local::bias_pollute_upper;
      if (pin_kv_slot)   kv_slot        == local::bias_kv_slot;
      if (pin_zeroize)   zeroize_mid_op == local::bias_zeroize_mid_op;
    }) `uvm_fatal("SEQ", "ECC_in_random_multiaxis_sequence::body() randomization failed")
    `uvm_info("SEQ", {"Randomized: ", req.convert2string()}, UVM_MEDIUM)
    finish_item(req);
  endtask

endclass : ECC_in_random_multiaxis_sequence
