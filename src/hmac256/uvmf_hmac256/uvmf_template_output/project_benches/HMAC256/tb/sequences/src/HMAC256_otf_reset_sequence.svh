//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//----------------------------------------------------------------------
// Description: HMAC256_otf_reset_sequence
//   Start an HMAC256 operation, then trigger an on-the-fly reset partway
//   through the block sequence. After the reset the DUT must come
//   back to STATUS.READY=1 cleanly, prove RAL still works, and run
//   a small follow-on operation to confirm recovery.
//----------------------------------------------------------------------

class HMAC256_otf_reset_sequence extends HMAC256_bench_sequence_base;

  `uvm_object_utils(HMAC256_otf_reset_sequence)

  uvm_event ev_rst;

  function new(string name = "HMAC256_otf_reset_sequence");
    super.new(name);
  endfunction

  virtual task body();
    bit [31:0] read_data;
    bit [31:0] ctrl_init;

    ev_rst = uvm_event_pool::get_global("ev_rst");

    fork
      hmac256_rst_agent_config.wait_for_reset();
    join
    reg_model.reset();

    wait_for_status(32'h1, "READY", read_data);

    // Kick off an HMAC-SHA-224 op with garbage KEY/BLOCK -- we only care
    // about reset recovery, not the tag.
    foreach (reg_model.HMAC256_KEY[i])
      reg_model.HMAC256_KEY[i].write(status, $urandom());
    foreach (reg_model.HMAC256_BLOCK[i])
      reg_model.HMAC256_BLOCK[i].write(status, $urandom());

    ctrl_init      = 32'h0;
    ctrl_init[0]   = 1'b1;
    reg_model.HMAC256_CTRL.write(status, ctrl_init);

    // Let the engine grind a bit, then yank reset.
    fork
      hmac256_rst_agent_config.wait_for_num_clocks(40);
    join

    `uvm_info("HMAC256_OTF", "Triggering on-the-fly reset", UVM_LOW)
    ev_rst.trigger();

    // Wait long enough for hdl_top to deassert rst and the DUT to
    // become responsive again (200 ns hold + a few clocks).
    fork
      hmac256_rst_agent_config.wait_for_num_clocks(50);
    join
    reg_model.reset();

    // Follow-on probe: STATUS.READY must come back high and RAL
    // traffic must succeed.
    wait_for_status(32'h1, "READY", read_data);
    `uvm_info("HMAC256_OTF",
      $sformatf("Post-reset STATUS recovered: 0x%08h", read_data), UVM_LOW)

    `uvm_info("HMAC256_OTF", "HMAC256_otf_reset_sequence complete", UVM_LOW)
    $display("* TESTCASE PASSED");
  endtask

endclass
