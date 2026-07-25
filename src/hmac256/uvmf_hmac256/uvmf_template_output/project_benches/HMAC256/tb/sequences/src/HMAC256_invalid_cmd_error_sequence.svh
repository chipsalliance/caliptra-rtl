//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//----------------------------------------------------------------------
// Description: HMAC256_invalid_cmd_error_sequence
//   Walk every 5-bit CTRL encoding {restore, last, next, init, zeroize}
//   for both HMAC256 modes (HMAC-224 and HMAC-256). For each combination:
//     - predict whether it is legal or illegal per hmac256.sv
//       invalid_cmd_error
//     - drive the CTRL beat
//     - if illegal: check STATUS.VALID stays 0 and error0_sts asserts
//     - if legal:   just kick the op, let it drain, no self-check
//   The full 32 * 2 sweep saturates hmac256_cmd_cp x mode_cp in the
//   covergroup and exercises every illegal path in the RTL.
//----------------------------------------------------------------------

class HMAC256_invalid_cmd_error_sequence extends HMAC256_bench_sequence_base;

  `uvm_object_utils(HMAC256_invalid_cmd_error_sequence)

  // CTRL field bit indices in the 5-bit cmd we sweep.
  localparam int CMD_ZEROIZE = 0;
  localparam int CMD_INIT    = 1;
  localparam int CMD_NEXT    = 2;
  localparam int CMD_LAST    = 3;
  localparam int CMD_RESTORE = 4;

  function new(string name = "HMAC256_invalid_cmd_error_sequence");
    super.new(name);
  endfunction

  // Mirrors hmac256.sv invalid_cmd_error.
  function bit is_illegal(bit [4:0] cmd);
    bit init_b    = cmd[CMD_INIT];
    bit next_b    = cmd[CMD_NEXT];
    bit last_b    = cmd[CMD_LAST];
    bit restore_b = cmd[CMD_RESTORE];
    return   (last_b    & ~init_b & ~next_b & ~restore_b)   // LAST-alone
           | (restore_b & ~next_b & ~last_b)                // RESTORE-alone
           | (init_b    & next_b)                           // INIT+NEXT
           | (init_b    & restore_b);                       // INIT+RESTORE
  endfunction

  task drive_cmd(input bit [4:0] cmd, input bit mode_bit, input string id);
    bit [31:0]      read_data;
    uvm_reg_field   target_err_field;
    bit             expect_illegal = is_illegal(cmd);

    // Randomise KEY/BLOCK for each stimulus so the DUT sees fresh data.
    foreach (reg_model.HMAC256_KEY[i])
      reg_model.HMAC256_KEY[i].write(status, $urandom());
    foreach (reg_model.HMAC256_BLOCK[i])
      reg_model.HMAC256_BLOCK[i].write(status, $urandom());

    // Set the CTRL fields explicitly.
    reg_model.HMAC256_CTRL.INIT.set(cmd[CMD_INIT]);
    reg_model.HMAC256_CTRL.NEXT.set(cmd[CMD_NEXT]);
    reg_model.HMAC256_CTRL.LAST.set(cmd[CMD_LAST]);
    reg_model.HMAC256_CTRL.RESTORE.set(cmd[CMD_RESTORE]);
    reg_model.HMAC256_CTRL.ZEROIZE.set(cmd[CMD_ZEROIZE]);
    reg_model.HMAC256_CTRL.MODE.set(mode_bit);

    target_err_field = reg_model.intr_block_rf.error_internal_intr_r.error0_sts;

    `uvm_info(id,
      $sformatf("cmd=5'b%05b mode=%0d expect_illegal=%0d",
                cmd, mode_bit, expect_illegal), UVM_LOW)
    reg_model.HMAC256_CTRL.update(status);

    fork
      hmac256_rst_agent_config.wait_for_num_clocks(200);
    join

    reg_model.HMAC256_STATUS.read(status, read_data);
    reg_model.intr_block_rf.error_internal_intr_r.read(status, read_data);

    if (expect_illegal) begin
      // STATUS.VALID must stay 0.
      if (reg_model.HMAC256_STATUS.VALID.get_mirrored_value() !== 1'b0) begin
        `uvm_error(id,
          $sformatf("STATUS.VALID asserted after invalid CTRL cmd=5'b%05b",
                    cmd))
      end
      // error0_sts must be high.
      if (((read_data >> target_err_field.get_lsb_pos()) & 32'h1) == 1'b0) begin
        `uvm_error(id,
          $sformatf("expected error0_sts high for cmd=5'b%05b (raw=0x%08h)",
                    cmd, read_data))
      end
      // Clear the error bit before the next stimulus.
      reg_model.intr_block_rf.error_internal_intr_r.write(status,
          32'h1 << target_err_field.get_lsb_pos());
    end else begin
      // Legal encoding
      hmac256_rst_agent_config.wait_for_num_clocks(50);
    end

    // Zeroize to leave the DUT in a clean state before the next stimulus.
    reg_model.HMAC256_CTRL.INIT.set(1'b0);
    reg_model.HMAC256_CTRL.NEXT.set(1'b0);
    reg_model.HMAC256_CTRL.LAST.set(1'b0);
    reg_model.HMAC256_CTRL.RESTORE.set(1'b0);
    reg_model.HMAC256_CTRL.ZEROIZE.set(1'b1);
    reg_model.HMAC256_CTRL.update(status);
    reg_model.HMAC256_CTRL.ZEROIZE.set(1'b0);

    wait_for_status(32'h1, "READY", read_data);
  endtask

  rand int unsigned num_random_stimuli;
  rand bit [4:0]    rc_cmd;
  rand bit          rc_mode;

  constraint c_num  { num_random_stimuli inside {[16:48]}; }

  virtual task body();
    bit [31:0] read_data;

    fork
      hmac256_rst_agent_config.wait_for_reset();
    join
    reg_model.reset();

    wait_for_status(32'h1, "READY", read_data);

    for (int m = 0; m < 2; m++) begin
      for (int c = 0; c < 32; c++) begin
        drive_cmd(c[4:0], m[0],
          $sformatf("HMAC256_INVALID_CMD.sweep.mode%0d.cmd%02h", m, c));
      end
    end

    if (!this.randomize(num_random_stimuli))
      `uvm_fatal("HMAC256_INVALID_CMD",
        "randomize(num_random_stimuli) failed")

    repeat (num_random_stimuli) begin
      if (!this.randomize(rc_cmd, rc_mode))
        `uvm_fatal("HMAC256_INVALID_CMD",
          "randomize(rc_cmd/rc_mode) failed")
      drive_cmd(rc_cmd, rc_mode,
        $sformatf("HMAC256_INVALID_CMD.rand.mode%0d.cmd%02h",
                  rc_mode, rc_cmd));
    end

    `uvm_info("HMAC256_INVALID_CMD",
      $sformatf("HMAC256_invalid_cmd_error_sequence complete (%0d random stimuli)",
                num_random_stimuli), UVM_LOW)
    $display("* TESTCASE PASSED");
  endtask

endclass
