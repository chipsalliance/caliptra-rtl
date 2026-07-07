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
//   Drive every illegal CTRL encoding covered by invalid_cmd_error in
//   hmac256.sv (LAST-alone, RESTORE-alone, INIT+NEXT, INIT+RESTORE and
//   supersets thereof). The DUT must reject each: STATUS.VALID stays
//   0 and error0_sts in error_internal_intr_r asserts. All encodings
//   collapse into the same `invalid_cmd_error -> error0_sts` path.
//----------------------------------------------------------------------

class HMAC256_invalid_cmd_error_sequence extends HMAC256_bench_sequence_base;

  `uvm_object_utils(HMAC256_invalid_cmd_error_sequence)

  typedef enum bit [2:0] {
    INVALID_LAST_ALONE,        // 4'b0100
    INVALID_RESTORE_ALONE,     // 4'b1000
    INVALID_INIT_NEXT,         // 4'b0011
    INVALID_INIT_NEXT_LAST,    // 4'b0111
    INVALID_INIT_RESTORE,      // 4'b1001
    INVALID_INIT_NEXT_RESTORE, // 4'b1011
    INVALID_INIT_LAST_RESTORE, // 4'b1101
    INVALID_ALL_FOUR           // 4'b1111
  } invalid_cmd_e;

  function new(string name = "HMAC256_invalid_cmd_error_sequence");
    super.new(name);
  endfunction

  task drive_invalid_cmd(input invalid_cmd_e kind, input string id);
    bit [31:0]      read_data;
    uvm_reg_field   target_err_field;

    foreach (reg_model.HMAC256_KEY[i])
      reg_model.HMAC256_KEY[i].write(status, $urandom());
    foreach (reg_model.HMAC256_BLOCK[i])
      reg_model.HMAC256_BLOCK[i].write(status, $urandom());

    reg_model.HMAC256_CTRL.INIT.set(1'b0);
    reg_model.HMAC256_CTRL.NEXT.set(1'b0);
    reg_model.HMAC256_CTRL.LAST.set(1'b0);
    reg_model.HMAC256_CTRL.RESTORE.set(1'b0);

    case (kind)
      INVALID_LAST_ALONE: begin
        reg_model.HMAC256_CTRL.LAST.set(1'b1);
      end
      INVALID_RESTORE_ALONE: begin
        reg_model.HMAC256_CTRL.RESTORE.set(1'b1);
      end
      INVALID_INIT_NEXT: begin
        reg_model.HMAC256_CTRL.INIT.set(1'b1);
        reg_model.HMAC256_CTRL.NEXT.set(1'b1);
      end
      INVALID_INIT_NEXT_LAST: begin
        reg_model.HMAC256_CTRL.INIT.set(1'b1);
        reg_model.HMAC256_CTRL.NEXT.set(1'b1);
        reg_model.HMAC256_CTRL.LAST.set(1'b1);
      end
      INVALID_INIT_RESTORE: begin
        reg_model.HMAC256_CTRL.INIT.set(1'b1);
        reg_model.HMAC256_CTRL.RESTORE.set(1'b1);
      end
      INVALID_INIT_NEXT_RESTORE: begin
        reg_model.HMAC256_CTRL.INIT.set(1'b1);
        reg_model.HMAC256_CTRL.NEXT.set(1'b1);
        reg_model.HMAC256_CTRL.RESTORE.set(1'b1);
      end
      INVALID_INIT_LAST_RESTORE: begin
        reg_model.HMAC256_CTRL.INIT.set(1'b1);
        reg_model.HMAC256_CTRL.LAST.set(1'b1);
        reg_model.HMAC256_CTRL.RESTORE.set(1'b1);
      end
      INVALID_ALL_FOUR: begin
        reg_model.HMAC256_CTRL.INIT.set(1'b1);
        reg_model.HMAC256_CTRL.NEXT.set(1'b1);
        reg_model.HMAC256_CTRL.LAST.set(1'b1);
        reg_model.HMAC256_CTRL.RESTORE.set(1'b1);
      end
    endcase
    target_err_field = reg_model.intr_block_rf.error_internal_intr_r.error0_sts;

    `uvm_info(id, "Writing illegal CTRL command", UVM_LOW)
    reg_model.HMAC256_CTRL.update(status);

    fork
      hmac256_rst_agent_config.wait_for_num_clocks(200);
    join

    reg_model.HMAC256_STATUS.read(status, read_data);
    if (reg_model.HMAC256_STATUS.VALID.get_mirrored_value() !== 1'b0) begin
      `uvm_error(id,
        $sformatf("STATUS.VALID asserted after invalid CTRL (status=0x%08h)",
                  read_data))
    end

    reg_model.intr_block_rf.error_internal_intr_r.read(status, read_data);
    if ((read_data >> target_err_field.get_lsb_pos()) & 32'h1) begin
      `uvm_info(id,
        $sformatf("Error bit '%s' asserted as expected (raw=0x%08h)",
                  target_err_field.get_name(), read_data), UVM_LOW)
    end else begin
      `uvm_error(id,
        $sformatf("Expected error bit '%s' not set in error_internal_intr_r (raw=0x%08h)",
                  target_err_field.get_name(), read_data))
    end

    // Clear the asserted bit by writing 1 to it.
    reg_model.intr_block_rf.error_internal_intr_r.write(status,
        32'h1 << target_err_field.get_lsb_pos());

    wait_for_status(32'h1, "READY", read_data);
  endtask

  virtual task body();
    bit [31:0] read_data;

    fork
      hmac256_rst_agent_config.wait_for_reset();
    join
    reg_model.reset();

    wait_for_status(32'h1, "READY", read_data);

    drive_invalid_cmd(INVALID_LAST_ALONE,        "HMAC256_LAST_ALONE");
    drive_invalid_cmd(INVALID_RESTORE_ALONE,     "HMAC256_RESTORE_ALONE");
    drive_invalid_cmd(INVALID_INIT_NEXT,         "HMAC256_INIT_NEXT");
    drive_invalid_cmd(INVALID_INIT_NEXT_LAST,    "HMAC256_INIT_NEXT_LAST");
    drive_invalid_cmd(INVALID_INIT_RESTORE,      "HMAC256_INIT_RESTORE");
    drive_invalid_cmd(INVALID_INIT_NEXT_RESTORE, "HMAC256_INIT_NEXT_RESTORE");
    drive_invalid_cmd(INVALID_INIT_LAST_RESTORE, "HMAC256_INIT_LAST_RESTORE");
    drive_invalid_cmd(INVALID_ALL_FOUR,          "HMAC256_ALL_FOUR");

    `uvm_info("HMAC256_INVALID_CMD",
      "HMAC256_invalid_cmd_error_sequence complete", UVM_LOW)
    $display("* TESTCASE PASSED");
  endtask

endclass
