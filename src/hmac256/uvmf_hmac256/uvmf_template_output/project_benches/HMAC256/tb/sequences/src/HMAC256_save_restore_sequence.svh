//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//----------------------------------------------------------------------
// Description: HMAC256_save_restore_sequence
//   Models the real save / restore use case: a long HMAC256 op gets
//   suspended at a random save point so a different (key, msg) pair
//   can run on the engine, then the first op is resumed via
//   CTRL.RESTORE and must finish with the same tag as if it had never
//   been interrupted.
//
//   Random shape per sim:
//     B   in [2..10]   raw SHA blocks of MSG1 
//     S   in [1..B-1]  save after S blocks (cannot save on the LAST)
//     B2  in [1..6]    raw SHA blocks of intervening MSG2
//
//   Flow:
//     1. Run KEY1/MSG1 single-shot              -> ref_tag_a
//     2. Run KEY1, drive blocks 0..S-1 (no LAST) -> save_tag (intermediate)
//     3. Run KEY2/MSG2 single-shot               -> ref_tag_b (also self-checks)
//     4. Re-write KEY1, write back save_tag,
//        drive blocks S..B-1 with NEXT|RESTORE on the first one
//                                                -> restore_tag, must == ref_tag_a
//----------------------------------------------------------------------

class HMAC256_save_restore_sequence extends HMAC256_bench_sequence_base;

  `uvm_object_utils(HMAC256_save_restore_sequence)

  rand int unsigned block_length_a;
  rand int unsigned save_point;
  rand int unsigned block_length_b;
  constraint c_a_len { block_length_a inside {[2:10]}; }
  constraint c_b_len { block_length_b inside {[1:6]};  }
  constraint c_save  { save_point > 0; save_point < block_length_a; }

  // Context A (the saved / restored op).
  bit [31:0] key_a       [16];
  bit [31:0] blocks_a    [];   // sized to block_length_a * BENCH_BLOCK_DWORDS
  bit [31:0] ref_tag_a [8];
  bit [31:0] save_tag [8];
  bit [31:0] restore_tag [8];

  // Context B (the intervening op).
  bit [31:0] key_b       [16];
  bit [31:0] blocks_b    [];   // sized to block_length_b * 32
  bit [31:0] ref_tag_b [8];
  bit [31:0] mid_tag_b [8];

  uvm_event ev_rst;

  function new(string name = "HMAC256_save_restore_sequence");
    super.new(name);
  endfunction

  // ----------------------------------------------------------------
  // Fill blocks[] for a B-block op: random message dwords for the
  // first (B-1) blocks, FIPS-180 padding tail in the last block.
  // ----------------------------------------------------------------
  function void build_random_msg(input int unsigned block_length,
                                 output bit [31:0] blocks []);
    bit [31:0] pad_blk [BENCH_BLOCK_DWORDS];
    int unsigned msg_blocks   = block_length - 1;
    int unsigned pad_blk_base = msg_blocks * BENCH_BLOCK_DWORDS;
    blocks = new[block_length * BENCH_BLOCK_DWORDS];
    for (int i = 0; i < msg_blocks * BENCH_BLOCK_DWORDS; i++)
      blocks[i] = $urandom();
    build_pad_block(block_length, pad_blk);
    for (int i = 0; i < BENCH_BLOCK_DWORDS; i++)
      blocks[pad_blk_base + i] = pad_blk[i];
  endfunction

  // ----------------------------------------------------------------
  // body
  // ----------------------------------------------------------------
  virtual task body();
    bit [31:0] read_data;
    int        mismatches_a;
    int        mismatches_b;

    ev_rst = uvm_event_pool::get_global("ev_rst");

    fork
      hmac256_rst_agent_config.wait_for_reset();
    join
    reg_model.reset();

    if (!this.randomize())
      `uvm_fatal("HMAC256_SR", "randomize() failed -- check c_a_len/c_save/c_b_len")

    foreach (key_a[i]) key_a[i] = $urandom();
    foreach (key_b[i]) key_b[i] = $urandom();
    build_random_msg(block_length_a, blocks_a);
    build_random_msg(block_length_b, blocks_b);

    `uvm_info("HMAC256_SR",
      $sformatf("Shape: A.block_length=%0d, save_point=%0d, B.block_length=%0d",
                block_length_a, save_point, block_length_b), UVM_LOW)

    // -------- Step 1: reference HMAC256 for context A --------
    `uvm_info("HMAC256_SR", "Step 1: reference HMAC256 for context A", UVM_LOW)
    wait_for_status(32'h1, "READY", read_data);
    write_key_regs(key_a);
    write_random_lfsr_seed();
    run_blocks(blocks_a,
               .start_idx(0),
               .end_idx(block_length_a - 1),
               .total_blocks(block_length_a),
               .restore_first(1'b0),
               .mode_bit(1'b1),
               .wait_last(1'b1));
    read_tag_regs(ref_tag_a);


    `uvm_info("HMAC256_SR", "Step 2: snapshot intermediate state of A", UVM_LOW)
    ev_rst.trigger();
    fork hmac256_rst_agent_config.wait_for_num_clocks(50); join
    reg_model.reset();

    wait_for_status(32'h1, "READY", read_data);
    write_key_regs(key_a);
    write_random_lfsr_seed();
    // wait_last=0 because we are pausing -- no LAST yet.
    run_blocks(blocks_a,
               .start_idx(0),
               .end_idx(save_point - 1),
               .total_blocks(block_length_a),
               .restore_first(1'b0),
               .mode_bit(1'b1),
               .wait_last(1'b0));
    read_tag_regs(save_tag);
    `uvm_info("HMAC256_SR",
      $sformatf("Saved A.TAG[0]=0x%08h A.TAG[7]=0x%08h",
                save_tag[0], save_tag[7]), UVM_LOW)

    // -------- Step 3: intervening HMAC256 for context B --------
    `uvm_info("HMAC256_SR", "Step 3: intervening HMAC256 for context B", UVM_LOW)
    wait_for_status(32'h1, "READY", read_data);
    write_key_regs(key_b);
    write_random_lfsr_seed();
    run_blocks(blocks_b,
               .start_idx(0),
               .end_idx(block_length_b - 1),
               .total_blocks(block_length_b),
               .restore_first(1'b0),
               .mode_bit(1'b1),
               .wait_last(1'b1));
    read_tag_regs(mid_tag_b);

    // Self-check B: re-run from scratch, both runs must match.
    ev_rst.trigger();
    fork hmac256_rst_agent_config.wait_for_num_clocks(50); join
    reg_model.reset();
    wait_for_status(32'h1, "READY", read_data);
    write_key_regs(key_b);
    write_random_lfsr_seed();
    run_blocks(blocks_b,
               .start_idx(0),
               .end_idx(block_length_b - 1),
               .total_blocks(block_length_b),
               .restore_first(1'b0),
               .mode_bit(1'b1),
               .wait_last(1'b1));
    read_tag_regs(ref_tag_b);

    mismatches_b = 0;
    for (int i = 0; i < 8; i++) begin
      if (mid_tag_b[i] !== ref_tag_b[i]) begin
        `uvm_error("HMAC256_SR_CHECK",
          $sformatf("B.TAG[%0d] mismatch in intervening op: got=%08h ref=%08h",
                    i, mid_tag_b[i], ref_tag_b[i]))
        mismatches_b++;
      end
    end
    if (mismatches_b == 0)
      `uvm_info("HMAC256_SR_CHECK",
        "Intervening B op self-check passed", UVM_LOW)

    // -------- Step 4: restore context A and finish MSG1 --------
    `uvm_info("HMAC256_SR", "Step 4: restore context A and finish MSG1", UVM_LOW)
    ev_rst.trigger();
    fork hmac256_rst_agent_config.wait_for_num_clocks(50); join
    reg_model.reset();

    wait_for_status(32'h1, "READY", read_data);
    write_key_regs(key_a);          // restore A's key
    write_random_lfsr_seed();
    write_tag_regs(save_tag);       // restore A's inner state
    // First CTRL writes RESTORE plus NEXT or LAST depending on
    // whether more blocks remain after the save point.
    run_blocks(blocks_a,
               .start_idx(save_point),
               .end_idx(block_length_a - 1),
               .total_blocks(block_length_a),
               .restore_first(1'b1),
               .mode_bit(1'b1),
               .wait_last(1'b1));
    read_tag_regs(restore_tag);

    // -------- Compare restored A.TAG to single-shot reference --------
    mismatches_a = 0;
    for (int i = 0; i < 8; i++) begin
      if (restore_tag[i] !== ref_tag_a[i]) begin
        `uvm_error("HMAC256_SR_CHECK",
          $sformatf("A.TAG[%0d] mismatch after restore: got=%08h ref=%08h",
                    i, restore_tag[i], ref_tag_a[i]))
        mismatches_a++;
      end
    end
    if (mismatches_a == 0)
      `uvm_info("HMAC256_SR_CHECK",
        "Restored A.TAG matches single-shot reference", UVM_LOW)

    `uvm_info("HMAC256_SR", "HMAC256_save_restore_sequence complete", UVM_LOW)
    $display("* TESTCASE PASSED");
  endtask

endclass
