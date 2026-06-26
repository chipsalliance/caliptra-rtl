//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//----------------------------------------------------------------------
// Description: HMAC_random_sequence
//   Self-checking RAL-based stim for the HMAC block. MODE and message
//   length are randomized; KEY, BLOCK[], LFSR_SEED are randomized.
//   After CTRL.LAST + STATUS.READY, TAG is read via RAL and compared
//   against the value produced by src/hmac/tb/test_gen.py (openssl
//   HMAC reference, shared with the standalone TB).
//----------------------------------------------------------------------

class HMAC_random_sequence extends HMAC_bench_sequence_base;

  `uvm_object_utils(HMAC_random_sequence)

  // Random ops driven per sim (matches uvmf_2022 repeat(10) + repeat(5)).
  localparam int unsigned NUM_OPS = 15;
  // Per-mode filenames the shared src/hmac/tb/test_gen.py uses.
  // The Python script generates one of these and writes the matching
  // expected_hmac{384,512}_tag.txt depending on which input is present.
  localparam string PY_INPUT_384  = "hmac384_uvm_test_vector.txt";
  localparam string PY_INPUT_512  = "hmac512_uvm_test_vector.txt";
  localparam string PY_OUTPUT_384 = "expected_hmac384_tag.txt";
  localparam string PY_OUTPUT_512 = "expected_hmac512_tag.txt";

  rand bit [3:0] block_length;
  constraint c_block_length { block_length > 0; }
  rand bit       mode;  //   mode = 1'b1 -> HMAC-512 mode = 1'b0 -> HMAC-384
  bit [31:0] key_dwords   [16];
  bit [31:0] block_dwords [];  

  function new(string name = "HMAC_random_sequence");
    super.new(name);
  endfunction

  // ----------------------------------------------------------------
  // Write the openssl reference's input file. src/hmac/tb/test_gen.py
  // expects per-mode files:
  //   hmac384_uvm_test_vector.txt -> KEY = <hex> / SEED = <hex> / BLOCK = <hex>
  //   hmac512_uvm_test_vector.txt -> same format
  // It parses lines as: "KEY = ", "SEED = ", anything else => msg dword
  // (strips first 8 chars to skip "BLOCK = ").  msg passed to openssl
  // is real message bytes only (openssl re-pads).
  // ----------------------------------------------------------------
  function void write_predictor_input(input int block_length);
    int          fd;
    int unsigned msg_blocks    = block_length - 1;
    int unsigned key_dwords_n  = mode ? 16 : 12;
    string       key_hex       = "";
    string       msg_hex       = "";
    string       fname         = mode ? PY_INPUT_512 : PY_INPUT_384;
    for (int i = 0; i < key_dwords_n; i++)
      key_hex = {key_hex, $sformatf("%08x", key_dwords[i])};
    fd = $fopen(fname, "w");
    if (fd == 0) begin
      `uvm_fatal("HMAC_RAND",
                 $sformatf("cannot open %s for write", fname))
    end
    $fwrite(fd, "KEY = %s\n",  key_hex);
    $fwrite(fd, "SEED = 0\n");
    // Real message blocks only -- one BLOCK = <hex> line per raw SHA
    // block.  The synthesized FIPS padding block is intentionally
    // skipped so openssl can do its own padding.
    for (int blk = 0; blk < msg_blocks; blk++) begin
      msg_hex = "";
      for (int i = 0; i < BENCH_BLOCK_DWORDS; i++)
        msg_hex = {msg_hex, $sformatf("%08x", block_dwords[blk * BENCH_BLOCK_DWORDS + i])};
      $fwrite(fd, "BLOCK = %s\n", msg_hex);
    end
    $fclose(fd);
  endfunction

  // ----------------------------------------------------------------
  // Read the openssl reference's output file. Format:
  //   TAG = <96 hex chars (HMAC-384) or 128 hex chars (HMAC-512)>
  // ----------------------------------------------------------------
  function void read_predictor_output(output bit [31:0] tag [16]);
    int        fd;
    string     line;
    string     hex;
    bit [31:0] dword;
    int        code;
    string     fname = mode ? PY_OUTPUT_512 : PY_OUTPUT_384;
    fd = $fopen(fname, "r");
    if (fd == 0) begin
      `uvm_fatal("HMAC_RAND",
                 $sformatf("cannot open %s for read", fname))
    end
    while (!$feof(fd)) begin
      void'($fgets(line, fd));
      if (line.len() >= 6 && line.substr(0,3) == "TAG ") begin
        hex = line.substr(6, line.len()-2);
        for (int i = 0; i < 16; i++) begin
          if ((i*8 + 7) >= hex.len()) break;
          code = $sscanf(hex.substr(i*8, i*8 + 7), "%h", dword);
          tag[i] = dword;
        end
      end
    end
    $fclose(fd);
  endfunction

  // ----------------------------------------------------------------
  // body -- runs NUM_OPS independent random HMAC ops per sim.
  // ----------------------------------------------------------------
  virtual task body();
    bit [31:0] read_data;
    bit [31:0] actual_tag   [16];
    bit [31:0] expected_tag [16];

    fork
      hmac_rst_agent_config.wait_for_reset();
    join
    reg_model.reset();

    for (int op_i = 0; op_i < NUM_OPS; op_i++) begin

    if (!this.randomize())
      `uvm_fatal("HMAC_RAND", "randomize() failed -- check block_length / mode constraints")

    block_dwords = new[block_length * 32];

    `uvm_info("HMAC_RAND",
      $sformatf("Op %0d/%0d: MODE=%s, block_length=%0d",
                op_i + 1, NUM_OPS,
                mode ? "HMAC-512" : "HMAC-384", block_length), UVM_LOW)

    wait_for_status(32'h1, "READY", read_data);

    // KEY (16 dwords = 512 bits).
    foreach (reg_model.HMAC512_KEY[i]) begin
      key_dwords[i] = $urandom();
      reg_model.HMAC512_KEY[i].write(status, key_dwords[i]);
    end

    // LFSR seed (6 dwords). 
    foreach (reg_model.HMAC512_LFSR_SEED[i]) begin
      reg_model.HMAC512_LFSR_SEED[i].write(status, $urandom());
    end

    // Drive each block. CTRL bit layout from src/hmac/rtl/hmac_reg.rdl:
    //   [0]=INIT [1]=NEXT [3]=MODE [5]=LAST
    // BLOCK[] layout for block_length=B:
    //   BLOCK[0..B-2] : random message bytes (only present if B>1)
    //   BLOCK[B-1]   : FIPS-180 padding {1'b1, zeros, 128-bit length}
    // pad_len_bits = B * 1024 (K_ipad block + (B-1) message blocks).
    begin
      int unsigned msg_blocks    = block_length - 1;
      int unsigned pad_len_bits  = block_length * 1024;
      int unsigned pad_blk_base  = msg_blocks * 32;

      for (int i = 0; i < msg_blocks * 32; i++) begin
        block_dwords[i] = $urandom();
      end
      block_dwords[pad_blk_base]      = 32'h8000_0000;
      for (int i = 1; i < 31; i++) begin
        block_dwords[pad_blk_base + i] = 32'h0;
      end
      block_dwords[pad_blk_base + 31] = pad_len_bits;
    end

    run_blocks(block_dwords,
               .start_idx(0),
               .end_idx(block_length - 1),
               .total_blocks(block_length),
               .restore_first(1'b0),
               .mode_bit(mode),
               .wait_last(1'b1));

    // Read TAG[0..15] via RAL.
    foreach (reg_model.HMAC512_TAG[i]) begin
      reg_model.HMAC512_TAG[i].read(status, actual_tag[i]);
    end

    // Compute the expected TAG using openssl via shared Python helper
    // (src/hmac/tb/test_gen.py — same script the standalone TB uses).
    write_predictor_input(block_length);
    void'($system("python3 ${CALIPTRA_ROOT}/src/hmac/tb/test_gen.py"));
    read_predictor_output(expected_tag);

    // Compare. HMAC-384 produces a 12-dword (384-bit) TAG; the upper
    // four TAG dwords are undefined in 384 mode. HMAC-512 fills all
    // 16 dwords. 
    begin
      int unsigned tag_dwords = mode ? 16 : 12;
      for (int i = 0; i < tag_dwords; i++) begin
        if (actual_tag[i] !== expected_tag[i]) begin
          `uvm_error("HMAC_RAND_CHECK",
            $sformatf("Op %0d TAG[%0d] mismatch: actual=%08h expected=%08h",
                      op_i + 1, i, actual_tag[i], expected_tag[i]))
        end
      end
    end
    `uvm_info("HMAC_RAND_CHECK",
      $sformatf("Op %0d/%0d TAG comparison done", op_i + 1, NUM_OPS), UVM_LOW)

    end // for op_i

    fork
      hmac_rst_agent_config.wait_for_num_clocks(200);
    join

    `uvm_info("HMAC_RAND",
      $sformatf("HMAC_random_sequence complete (%0d ops)", NUM_OPS), UVM_LOW)
    $display("* TESTCASE PASSED");
  endtask

endclass
