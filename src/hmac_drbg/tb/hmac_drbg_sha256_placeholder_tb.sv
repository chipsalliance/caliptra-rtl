// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
//======================================================================
//
// hmac_drbg_sha256_placeholder_tb.sv
//
// Self-checking testbench for HMAC-DRBG-SHA256.  Mirrors
// `hmac_drbg_tb.sv` (the SHA-384 version) but with 256-bit widths and
// KAT vectors produced by `hmac_drbg_sha256_placeholder_ref.py`.
//
//======================================================================

module hmac_drbg_sha256_placeholder_tb();

  //----------------------------------------------------------------
  // Local Parameters.
  //----------------------------------------------------------------
  localparam MAX_ROUND    = 15;
  localparam MAX_ROUND_W  = $clog2(MAX_ROUND);

  localparam REG_SIZE        = 256;
  localparam [REG_SIZE-1 : 0] GROUP_ORDER_P256 = { {(REG_SIZE-256){1'b0}}, 256'hFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551 };
  localparam [REG_SIZE-1 : 0] HMAC_DRBG_PRIME  = GROUP_ORDER_P256;

  localparam CLK_HALF_PERIOD = 1;
  localparam CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  localparam DEBUG     = 0;

  string      hmac_drbg_test_vector_file;
  string      hmac_drbg_test_to_run;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0]  cycle_ctr;
  reg [63 : 0]  error_ctr;

  reg [7 : 0]   tc_number;

  reg                        clk_tb;
  reg                        reset_n_tb;

  reg                        zeroize_tb;
  reg                        init_tb;
  reg                        next_tb;
  wire                       ready_tb;
  wire                       valid_tb;

  reg   [REG_SIZE-1 : 0]     entropy_tb;
  reg   [REG_SIZE-1 : 0]     nonce_tb;
  wire  [REG_SIZE-1 : 0]     drbg_tb;

  logic                      busy_seen;

  initial begin
    if ($value$plusargs("HMAC_DRBG_SHA256_TEST=%s", hmac_drbg_test_to_run)) begin
      $display("%m: Running hmac_drbg_sha256_placeholder test = %s", hmac_drbg_test_to_run);
    end else begin
      hmac_drbg_test_to_run = "HMAC_DRBG_SHA256_directed_test";
      $display("%m: Running hmac_drbg_sha256_placeholder test = %s", hmac_drbg_test_to_run);
    end

    if (hmac_drbg_test_to_run == "HMAC_DRBG_SHA256_directed_test") begin
      if ($value$plusargs("HMAC_DRBG_SHA256_TEST_VECTOR_FILE=%s", hmac_drbg_test_vector_file)) begin
        $display("%m: Using HMAC_DRBG_SHA256 test vectors from file specified via plusarg: %s",
                 hmac_drbg_test_vector_file);
      end else begin
        hmac_drbg_test_vector_file = "";
        $display("%m: There is no valid test vector file.");
      end
    end
  end

  typedef struct packed {
      logic [REG_SIZE-1 : 0]               entropy;
      logic [REG_SIZE-1 : 0]               nonce;
      logic [MAX_ROUND_W-1:0]              num_rounds;
      logic [MAX_ROUND-1:0][REG_SIZE-1:0]  drbg_outputs;
  } test_vector_t;

  test_vector_t test_vector;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  hmac_drbg_sha256_placeholder
  #(
        .REG_SIZE(REG_SIZE),
        .HMAC_DRBG_PRIME(HMAC_DRBG_PRIME)
  ) dut
  (
        .clk(clk_tb),
        .reset_n(reset_n_tb),
        .zeroize(zeroize_tb),
        .init_cmd(init_tb),
        .next_cmd(next_tb),
        .ready(ready_tb),
        .valid(valid_tb),
        .entropy(entropy_tb),
        .nonce(nonce_tb),
        .drbg(drbg_tb)
    );

  // Bind coverage interface.
  hmac_drbg_sha256_placeholder_cov_bind i_hmac_drbg_sha256_cov_bind();

  //----------------------------------------------------------------
  // clk_gen
  //----------------------------------------------------------------
  always begin : clk_gen
    #CLK_HALF_PERIOD;
    clk_tb = !clk_tb;
  end

  //----------------------------------------------------------------
  // sys_monitor()
  //----------------------------------------------------------------
  always begin : sys_monitor
    cycle_ctr = cycle_ctr + 1;
    #(CLK_PERIOD);
    if (DEBUG) dump_dut_state();
  end

  //----------------------------------------------------------------
  // Random helpers.
  //----------------------------------------------------------------
  function logic [REG_SIZE-1 : 0] random_gen();
    logic [REG_SIZE-1 : 0] random_seed;
    for (int i = 0; i < (REG_SIZE / 32); i++) begin
      random_seed[i*32 +: 32] = $urandom;
    end
    return random_seed;
  endfunction

  task dump_dut_state;
    begin
      $display("cycle: 0x%016x", cycle_ctr);
      $display("STATE      = 0x%02d", dut.drbg_st_reg);
      $display("HMAC block = 0x%0128x", dut.HMAC_block);
      $display("HMAC key   = 0x%064x", dut.HMAC_key);
      $display("HMAC tag   = 0x%064x", dut.HMAC_tag);
      $display("");
    end
  endtask

  task reset_dut;
    begin
      $display("*** Toggle reset.");
      reset_n_tb = 0;
      #(2 * CLK_PERIOD);
      reset_n_tb = 1;
      $display("");
    end
  endtask

  task display_test_results;
    begin
      if (error_ctr == 0) begin
        $display("*** All %02d test cases completed successfully", tc_number);
        $display("* TESTCASE PASSED");
      end else begin
        $display("*** %02d tests completed - %02d test cases did not complete successfully.",
                  tc_number, error_ctr);
        $display("* TESTCASE FAILED");
      end
    end
  endtask

  task init_sim;
    begin
      cycle_ctr   = 0;
      error_ctr   = 0;
      tc_number   = 0;
      clk_tb      = 0;
      reset_n_tb  = 1;
      zeroize_tb  = 0;
      init_tb     = 0;
      next_tb     = 0;
      entropy_tb  = '0;
      nonce_tb    = '0;
    end
  endtask

  //----------------------------------------------------------------
  // hmac256_drbg
  // Single INIT and check against `expected_drbg`.
  //----------------------------------------------------------------
  task hmac256_drbg(input [REG_SIZE-1 : 0] entropy,
                    input [REG_SIZE-1 : 0] nonce,
                    input [REG_SIZE-1 : 0] expected_drbg);
    begin
      if (!ready_tb)
        wait(ready_tb);

      $display("The HMAC DRBG SHA-256 core is triggered...");

      entropy_tb = entropy;
      nonce_tb   = nonce;

      $display("*** entropy : %064x", entropy_tb);
      $display("*** nonce   : %064x", nonce_tb);

      #(1 * CLK_PERIOD);
      init_tb = 1'b1;

      #(1 * CLK_PERIOD);
      init_tb = 1'b0;

      #(2 * CLK_PERIOD);

      wait(valid_tb);
      $display("The HMAC DRBG core completed the execution");

      if (drbg_tb == expected_drbg) begin
        $display("*** TC %0d successful.", tc_number);
        $display("");
      end else begin
        $display("*** ERROR: TC %0d NOT successful.", tc_number);
        $display("Expected: 0x%064x", expected_drbg);
        $display("Got:      0x%064x", drbg_tb);
        $display("");
        error_ctr = error_ctr + 1;
      end

      tc_number = tc_number + 1;
    end
  endtask

  //----------------------------------------------------------------
  // hmac256_drbg_multi_rounds
  // Run INIT then a sequence of NEXTs, checking each output.
  //----------------------------------------------------------------
  task hmac256_drbg_multi_rounds(input [REG_SIZE-1 : 0] entropy,
                                 input [REG_SIZE-1 : 0] nonce,
                                 input [MAX_ROUND : 0][REG_SIZE-1 : 0] expected_drbg,
                                 input [MAX_ROUND_W-1:0] num_rounds);
    begin
      if (!ready_tb)
        wait(ready_tb);

      $display("The HMAC DRBG SHA-256 multi rounds is triggered...");

      entropy_tb = entropy;
      nonce_tb   = nonce;

      $display("*** entropy : %064x", entropy_tb);
      $display("*** nonce   : %064x", nonce_tb);

      for (int i = 0; i < num_rounds; i++) begin
        #(1 * CLK_PERIOD);
        if (i == 0) begin
          init_tb = 1'b1;
          next_tb = 1'b0;
        end else begin
          init_tb = 1'b0;
          next_tb = 1'b1;
        end

        #(1 * CLK_PERIOD);
        init_tb = 1'b0;
        next_tb = 1'b0;

        #(2 * CLK_PERIOD);

        wait(valid_tb);
        $display("Received valid flag");

        if (drbg_tb == expected_drbg[i]) begin
          $display("*** TC %0d round #%0d successful.", tc_number, i);
          $display("");
        end else begin
          $display("*** ERROR: TC %0d round #%0d NOT successful.", tc_number, i);
          $display("Expected: 0x%064x", expected_drbg[i]);
          $display("Got:      0x%064x", drbg_tb);
          $display("");
          error_ctr = error_ctr + 1;
        end
      end

      tc_number = tc_number + 1;
    end
  endtask

  //----------------------------------------------------------------
  // hmac256_drbg_failure_injection
  // Force `failure_check` to '1' so the RTL takes the K3/V3 reject
  // path; then verify the next output matches the expected value.
  //----------------------------------------------------------------
  task hmac256_drbg_failure_injection(input [REG_SIZE-1 : 0] entropy,
                                      input [REG_SIZE-1 : 0] nonce,
                                      input [REG_SIZE-1 : 0] expected_drbg);
    begin
      if (!ready_tb)
        wait(ready_tb);

      $display("HMAC-DRBG-SHA256 failure injection");

      entropy_tb = entropy;
      nonce_tb   = nonce;

      $display("*** entropy : %064x", entropy_tb);
      $display("*** nonce   : %064x", nonce_tb);

      #(1 * CLK_PERIOD);
      init_tb = 1'b1;

      #(1 * CLK_PERIOD);
      init_tb = 1'b0;

      #(2 * CLK_PERIOD);

      wait(dut.drbg_st_reg == dut.CHCK_ST);
      force dut.failure_check = 1'b1;
      #(1 * CLK_PERIOD);
      release dut.failure_check;
      #(1 * CLK_PERIOD);

      wait(valid_tb);
      $display("The HMAC DRBG core completed the execution");

      if (drbg_tb == expected_drbg) begin
        $display("*** TC %0d successful (failure-injection).", tc_number);
        $display("");
      end else begin
        $display("*** ERROR: TC %0d failure-injection NOT successful.", tc_number);
        $display("Expected: 0x%064x", expected_drbg);
        $display("Got:      0x%064x", drbg_tb);
        $display("");
        error_ctr = error_ctr + 1;
      end

      tc_number = tc_number + 1;
    end
  endtask

  //----------------------------------------------------------------
  // hmac_drbg_zeroize_test
  // Issue a command and zeroize in the same cycle; verify the FSM
  // returns to IDLE and `ready` stays high (busy must not appear).
  //----------------------------------------------------------------
  task hmac_drbg_zeroize_test();
    begin
      busy_seen = 0;

      if (!ready_tb)
        wait(ready_tb);

      $display("HMAC DRBG SHA-256 Zeroize...");

      entropy_tb = random_gen();
      nonce_tb   = random_gen();

      # CLK_PERIOD;
      init_tb    = 1'b1;
      zeroize_tb = 1'b1;

      # CLK_PERIOD;
      init_tb    = 1'b0;
      zeroize_tb = 1'b0;
      for (int i = 0; i < 10; i++) begin
        # CLK_PERIOD;
        if (!ready_tb)
          busy_seen = 1;
      end

      if (busy_seen) begin
        $display("*** ERROR: TC %0d NOT successful.\n", tc_number);
        error_ctr = error_ctr + 1;
      end

      # CLK_PERIOD;
      busy_seen = 0;

      # CLK_PERIOD;
      next_tb    = 1'b1;
      zeroize_tb = 1'b1;

      # CLK_PERIOD;
      next_tb    = 1'b0;
      zeroize_tb = 1'b0;
      for (int i = 0; i < 10; i++) begin
        # CLK_PERIOD;
        if (!ready_tb)
          busy_seen = 1;
      end

      if (busy_seen) begin
        $display("*** ERROR: TC %0d NOT successful.\n", tc_number);
        error_ctr = error_ctr + 1;
      end

      tc_number = tc_number + 1;
    end
  endtask

  //----------------------------------------------------------------
  // read_test_vectors
  // Parse the (hex) test vector file produced by the Python ref.
  //----------------------------------------------------------------
  task read_test_vectors(input string fname);
    begin
      integer line_cnt;
      integer fin;
      integer rv;
      bit [REG_SIZE-1:0]      val;
      bit [MAX_ROUND_W-1:0]   round_val;
      integer test_vector_cnt;

      line_cnt = 0;
      test_vector_cnt = 0;

      fin = $fopen(fname, "r");
      if (fin == 0)
        $error("Can't open file %s", fname);
      while (!$feof(fin)) begin
        if (line_cnt == 0) begin
          rv = $fscanf(fin, "%h\n", round_val);
          if (rv != 1) begin
            $error("Failed to read the number of rounds");
            $fclose(fin);
            $finish;
          end
          test_vector.num_rounds = round_val;
        end else begin
          rv = $fscanf(fin, "%h\n", val);
          if (rv != 1) begin
            $error("Failed to read a matching string");
            $fclose(fin);
            $finish;
          end
          case (line_cnt)
            0: test_vector.num_rounds = val;
            1: test_vector.entropy    = val;
            2: test_vector.nonce      = val;
            default: begin
              test_vector.drbg_outputs[test_vector_cnt] = val;
              test_vector_cnt++;
            end
          endcase
        end
        line_cnt++;
      end
      $fclose(fin);

      $display("Read test vector with %0d rounds from %s", test_vector_cnt, fname);
    end
  endtask

  //----------------------------------------------------------------
  // hmac_drbg_directed_test
  // Caliptra-style KATs computed by hmac_drbg_sha256_placeholder_ref.py.
  //----------------------------------------------------------------
  task hmac_drbg_directed_test;
    begin
      reg [REG_SIZE-1 : 0] entropy_v;
      reg [REG_SIZE-1 : 0] nonce_v;
      reg [REG_SIZE-1 : 0] expected_v;

      // COUNT 0 -- all-zero entropy + nonce
      entropy_v  = 256'h0000000000000000000000000000000000000000000000000000000000000000;
      nonce_v    = 256'h0000000000000000000000000000000000000000000000000000000000000000;
      expected_v = 256'h601cf54e09f7b9149eee6624bfba7d12daae70b5f2d8c57b405f96d1aa92dc47;
      hmac256_drbg(entropy_v, nonce_v, expected_v);

      // COUNT 1 -- all-ones entropy + nonce
      entropy_v  = 256'hffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
      nonce_v    = 256'hffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
      expected_v = 256'hd046938ba37e4f0727efb41c8b512434fe4661be6ef60257eaf3ed3e9632bc17;
      hmac256_drbg(entropy_v, nonce_v, expected_v);

      // COUNT 2
      entropy_v  = 256'hf71ee80f1d123dc3f70eaa1fb3272714858ea555bc496bf39adb107b192bf0bc;
      nonce_v    = 256'hde2b2a66ee13797c69438a9bf6f8514c0a8abefd3e5533e1119ae88e8d641771;
      expected_v = 256'he3e98356c49d48b514b0401a14a4d49edf7ebfa56596711b25e65ebc7de7ddd0;
      hmac256_drbg(entropy_v, nonce_v, expected_v);

      // COUNT 3
      entropy_v  = 256'h6b9d3dad2e1b8c1c05b19875b6659f4de23c3b667bf297ba9aa47740787137d8;
      nonce_v    = 256'h9a9083505bc92276aec4be312696ef7bf3bf603f4bbd381196a029f340585312;
      expected_v = 256'h5592a9422c79cb72b937bb7aa5fafd652ab42e3ae6ca28511d97637d536e3e00;
      hmac256_drbg(entropy_v, nonce_v, expected_v);

      // COUNT 4 -- failure-injection test (FSM forced into K3/V3 loop).
      // The second iteration of the inner generate loop reuses the same
      // state machine but with K/V already updated; using the all-zero
      // seed material, the NEXT-after-INIT value is the expected output.
      entropy_v  = 256'h0000000000000000000000000000000000000000000000000000000000000000;
      nonce_v    = 256'h0000000000000000000000000000000000000000000000000000000000000000;
      expected_v = 256'h5b01f41b19fac4275d50e29a795c8d4be1eba6c3ac4c9e56ee7c168e3de228cd;
      hmac256_drbg_failure_injection(entropy_v, nonce_v, expected_v);
    end
  endtask

  //----------------------------------------------------------------
  // hmac_drbg_multi_rounds_directed_test
  //----------------------------------------------------------------
  task hmac_drbg_multi_rounds_directed_test;
    begin
      read_test_vectors(hmac_drbg_test_vector_file);
      hmac256_drbg_multi_rounds(test_vector.entropy,
                                test_vector.nonce,
                                test_vector.drbg_outputs,
                                test_vector.num_rounds);
    end
  endtask

  //----------------------------------------------------------------
  // hmac_drbg_randomized_test
  // Generate random (entropy, nonce, num_rounds), call the Python
  // ref to compute expected outputs, then check the RTL.
  //----------------------------------------------------------------
  task hmac_drbg_randomized_test;
    begin
      int file;
      reg [REG_SIZE-1 : 0]    entropy;
      reg [REG_SIZE-1 : 0]    nonce;
      reg [MAX_ROUND_W-1:0]   num_rounds;

      entropy    = random_gen();
      nonce      = random_gen();
      num_rounds = $urandom_range(1, MAX_ROUND);

      file = $fopen("tb_inputs.hex", "w");
      $fdisplay(file, "%d", num_rounds);
      $fdisplay(file, "%h", entropy);
      $fdisplay(file, "%h", nonce);
      $fclose(file);

      $system($sformatf("python3 hmac_drbg_sha256_placeholder_ref.py"));

      read_test_vectors("hmac_drbg_sha256_test_vector.hex");

      hmac256_drbg_multi_rounds(test_vector.entropy,
                                test_vector.nonce,
                                test_vector.drbg_outputs,
                                test_vector.num_rounds);
    end
  endtask

  //----------------------------------------------------------------
  // always_debug
  //----------------------------------------------------------------
  always @(dut.drbg_st_reg) begin
    if (DEBUG)
      $display("--------------\n state\n %0d --------------", dut.drbg_st_reg);
  end

  //----------------------------------------------------------------
  // main
  //----------------------------------------------------------------
  initial begin : main
    $display("   -= Testbench for HMAC-DRBG-SHA256 started =-");
    $display("    ===========================================");
    $display("");

    init_sim();
    reset_dut();

    if (hmac_drbg_test_to_run == "HMAC_DRBG_SHA256_directed_test") begin
      hmac_drbg_directed_test();
      if (hmac_drbg_test_vector_file != "")
        hmac_drbg_multi_rounds_directed_test();
    end else begin
      hmac_drbg_randomized_test();
    end

    hmac_drbg_zeroize_test();

    display_test_results();

    $display("");
    $display("*** HMAC-DRBG-SHA256 simulation done. ***");

    #(2 * CLK_PERIOD);
    $finish;
  end // main

endmodule

//======================================================================
// EOF hmac_drbg_sha256_placeholder_tb.sv
//======================================================================
