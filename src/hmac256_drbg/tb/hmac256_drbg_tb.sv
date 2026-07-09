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
// hmac256_drbg_tb.sv
//
// Standalone testbench for hmac256_drbg. Randomizes entropy, nonce, and
// LFSR seed each iteration, invokes the python reference model to
// produce expected outputs, and compares DUT results against them.
//======================================================================

module hmac256_drbg_tb();


  //----------------------------------------------------------------
  // Local Parameters.
  //----------------------------------------------------------------
    localparam MAX_ROUND    = 15;
    localparam MAX_ROUND_W  = $clog2(MAX_ROUND);

    localparam REG_SIZE  = 256;
    localparam HMAC_DRBG_PRIME = 256'hFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551;

    localparam CLK_HALF_PERIOD = 1;
    localparam CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

    localparam DEBUG     = 0;

    string      hmac256_drbg_test_vector_file;
    string      hmac256_drbg_test_to_run;
  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0]  cycle_ctr;
  reg [63 : 0]  error_ctr;

  reg [7 : 0]   tc_number;

  // Clock and reset.
  reg                        clk_tb;
  reg                        reset_n_tb;

  //Control
  reg                        zeroize_tb;
  reg                        init_tb;
  reg                        next_tb;
  wire                       ready_tb;
  wire                       valid_tb;

  //Data
  reg   [191 : 0]                   lfsr_seed_tb;
  reg   [REG_SIZE-1 : 0]            entropy_tb;
  reg   [REG_SIZE-1 : 0]            nonce_tb;
  wire  [REG_SIZE-1 : 0]            drbg_tb;

  logic                     busy_seen;

  initial begin
    if ($value$plusargs("HMAC256_DRBG_TEST=%s", hmac256_drbg_test_to_run)) begin
      $display("%m: Running hmac256_drbg test = %s", hmac256_drbg_test_to_run);
    end else begin
      hmac256_drbg_test_to_run = "HMAC256_DRBG_randomized_test";
      $display("%m: Running hmac256_drbg test = %s", hmac256_drbg_test_to_run);
    end

    if (hmac256_drbg_test_to_run == "HMAC256_DRBG_directed_test") begin
      if ($value$plusargs("HMAC256_DRBG_TEST_VECTOR_FILE=%s", hmac256_drbg_test_vector_file)) begin
        $display("%m: Using HMAC256_DRBG test vectors from file specified via plusarg: %s", hmac256_drbg_test_vector_file);
      end else begin
        hmac256_drbg_test_vector_file = "";
        $display("%m: There is no valid test vector file.");
      end
    end
  end


  typedef struct packed {
      logic [REG_SIZE-1 : 0]  entropy;
      logic [REG_SIZE-1 : 0]  nonce;
      logic [MAX_ROUND_W-1:0] num_rounds;
      logic [MAX_ROUND-1:0][REG_SIZE-1:0] drbg_outputs;
  } test_vector_t;

  test_vector_t test_vector;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  hmac256_drbg
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
        .lfsr_seed(lfsr_seed_tb),
        .entropy(entropy_tb),
        .nonce(nonce_tb),
        .drbg(drbg_tb)
    );

  //----------------------------------------------------------------
  // clk_gen
  //----------------------------------------------------------------
  always
    begin : clk_gen
      #CLK_HALF_PERIOD;
      clk_tb = !clk_tb;
    end // clk_gen


  //----------------------------------------------------------------
  // sys_monitor()
  //----------------------------------------------------------------
  always
    begin : sys_monitor
      cycle_ctr = cycle_ctr + 1;

      #(CLK_PERIOD);

      if (DEBUG)
        begin
          dump_dut_state();
        end
    end

  //----------------------------------------------------------------
  // Randomize function
  //----------------------------------------------------------------
  function logic [REG_SIZE-1 : 0] random_gen();
    logic [REG_SIZE-1 : 0] random_seed;
    for (int i=0; i < (REG_SIZE / 32); i++) begin
      random_seed[i*32 +: 32] = $urandom;
    end
    return random_seed;
  endfunction

  //----------------------------------------------------------------
  // dump_dut_state()
  //----------------------------------------------------------------
  task dump_dut_state;
    begin
      $display("cycle: 0x%016x", cycle_ctr);
      $display("State of DUT");
      $display("------------");
      $display("STATE  = 0x%02d", dut.drbg_st_reg);
      $display("");
      $display("HMAC block: 0x%064x",dut.HMAC_block);
      $display("HMAC key:   0x%064x",dut.HMAC_key);
      $display("HMAC seed:  0x%048x",dut.lfsr_seed);
      $display("HMAC tag:   0x%064x",dut.HMAC_tag);
      $display("");

    end
  endtask // dump_dut_state


  //----------------------------------------------------------------
  // reset_dut()
  //----------------------------------------------------------------
  task reset_dut;
    begin
      $display("*** Toggle reset.");
      reset_n_tb = 0;

      #(2 * CLK_PERIOD);
      reset_n_tb = 1;
      $display("");
    end
  endtask // reset_dut


  //----------------------------------------------------------------
  // display_test_results()
  //----------------------------------------------------------------
  task display_test_results;
    begin
      if (error_ctr == 0)
        begin
          $display("*** All %02d test cases completed successfully", tc_number);
          $display("* TESTCASE PASSED");
        end
      else
        begin
          $display("*** %02d tests completed - %02d test cases did not complete successfully.",
                   tc_number, error_ctr);
          $display("* TESTCASE FAILED");
        end
    end
  endtask // display_test_results


  //----------------------------------------------------------------
  // init_sim()
  //----------------------------------------------------------------
  task init_sim;
    begin
      cycle_ctr         = 0;
      error_ctr         = 0;
      tc_number         = 0;

      clk_tb            = 0;
      reset_n_tb        = 1;

      zeroize_tb        = 0;
      init_tb           = 0;
      next_tb           = 0;

      //Data
      lfsr_seed_tb      = 192'h0;
      entropy_tb        = 256'h0;
      nonce_tb          = 256'h0;
    end
  endtask // init_sim


  //----------------------------------------------------------------
  // hmac256_drbg_multi_rounds()
  //----------------------------------------------------------------
  task hmac256_drbg_multi_rounds(input [REG_SIZE-1 : 0] entropy, input [REG_SIZE-1 : 0] nonce,
                  input [MAX_ROUND-1 : 0][REG_SIZE-1 : 0] expected_drbg,
                  input [MAX_ROUND_W-1:0] num_rounds);
    begin
        if (!ready_tb)
            wait(ready_tb);

        $display("The HMAC256 DRBG multi rounds is triggered...");

        entropy_tb = entropy;
        nonce_tb = nonce;

        $display("*** entropy   : %064x", entropy_tb);
        $display("*** nonce     : %064x", nonce_tb);

        for (int i = 0; i < num_rounds; i++) begin
          lfsr_seed_tb = 192'(random_gen());
          $display("*** lfsr_seed : %048x", lfsr_seed_tb);

          #(1 * CLK_PERIOD);
          if (i==0) begin
            init_tb = 1'b1;
            next_tb = 1'b0;
          end
          else begin
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
          end
          else begin
              $display("*** ERROR: TC %0d round #%0d NOT successful.", tc_number, i);
              $display("Expected: 0x%064x", expected_drbg[i]);
              $display("Got:      0x%064x", drbg_tb);
              $display("");
              error_ctr = error_ctr + 1;
          end
        end

        tc_number = tc_number+1;
    end
  endtask // hmac256_drbg_multi_rounds

  //----------------------------------------------------------------
  // hmac256_drbg_multi_rounds_directed_test()
  //----------------------------------------------------------------
  task hmac256_drbg_multi_rounds_directed_test;
    begin
      read_test_vectors(hmac256_drbg_test_vector_file);

      hmac256_drbg_multi_rounds(test_vector.entropy, test_vector.nonce, test_vector.drbg_outputs, test_vector.num_rounds);
    end
  endtask

  task hmac256_drbg_randomized_test;
    begin
      int file;
      reg [REG_SIZE-1 : 0] entropy;
      reg [REG_SIZE-1 : 0] nonce;
      reg [MAX_ROUND_W-1:0] num_rounds;

      entropy    = random_gen();
      nonce      = random_gen();
      num_rounds = $urandom_range(1, MAX_ROUND);

      // Write test vectors to tb_inputs.hex
      file = $fopen("tb_inputs.hex", "w");
      if (file == 0)
        $fatal(1, "Can't open file tb_inputs.hex for writing");
      $fdisplay(file, "%d", num_rounds);
      $fdisplay(file, "%h", entropy);
      $fdisplay(file, "%h", nonce);
      $fclose(file);

      // Call Python reference model
      if ($system("python3 hmac256_drbg_ref.py") != 0)
          $fatal(1, "Python reference model failed");

      // Read expected results
      read_test_vectors("hmac256_drbg_test_vector.hex");

      hmac256_drbg_multi_rounds(test_vector.entropy, test_vector.nonce, test_vector.drbg_outputs, test_vector.num_rounds);
    end
  endtask

  //----------------------------------------------------------------
  // read_test_vectors()
  //----------------------------------------------------------------
  task read_test_vectors(input string fname);
    begin
      integer line_cnt;
      integer fin;
      integer rv;
      bit [REG_SIZE-1:0] val;
      bit [MAX_ROUND_W-1:0] round_val;
      integer test_vector_cnt;

      line_cnt = 0;
      test_vector_cnt = 0;

      fin = $fopen(fname, "r");
      if (fin == 0)
          $fatal(1, "Can't open file %s", fname);
      while (!$feof(fin)) begin
        if (line_cnt == 0) begin
          rv = $fscanf(fin, "%h\n", round_val);
          if (rv != 1) begin
              $error("Failed to read the number of rounds");
              $fclose(fin);
              $finish;
          end
          test_vector.num_rounds = round_val;
        end
        else begin
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
                if (test_vector_cnt >= MAX_ROUND)
                  $fatal(1, "Too many DRBG outputs in %s (max %0d)", fname, MAX_ROUND);
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

  task hmac256_drbg_zeroize_test();
    begin
      busy_seen = 0;

      if (!ready_tb)
        wait(ready_tb);

      $display("HMAC256 DRBG Zeroize...");

      entropy_tb   = random_gen();
      nonce_tb     = random_gen();
      lfsr_seed_tb = 192'(random_gen());

      # CLK_PERIOD;
      init_tb    = 1'b1;
      zeroize_tb = 1'b1;

      # CLK_PERIOD;
      init_tb    = 1'b0;
      zeroize_tb = 1'b0;
      for (int i=0; i < 10; i++) begin
        # CLK_PERIOD;
        if (!ready_tb)
          busy_seen = 1;
      end

      if (busy_seen)
      begin
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
      for (int i=0; i < 10; i++) begin
        # CLK_PERIOD;
        if (!ready_tb)
          busy_seen = 1;
      end

      if (busy_seen)
      begin
        $display("*** ERROR: TC %0d NOT successful.\n", tc_number);
        error_ctr = error_ctr + 1;
      end

      tc_number = tc_number+1;
    end
  endtask

  //----------------------------------------------------------------
  // hmac256_drbg_failure_injection_test()
  //   Force the internal failure_check high while the DUT is in CHCK_ST
  //   to exercise the rejection retry path (K3 -> V3 -> T). Confirms the
  //   engine does not lock up when the DRBG output equals 0 or >= P-256
  //   curve order.
  //----------------------------------------------------------------
  task hmac256_drbg_failure_injection_test();
    begin
      if (!ready_tb)
        wait(ready_tb);

      $display("HMAC256 DRBG failure injection");

      entropy_tb   = random_gen();
      nonce_tb     = random_gen();
      lfsr_seed_tb = 192'(random_gen());

      $display("*** entropy   : %064x", entropy_tb);
      $display("*** nonce     : %064x", nonce_tb);
      $display("*** lfsr_seed : %048x", lfsr_seed_tb);

      # CLK_PERIOD;
      init_tb = 1'b1;

      # CLK_PERIOD;
      init_tb = 1'b0;

      # (2 * CLK_PERIOD);

      wait(dut.drbg_st_reg == dut.CHCK_ST);
      force dut.failure_check = 1'b1;
      # CLK_PERIOD;
      release dut.failure_check;
      # CLK_PERIOD;

      wait(valid_tb);
      $display("*** TC %0d: rejection retry completed, valid asserted", tc_number);

      tc_number = tc_number + 1;
    end
  endtask

  //----------------------------------------------------------------
  // always_debug()
  //----------------------------------------------------------------
  always @(dut.drbg_st_reg)
  begin
      if (DEBUG)
        $display("--------------\n state\n %0d --------------", dut.drbg_st_reg);
  end


  //----------------------------------------------------------------
  // main
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -= Testbench for HMAC256 DRBG started =-");
      $display("    ==============================");
      $display("");

      init_sim();
      reset_dut();

      if (hmac256_drbg_test_to_run == "HMAC256_DRBG_directed_test") begin
        if (hmac256_drbg_test_vector_file != "")
          hmac256_drbg_multi_rounds_directed_test();
      end
      else begin
        hmac256_drbg_randomized_test();
      end

      hmac256_drbg_zeroize_test();

      hmac256_drbg_failure_injection_test();

      display_test_results();

      $display("");
      $display("*** HMAC256 DRBG simulation done. ***");

      #(2 * CLK_PERIOD);
      $finish;
    end // main

endmodule // hmac256_drbg_tb

//======================================================================
// EOF hmac256_drbg_tb.sv
//======================================================================
