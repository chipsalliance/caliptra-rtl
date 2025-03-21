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
// hmac_drbg_tb.sv
//
//
// 
// This test to check HMAC DRBG functionality
// Empty test
//======================================================================

module hmac_drbg_tb();


  //----------------------------------------------------------------
  // Local Parameters.
  //----------------------------------------------------------------
    localparam MAX_ROUND    = 15;
    localparam MAX_ROUND_W  = $clog2(MAX_ROUND);

    localparam REG_SIZE  = 384;
    localparam HMAC_DRBG_PRIME = 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973;

    localparam CLK_HALF_PERIOD = 1;
    localparam CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

    localparam DEBUG     = 0;

    string      hmac_drbg_test_vector_file; // Input test vector file
    string      hmac_drbg_test_to_run;
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
  reg   [REG_SIZE-1 : 0]            lfsr_seed_tb;
  reg   [REG_SIZE-1 : 0]            entropy_tb;
  reg   [REG_SIZE-1 : 0]            nonce_tb;
  wire  [REG_SIZE-1 : 0]            drbg_tb;

  logic                     failure_injected;

  initial begin
    if ($value$plusargs("HMAC_DRBG_TEST=%s", hmac_drbg_test_to_run)) begin
      $display("%m: Running hmac_drbg test = %s", hmac_drbg_test_to_run);
    end else begin
      hmac_drbg_test_to_run = "HMAC_DRBG_directed_test";
      $display("%m: Running hmac_drbg test = %s", hmac_drbg_test_to_run);
    end

    if (hmac_drbg_test_to_run == "HMAC_DRBG_directed_test") begin
      if ($value$plusargs("HMAC_DRBG_TEST_VECTOR_FILE=%s", hmac_drbg_test_vector_file)) begin
        $display("%m: Using HMAC_DRBG test vectors from file specified via plusarg: %s", hmac_drbg_test_vector_file);
      end else begin
        hmac_drbg_test_vector_file = "";
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
  hmac_drbg 
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

  //bind coverage file
  hmac_drbg_cov_bind i_hmac_drbg_cov_bind();

  //----------------------------------------------------------------
  // clk_gen
  //
  // Always running clock generator process.
  //----------------------------------------------------------------
  always
    begin : clk_gen
      #CLK_HALF_PERIOD;
      clk_tb = !clk_tb;
    end // clk_gen


  //----------------------------------------------------------------
  // sys_monitor()
  //
  // An always running process that creates a cycle counter and
  // conditionally displays information about the DUT.
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
  //
  // 
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
  //
  // Dump the state of the dump when needed.
  //----------------------------------------------------------------
  task dump_dut_state;
    begin
      $display("cycle: 0x%016x", cycle_ctr);
      $display("State of DUT");
      $display("------------");
      $display("STATE  = 0x%02d", dut.drbg_st_reg);
      $display("");
      $display("HMAC block: 0x%096x",dut.HMAC_block);
      $display("HMAC key: 0x%096x",dut.HMAC_key);
      $display("HMAC lfsr_seed: 0x%096x",dut.lfsr_seed);
      $display("HMAC tag: 0x%096x",dut.HMAC_tag);
      $display("");

    end
  endtask // dump_dut_state


  //----------------------------------------------------------------
  // reset_dut()
  //
  // Toggle reset to put the DUT into a well known state.
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
  //
  // Display the accumulated test results.
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
  //
  // Initialize all counters and testbed functionality as well
  // as setting the DUT inputs to defined values.
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
      lfsr_seed_tb      = 384'h0;
      entropy_tb        = 384'h0;
      nonce_tb          = 384'h0;

      failure_injected  = 0;
    end
  endtask // init_sim


  //----------------------------------------------------------------
  // hmac384_drbg()
  //
  //----------------------------------------------------------------
  task hmac384_drbg(input [383 : 0] entropy, input [383 : 0] nonce,
                  input [383 : 0] lfsr_seed, input  [383 : 0] expected_drbg);
    begin
        if (!ready_tb)
            wait(ready_tb);
            
        $display("The HMAC DRBG core is triggered...");
        
        entropy_tb = entropy;
        nonce_tb = nonce;
        lfsr_seed_tb = lfsr_seed;

        $display("*** entropy   : %096x", entropy_tb);
        $display("*** nonce     : %096x", nonce_tb);
        $display("*** lfsr_seed : %096x", lfsr_seed);

        #(1 * CLK_PERIOD);
        init_tb = 1'b1;  

        #(1 * CLK_PERIOD);
        init_tb = 1'b0;

        #(2 * CLK_PERIOD);
        

        wait(valid_tb);
        $display("The HMAC DRBG core completed the execution");

        if (drbg_tb == expected_drbg)
          begin
            $display("*** TC %0d successful.", tc_number);
            $display("");
          end
        else
          begin
            $display("*** ERROR: TC %0d NOT successful.", tc_number);
            $display("Expected: 0x%096x", expected_drbg);
            $display("Got:      0x%096x", drbg_tb);
            $display("");
            error_ctr = error_ctr + 1;
          end

        tc_number = tc_number+1;

    end
  endtask // hmac384_drbg


  //----------------------------------------------------------------
  // hmac384_drbg_multi_rounds()
  //
  //----------------------------------------------------------------
  task hmac384_drbg_multi_rounds(input [REG_SIZE-1 : 0] entropy, input [REG_SIZE-1 : 0] nonce,
                  input [MAX_ROUND : 0][REG_SIZE-1 : 0] expected_drbg, 
                  input [MAX_ROUND_W-1:0] num_rounds);
    begin
        if (!ready_tb)
            wait(ready_tb);
            
        $display("The HMAC DRBG multi rounds is triggered...");
        
        entropy_tb = entropy;
        nonce_tb = nonce;

        $display("*** entropy   : %096x", entropy_tb);
        $display("*** nonce     : %096x", nonce_tb);

        for (int i = 0; i < num_rounds; i++) begin
          lfsr_seed_tb = random_gen();
          $display("*** lfsr_seed : %096x", lfsr_seed_tb);

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
              $display("Expected: 0x%096x", expected_drbg[i]);
              $display("Got:      0x%096x", drbg_tb);
              $display("");
              error_ctr = error_ctr + 1;
          end
        end

        tc_number = tc_number+1;
    end
  endtask // hmac384_drbg_multi_rounds
  //----------------------------------------------------------------
  // hmac_drbg_test()
  //
  // Main test task will perform complete NIST SP 800-90A DRBG.
  //
  // NIST SP 800-90A:
  // https://csrc.nist.gov/publications/detail/sp/800-90a/archive/2012-01-23
  //
  // Source Website:
  // https://github.com/k-qy/HMAC-DRBG/tree/master/specs/drbgtestvectors/drbgvectors_no_reseed
  //----------------------------------------------------------------
  task hmac_drbg_test;
    begin
        reg [383 : 0] nist_entropy;
        reg [383 : 0] nist_nonce;
        reg [383 : 0] nist_expected;
        reg [383 : 0] seed;

        
        nist_entropy  = 384'h6B9D3DAD2E1B8C1C05B19875B6659F4DE23C3B667BF297BA9AA47740787137D896D5724E4C70A825F872C9EA60D2EDF5;        
        nist_nonce    = 384'h9a9083505bc92276aec4be312696ef7bf3bf603f4bbd381196a029f340585312313bca4a9b5b890efee42c77b1ee25fe;
        nist_expected = 384'h94ED910D1A099DAD3254E9242AE85ABDE4BA15168EAF0CA87A555FD56D10FBCA2907E3E83BA95368623B8C4686915CF9;
        seed = random_gen();

        hmac384_drbg(nist_entropy, nist_nonce, seed, nist_expected); 


        nist_entropy  = 384'h6B9D3DAD2E1B8C1C05B19875B6659F4DE23C3B667BF297BA9AA47740787137D896D5724E4C70A825F872C9EA60D2EDF5;
        nist_nonce    = 384'h768412320f7b0aa5812fce428dc4706b3cae50e02a64caa16a782249bfe8efc4b7ef1ccb126255d196047dfedf17a0a9;
        nist_expected = 384'h015EE46A5BF88773ED9123A5AB0807962D193719503C527B031B4C2D225092ADA71F4A459BC0DA98ADB95837DB8312EA;
        seed = random_gen();

        hmac384_drbg(nist_entropy, nist_nonce, seed, nist_expected); 

        nist_entropy  = 384'h14AEFB51DF578FF3D77662153B10CEE5C7930454AAE90E1A68C951E7466216DEEEAB7032856F3E6244194E9BE0923BE9;
        nist_nonce    = 384'h31759BD97E875F3559D260BEE1C6F9995F330BA2D3DD2D93502E7E696C1900632E22672EB5C83CF761F592AAFC0E040A;
        nist_expected = 384'hC8958B49032629A9EAB4FE2F7CA7F3B7C768EC825D143FE65002904A6E91EF971AC8F6B3C1E97F132F99161AE3E58E38;
        seed = random_gen();

        hmac384_drbg(nist_entropy, nist_nonce, seed, nist_expected); 

        nist_entropy  = 384'h14F93F145CE951B987CC52CD8EE5B916DF9042433E63F5771210B2E596709CFD4A9080EC1E0252F82E08333CBB259F0C;
        nist_nonce    = 384'h31759BD97E875F3559D260BEE1C6F9995F330BA2D3DD2D93502E7E696C1900632E22672EB5C83CF761F592AAFC0E040A;
        nist_expected = 384'h1E006AABF131E194003305A959A0B5C070C2E298393FB399D3F54181900B089E5619EF4AD594C4C4C71F4479DD87E96A;
        seed = random_gen();

        hmac384_drbg(nist_entropy, nist_nonce, seed, nist_expected); 


        nist_entropy  = 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
        nist_nonce    = 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
        nist_expected = 384'h7F68A6D896EA5DA62E78DEDB46F6662BC141F2F0B9E641ACC7342663FD51444E380FEA1DABBCA55F18987C0CFC10DF77;
        seed = random_gen();

        hmac384_drbg(nist_entropy, nist_nonce, seed, nist_expected); 

        nist_entropy  = 384'h000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
        nist_nonce    = 384'h000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
        nist_expected = 384'hFEEEF5544A76564990128AD189E873F21F0DFD5AD7E2FA861127EE6E394CA784871C1AEC032C7A8B10B93E0EAB8946D6;
        seed = random_gen();

        hmac384_drbg(nist_entropy, nist_nonce, seed, nist_expected); 


        nist_entropy  = 384'h1e8dcd3d3b23f17606d7cd0d00f3e30189375212b2c2846546df998d06b97b0db1f056638484d609c0895e8112153524;
        nist_nonce    = 384'he77696ce793069f247ecdb8f8932d612bbd2727772aff7e5d513d2aae2f784c5e33724c67cfde9f9462df78c76d457ed;
        //4dacc66cc713c711b64ef7f7fd86e14bb29580ec9123f1a9db947c86338073ea81f472c7ddf78ee7e213b0f7722f1fe6 assumed failed
        nist_expected = 384'hc84a3e2340ca28a68823e02635931d4e088c28f26c1442583327bd2aa3de12460211cb7519b222d0b948769ad6b16075;
        seed = random_gen();

        hmac384_drbg_failure_injection(nist_entropy, nist_nonce, seed, nist_expected); 

    end
  endtask // hmac_drbg_test

  //----------------------------------------------------------------
  // hmac_drbg_multi_rounds_directed_test()
  //
  //
  //----------------------------------------------------------------
  task hmac_drbg_multi_rounds_directed_test;
    begin
      // Read expected results from tb_expected.hex
      read_test_vectors(hmac_drbg_test_vector_file);

      hmac384_drbg_multi_rounds(test_vector.entropy, test_vector.nonce, test_vector.drbg_outputs, test_vector.num_rounds);

    end
  endtask

  task hmac_drbg_randomized_test;
    begin
      int file;
      string cmd, line;
      reg [REG_SIZE-1 : 0] entropy;
      reg [REG_SIZE-1 : 0] nonce;
      reg [MAX_ROUND_W-1:0] num_rounds;

      entropy = random_gen();
      nonce = random_gen();
      num_rounds = $urandom_range(1, MAX_ROUND);

      // Write test vectors to tb_inputs.hex
      file = $fopen("tb_inputs.hex", "w");
      $fdisplay(file, "%d", num_rounds);
      $fdisplay(file, "%h", entropy);
      $fdisplay(file, "%h", nonce);
      
      $fclose(file);

      // Call Python reference model
      $system($sformatf("python3 hmac_drbg_ref.py"));

      // Read expected results from tb_expected.hex
      read_test_vectors("hmac_drbg_test_vector.hex");

      hmac384_drbg_multi_rounds(test_vector.entropy, test_vector.nonce, test_vector.drbg_outputs, test_vector.num_rounds);

    end
  endtask

  //----------------------------------------------------------------
  // read_test_vectors()
  //
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
          $error("Can't open file %s", fname);
      while (!$feof(fin)) begin
        if (line_cnt == 0) begin
          rv = $fscanf(fin, "%h\n", round_val); // Read first line as an integer
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
                test_vector.drbg_outputs[test_vector_cnt]    = val;
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
  // hmac384_drbg_failure_injection()
  //
  //----------------------------------------------------------------
  task hmac384_drbg_failure_injection(input [383 : 0] entropy, input [383 : 0] nonce,
                  input [383 : 0] lfsr_seed, input  [383 : 0] expected_drbg);
    begin
        if (!ready_tb)
            wait(ready_tb);
            
        $display("HMAC-DRBG failure injection");
        
        entropy_tb = entropy;
        nonce_tb = nonce;
        lfsr_seed_tb = lfsr_seed;

        $display("*** entropy   : %096x", entropy_tb);
        $display("*** nonce     : %096x", nonce_tb);
        $display("*** lfsr_seed : %096x", lfsr_seed);

        #(1 * CLK_PERIOD);
        init_tb = 1'b1;  

        #(1 * CLK_PERIOD);
        init_tb = 1'b0;

        #(2 * CLK_PERIOD);
        
        wait(dut.drbg_st_reg == dut.CHCK_ST);
        failure_injected = 1;
        force dut.failure_check = 1'b1;
        #(1 * CLK_PERIOD);
        failure_injected = 0;
        release dut.failure_check;
        #(1 * CLK_PERIOD);

        wait(valid_tb);
        $display("The HMAC DRBG core completed the execution");

        if (drbg_tb == expected_drbg)
          begin
            $display("*** TC %0d successful.", tc_number);
            $display("");
          end
        else
          begin
            $display("*** ERROR: TC %0d NOT successful.", tc_number);
            $display("Expected: 0x%096x", expected_drbg);
            $display("Got:      0x%096x", drbg_tb);
            $display("");
            error_ctr = error_ctr + 1;
          end

        tc_number = tc_number+1;

    end
  endtask // hmac384_drbg_failure_injection

  //----------------------------------------------------------------
  // always_debug()
  //
  // This always block enables to debug the state transactions
  //----------------------------------------------------------------
  always @(dut.drbg_st_reg)
  begin
      if (DEBUG)
        $display("--------------\n state\n %0d --------------", dut.drbg_st_reg);
  end


  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      // $write("PLAYBOOK_RANDOM_SEED = %s\n", getenv("PLAYBOOK_RANDOM_SEED"));
      $display("   -= Testbench for HMAC DRBG started =-");
      $display("    ==============================");
      $display("");

      init_sim();
      //dump_dut_state();
      reset_dut();
      //dump_dut_state();

      if (hmac_drbg_test_to_run == "HMAC_DRBG_directed_test") begin
        hmac_drbg_test();
        if (hmac_drbg_test_vector_file != "")
          hmac_drbg_multi_rounds_directed_test();
      end
      else begin
        hmac_drbg_randomized_test();
      end

      display_test_results();

      $display("");
      $display("*** HMAC DRBG simulation done. ***");

      #(2 * CLK_PERIOD);
      $finish;
    end // main

endmodule // hmac_drbg_tb

//======================================================================
// EOF hmac_drbg_tb.sv
//======================================================================
