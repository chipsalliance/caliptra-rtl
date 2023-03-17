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
    localparam REG_SIZE  = 384;
    localparam SEED_SIZE = 384;
    localparam HMAC_DRBG_PRIME = 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973;

    localparam CLK_HALF_PERIOD = 1;
    localparam CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

    localparam DEBUG     = 0;
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
  reg   [147 : 0]            lfsr_seed_tb;
  reg   [383 : 0]            entropy_tb;
  reg   [383 : 0]            nonce_tb;
  wire  [383 : 0]            drbg_tb;


  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  hmac_drbg 
  #(
        .REG_SIZE(REG_SIZE),
        .HMAC_DRBG_PRIME(HMAC_DRBG_PRIME)
  ) hmac_drbg_dut
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
  function logic [383 : 0] random_gen();
    logic [383 : 0] random_seed;
    for (int i=0; i < 12; i++) begin
      random_seed[i*32 +: 32] = $random;
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
      $display("STATE  = 0x%02d", hmac_drbg_dut.drbg_st_reg);
      $display("");
      $display("HMAC block: 0x%096x",hmac_drbg_dut.HMAC_block);
      $display("HMAC key: 0x%096x",hmac_drbg_dut.HMAC_key);
      $display("HMAC lfsr_seed: 0x%096x",hmac_drbg_dut.HMAC_lfsr_seed);
      $display("HMAC tag: 0x%096x",hmac_drbg_dut.HMAC_tag);
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

    end
  endtask // hmac_drbg_test


  //----------------------------------------------------------------
  // always_debug()
  //
  // This always block enables to debug the state transactions
  //----------------------------------------------------------------
  always @(hmac_drbg_dut.drbg_st_reg)
  begin
      if (DEBUG)
        $display("--------------\n state\n %0d --------------", hmac_drbg_dut.drbg_st_reg);
  end


  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -= Testbench for HMAC DRBG started =-");
      $display("    ==============================");
      $display("");

      init_sim();
      //dump_dut_state();
      reset_dut();
      //dump_dut_state();

      hmac_drbg_test();

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
