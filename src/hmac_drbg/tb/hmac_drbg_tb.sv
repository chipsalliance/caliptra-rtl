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
  reg                        mode_tb;
  reg                        init_tb;
  reg                        next_tb;
  wire                       ready_tb;
  wire                       valid_tb;

  //Data
  reg   [SEED_SIZE-1 : 0]    seed_tb;
  reg   [383 : 0]            privkey_tb;
  reg   [383 : 0]            hashed_msg_tb;
  wire  [383 : 0]            nonce_tb;


  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  hmac_drbg 
  #(
        .REG_SIZE(REG_SIZE),
        .SEED_SIZE(SEED_SIZE),
        .HMAC_DRBG_PRIME(HMAC_DRBG_PRIME)
  ) hmac_drbg_dut
  (
        .clk(clk_tb),
        .reset_n(reset_n_tb),
        .mode(mode_tb),
        .init_cmd(init_tb),
        .next_cmd(next_tb),
        .ready(ready_tb),
        .valid(valid_tb),
        .seed(seed_tb),
        .privkey(privkey_tb),
        .hashed_msg(hashed_msg_tb),
        .nonce(nonce_tb)
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
  // dump_dut_state()
  //
  // Dump the state of the dump when needed.
  //----------------------------------------------------------------
  task dump_dut_state;
    begin
      $display("cycle: 0x%016x", cycle_ctr);
      $display("State of DUT");
      $display("------------");
      $display("STATE  = 0x%02d", hmac_drbg_dut.nonce_st_reg);
      $display("");
      $display("HMAC block: 0x%096x",hmac_drbg_dut.HMAC_block);
      $display("HMAC key: 0x%096x",hmac_drbg_dut.HMAC_key);
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

      mode_tb           = 0;
      init_tb           = 0;
      next_tb           = 0;
    
      //Data
      seed_tb           = 384'h0;
      privkey_tb        = 384'h0;
      hashed_msg_tb     = 384'h0;
    end
  endtask // init_sim


  //----------------------------------------------------------------
  // keygen_sim()
  //
  // HMAC DRBG works for key generation step
  //----------------------------------------------------------------
  task keygen_sim(input [383 : 0] seed, input  [383 : 0] nonce_expected);
    begin
        hashed_msg_tb = 384'h0;
        seed_tb = 384'h0;
        if (!ready_tb)
            wait(ready_tb);
            
        $display("The HMAC DRBG core is triggered...");
        mode_tb = 1'b0;        
        seed_tb = seed;
        $display("*** The seed : %096x",seed_tb);

        #(1 * CLK_PERIOD);
        init_tb = 1'b1;        
        #(1 * CLK_PERIOD);
        init_tb = 1'b0;
        #(2 * CLK_PERIOD);
        

        wait(valid_tb);
        $display("The HMAC DRBG core completed the execution");

        if (nonce_tb == nonce_expected)
          begin
            $display("*** TC %0d successful.", tc_number);
            $display("");
          end
        else
          begin
            $display("*** ERROR: TC %0d NOT successful.", tc_number);
            $display("Expected: 0x%096x", nonce_expected);
            $display("Got:      0x%096x", nonce_tb);
            $display("");
            error_ctr = error_ctr + 1;
          end

        tc_number = tc_number+1;

    end
  endtask // keygen_sim


  //----------------------------------------------------------------
  // sign_sim()
  //
  // HMAC DRBG works for signing step
  //----------------------------------------------------------------
  task sign_sim(input [383 : 0] h1, input [383 : 0] privKey, input  [383 : 0] nonce_expected);
    begin
        //$display("-----------------SIGNING-----------------");
        hashed_msg_tb = h1;
        privkey_tb = privKey;
        if (!ready_tb)
            wait(ready_tb);
            
        $display("The HMAC DRBG core is triggered...");
        mode_tb = 1'b1;
        $display("*** The seed : %096x",privkey_tb);

        #(1 * CLK_PERIOD);
        init_tb = 1'b1;        
        #(1 * CLK_PERIOD);
        init_tb = 1'b0;
        #(2 * CLK_PERIOD);
            

        wait(valid_tb);
        $display("The HMAC DRBG core completed the execution");

        if (nonce_tb == nonce_expected)
          begin
            $display("*** TC %0d successful.", tc_number);
            $display("");
          end
        else
          begin
            $display("*** ERROR: TC %0d NOT successful.", tc_number);
            $display("Expected: 0x%096x", nonce_expected);
            $display("Got:      0x%096x", nonce_tb);
            $display("");
  
            error_ctr = error_ctr + 1;
          end

        tc_number = tc_number+1;

    end
  endtask // sign_sim

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
        reg [255 : 0] nist_entropy;
        reg [127 : 0] nist_nonce;
        reg [383 : 0] nist_h1;
        reg [383 : 0] nist_privKey;
        reg [383 : 0] nist_expected;
        reg [383 : 0] seed;

        $display("\n\n=================KEYGEN TEST STARTS=================\n\n");

        nist_entropy  = 256'h51ec4987ddacbcf6348e4a891fa571c6e3aec02879eb0181a121a4846344a687;
        nist_nonce    = 128'hcdff9798761875320256e5a59bc94663;
        nist_expected = 384'h417534124df88195f2153b3b88483bdfcc32d95fa109cb745acca8b2c8a1b6fb05d187244af9a057ca867f14b3f21810;

        seed = {nist_entropy,nist_nonce};
        keygen_sim(seed,nist_expected);
        
        nist_entropy  = 256'hf8dfa70524d46f3545db3c687fe85a8ea35e32eda470b4e14b8b12f4e9c6bbf6;
        nist_nonce    = 128'hc08efa9ae1df90ae6f14b895c342ae07;
        nist_expected = 384'hdc9b998891e3a737fe9fc3ce4c9751831c2096e92b9092a57b04799241864f244e899dcda94e2e01ac5fe2f285498480;

        seed = {nist_entropy,nist_nonce};
        keygen_sim(seed,nist_expected); 
        
        nist_entropy  = 256'h7ab7da47ff7a95ebf2367de0a25c7885d80931447d2f5cc73ae7f66844910e48;
        nist_nonce    = 128'h1e05f53ca993b0266b7cde89960d681a;
        nist_expected = 384'hcd4bf0a6e15e9db50e200fc490933a89452a328287975ea37346ead493f99a89d7057dfb48c486208dd138accd4da162;

        seed = {nist_entropy,nist_nonce};
        keygen_sim(seed,nist_expected);


        nist_expected = 384'h4AE1C2B3AE2EE2A5FA0769B369C86A299160CE78F9A55176BEDE44CFD80E45F65449E2F83479DB4661B4F417605E0BB6;
        seed          = 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
        
        keygen_sim(seed,nist_expected);

        $display("\n\n=================SIGNING TEST STARTS=================\n\n"); 
        
        nist_privKey  = 384'h6B9D3DAD2E1B8C1C05B19875B6659F4DE23C3B667BF297BA9AA47740787137D896D5724E4C70A825F872C9EA60D2EDF5;        
        nist_h1       = 384'h9a9083505bc92276aec4be312696ef7bf3bf603f4bbd381196a029f340585312313bca4a9b5b890efee42c77b1ee25fe;
        nist_expected = 384'h94ED910D1A099DAD3254E9242AE85ABDE4BA15168EAF0CA87A555FD56D10FBCA2907E3E83BA95368623B8C4686915CF9;

        sign_sim(nist_h1,nist_privKey,nist_expected); 


        nist_privKey  = 384'h6B9D3DAD2E1B8C1C05B19875B6659F4DE23C3B667BF297BA9AA47740787137D896D5724E4C70A825F872C9EA60D2EDF5;
        nist_h1       = 384'h768412320f7b0aa5812fce428dc4706b3cae50e02a64caa16a782249bfe8efc4b7ef1ccb126255d196047dfedf17a0a9;
        nist_expected = 384'h015EE46A5BF88773ED9123A5AB0807962D193719503C527B031B4C2D225092ADA71F4A459BC0DA98ADB95837DB8312EA;

        sign_sim(nist_h1,nist_privKey,nist_expected); 

        nist_privKey  = 384'h14AEFB51DF578FF3D77662153B10CEE5C7930454AAE90E1A68C951E7466216DEEEAB7032856F3E6244194E9BE0923BE9;
        nist_h1       = 384'h31759BD97E875F3559D260BEE1C6F9995F330BA2D3DD2D93502E7E696C1900632E22672EB5C83CF761F592AAFC0E040A;
        nist_expected = 384'hC8958B49032629A9EAB4FE2F7CA7F3B7C768EC825D143FE65002904A6E91EF971AC8F6B3C1E97F132F99161AE3E58E38;

        sign_sim(nist_h1,nist_privKey,nist_expected); 

        nist_privKey  = 384'h14F93F145CE951B987CC52CD8EE5B916DF9042433E63F5771210B2E596709CFD4A9080EC1E0252F82E08333CBB259F0C;
        nist_h1       = 384'h31759BD97E875F3559D260BEE1C6F9995F330BA2D3DD2D93502E7E696C1900632E22672EB5C83CF761F592AAFC0E040A;
        nist_expected = 384'h1E006AABF131E194003305A959A0B5C070C2E298393FB399D3F54181900B089E5619EF4AD594C4C4C71F4479DD87E96A;

        sign_sim(nist_h1,nist_privKey,nist_expected);


        nist_privKey  = 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
        nist_h1       = 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
        nist_expected = 384'h7F68A6D896EA5DA62E78DEDB46F6662BC141F2F0B9E641ACC7342663FD51444E380FEA1DABBCA55F18987C0CFC10DF77;
        
        sign_sim(nist_h1,nist_privKey,nist_expected); 

    end
  endtask // hmac_drbg_test


  //----------------------------------------------------------------
  // always_debug()
  //
  // This always block enables to debug the state transactions
  //----------------------------------------------------------------
  always @(hmac_drbg_dut.nonce_st_reg)
  begin
      if (DEBUG)
        $display("--------------\n state\n %0d --------------", hmac_drbg_dut.nonce_st_reg);
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
