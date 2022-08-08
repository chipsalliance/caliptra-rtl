//======================================================================
//
// hmac_drbg_tb.sv
//
//
// Author: Emre Karabulut
// 
// This test to check HMAC DRBG functionality
// Empty test
//======================================================================

module hmac_drbg_tb();


  //----------------------------------------------------------------
  // Local Parameters.
  //----------------------------------------------------------------
    localparam SEED_LENGTH=384;

    localparam CLK_HALF_PERIOD = 1;
    localparam CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

    localparam DEBUG     = 0;
  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0]  cycle_ctr;
  reg [63 : 0]  error_ctr;
  reg [63 : 0]  tc_ctr;

  reg [7 : 0]   tc_number;

  // Clock and reset.
  reg                        clk_tb;
  reg                        reset_n_tb;

  //Control
  reg                        KEYGEN_SIGN_tb;
  reg                        init_tb;
  wire                       ready_tb;
  wire                       valid_tb;

  //Data
  reg   [SEED_LENGTH-1 : 0]  seed_tb;
  reg   [383 : 0]            privKey_tb;
  reg   [383 : 0]            h1_tb;
  wire  [383 : 0]            nonce_tb;


  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  hmac_drbg 
  #(
        .SEED_LENGTH(SEED_LENGTH)
  ) hmac_drbg_dut
  (
        .clk(clk_tb),
        .reset_n(reset_n_tb),
        .KEYGEN_SIGN(KEYGEN_SIGN_tb),
        .init(init_tb),
        .ready(ready_tb),
        .valid(valid_tb),
        .seed(seed_tb),
        .privKey(privKey_tb),
        .h1(h1_tb),
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
      $display("STATE  = 0x%02d", hmac_drbg_dut.nonce_st);
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
          $display("*** All %02d test cases completed successfully", tc_ctr);
          $display("* TESTCASE PASSED");
        end
      else
        begin
          $display("*** %02d tests completed - %02d test cases did not complete successfully.",
                   tc_ctr, error_ctr);
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
      tc_ctr            = 0;
      tc_number         = 0;

      clk_tb            = 0;
      reset_n_tb        = 1;

      KEYGEN_SIGN_tb    = 0;
      init_tb           = 0;
    
      //Data
      seed_tb           = 384'h0;
      privKey_tb        = 384'h0;
      h1_tb             = 384'h0;
    end
  endtask // init_sim


  //----------------------------------------------------------------
  // keygen_sim()
  //
  // HMAC DRBG works for key generation step
  //----------------------------------------------------------------
  task keygen_sim(input [383 : 0] seed, input  [383 : 0] nonce_expected);
    begin
        h1_tb = 384'h0;
        privKey_tb = 384'h0;
        if (!ready_tb)
            wait(ready_tb);
            
        $display("The HMAC DRBG core is triggered...");
        KEYGEN_SIGN_tb = 1'b0;        
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
        h1_tb = h1;
        privKey_tb = privKey;
        if (!ready_tb)
            wait(ready_tb);
            
        $display("The HMAC DRBG core is triggered...");
        KEYGEN_SIGN_tb = 1'b1;
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

        $display("\n\n=================SIGNING TEST STARTS=================\n\n"); 
        
        nist_privKey  = 384'h6B9D3DAD2E1B8C1C05B19875B6659F4DE23C3B667BF297BA9AA47740787137D896D5724E4C70A825F872C9EA60D2EDF5;        
        nist_h1       = 384'h9a9083505bc92276aec4be312696ef7bf3bf603f4bbd381196a029f340585312313bca4a9b5b890efee42c77b1ee25fe;
        nist_expected = 384'h94ED910D1A099DAD3254E9242AE85ABDE4BA15168EAF0CA87A555FD56D10FBCA2907E3E83BA95368623B8C4686915CF9;

        sign_sim(nist_h1,nist_privKey,nist_expected); 


        nist_privKey  = 384'h6B9D3DAD2E1B8C1C05B19875B6659F4DE23C3B667BF297BA9AA47740787137D896D5724E4C70A825F872C9EA60D2EDF5;
        nist_h1       = 384'h768412320f7b0aa5812fce428dc4706b3cae50e02a64caa16a782249bfe8efc4b7ef1ccb126255d196047dfedf17a0a9;
        nist_expected = 384'h015EE46A5BF88773ED9123A5AB0807962D193719503C527B031B4C2D225092ADA71F4A459BC0DA98ADB95837DB8312EA;

        sign_sim(nist_h1,nist_privKey,nist_expected); 

    end
  endtask // hmac_drbg_test


  //----------------------------------------------------------------
  // always_debug()
  //
  // This always block enables to debug the state transactions
  //----------------------------------------------------------------
  always @(hmac_drbg_dut.nonce_st)
  begin
      if (DEBUG)
        $display("--------------\n state\n %0d --------------", hmac_drbg_dut.nonce_st);
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
      dump_dut_state();
      reset_dut();
      dump_dut_state();

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
