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
// doe_core_cbc_tb.sv
// --------
// DOE testbench for the DOE core CBC.
//
//
//======================================================================

module doe_core_cbc_tb();

//----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG     = 0;

  parameter CLK_HALF_PERIOD = 1;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;


  parameter DOE_128_BIT_KEY = 0;
  parameter DOE_256_BIT_KEY = 1;

  parameter DOE_DECIPHER = 1'b0;
  parameter DOE_ENCIPHER = 1'b1;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0]  cycle_ctr;
  reg [63 : 0]  error_ctr;
  reg [63 : 0]  tc_ctr;
  reg [63 : 0]  temp_ctr;

  reg           clk_tb;
  reg           reset_n_tb;
  reg           zeroize_tb;
  
  logic         core_encdec_tb;
  logic         core_init_tb;
  logic         core_next_tb;
  logic         core_ready_tb;
  logic [255:0] core_key_tb;
  logic         core_keylen_tb;
  logic [127:0] core_IV_tb;
  logic         IV_updated_tb;
  logic [127:0] core_block_tb;
  logic [127:0] core_result_tb;
  logic         core_valid_tb;


  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  doe_core_cbc dut (
              .clk(clk_tb),
              .reset_n(reset_n_tb),
              .zeroize(zeroize_tb),

              .encdec(core_encdec_tb),
              .init_cmd(core_init_tb),
              .next_cmd(core_next_tb),
              .ready(core_ready_tb),

              .key(core_key_tb),
              .keylen(core_keylen_tb),

              .IV(core_IV_tb),
              .IV_updated(IV_updated_tb),

              .block_msg(core_block_tb),
              .result(core_result_tb),
              .result_valid(core_valid_tb)
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
      #(CLK_PERIOD);
      cycle_ctr = cycle_ctr + 1;
    end


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
      cycle_ctr     = 0;
      error_ctr     = 0;
      tc_ctr        = 0;
      temp_ctr      = 0;

      clk_tb        = 0;
      reset_n_tb    = 0;
      zeroize_tb    = 0;

      core_encdec_tb  = 0;
      core_init_tb    = 0;
      core_next_tb    = 0;
      core_key_tb     = 0;
      core_keylen_tb  = 0;
      core_IV_tb      = 0;
      IV_updated_tb   = 0;
      core_block_tb   = 0;
    end
  endtask // init_sim


  //----------------------------------------------------------------
  // wait_ready()
  //
  // Wait for the ready flag in the dut to be set.
  // (Actually we wait for either ready or valid to be set.)
  //
  // Note: It is the callers responsibility to call the function
  // when the dut is actively processing and will in fact at some
  // point set the flag.
  //----------------------------------------------------------------
  task wait_ready;
    begin
      #(CLK_PERIOD);
      while (core_ready_tb == 0)
        begin
          #(CLK_PERIOD);
        end
    end
  endtask // wait_ready



  //----------------------------------------------------------------
  // init_key()
  //
  // init the key in the dut by writing the given key and
  // key length and then trigger init processing.
  //----------------------------------------------------------------
  task init_key(input [255 : 0] key, input key_length);
    begin
      core_key_tb = key;
      core_keylen_tb = key_length;
      core_init_tb = 1'b1;
      
      #CLK_PERIOD;
      core_init_tb       = 0;

      wait_ready();
      
    end
  endtask // init_key


  //----------------------------------------------------------------
  // cbc_mode_single_block_test()
  //
  // Perform CBC mode encryption or decryption single block test.
  //----------------------------------------------------------------
  task cbc_mode_single_block_test(input [7 : 0]   tc_number,
                                  input           encdec,
                                  input [255 : 0] key,
                                  input           key_length,
                                  input [127 : 0] IV,
                                  input [127 : 0] block,
                                  input [127 : 0] expected);
    reg [31  : 0] start_time;
    reg [31 : 0] end_time;
    
    begin
      $display("*** TC %0d CBC mode test started.", tc_number);
      if (encdec==0)
        $display("*** DECRYPTION *** ");
      else
        $display("*** ENCRYPTION *** ");
      tc_ctr = tc_ctr + 1;

      start_time = cycle_ctr;
      init_key(key, key_length);
      
      core_IV_tb = IV;
      IV_updated_tb = 1'b1;      
      
      #(CLK_PERIOD);
      IV_updated_tb = 0;
      core_block_tb = block;
      core_encdec_tb = encdec;
      core_next_tb       = 1'b1;

      #(CLK_PERIOD);
      core_next_tb       = 0;
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);

      if (core_result_tb == expected)
        begin
          $display("*** TC %0d successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected);
          $display("Got:      0x%032x", core_result_tb);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // cbc_mode_single_block_test


  //----------------------------------------------------------------
  // cbc_mode_double_block_test()
  //
  // Perform CBC mode encryption or decryption double block test.
  //----------------------------------------------------------------
  task cbc_mode_double_block_test(input [7 : 0]   tc_number,
                                  input           encdec,
                                  input [255 : 0] key,
                                  input           key_length,
                                  input [127 : 0] IV,
                                  input [127 : 0] block1,
                                  input [127 : 0] block2,
                                  input [127 : 0] expected1,
                                  input [127 : 0] expected2
                                  );
    reg [31  : 0] start_time;
    reg [31 : 0] end_time;
    
    begin
      $display("*** TC %0d CBC mode DOUBLE BLOCK test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      if (encdec==0)
        $display("*** DECRYPTION *** ");
      else
        $display("*** ENCRYPTION *** ");

      start_time = cycle_ctr;
      init_key(key, key_length);
      
      core_IV_tb = IV;
      IV_updated_tb = 1'b1;
      
      #CLK_PERIOD;
      IV_updated_tb = 0;
      // first block
      core_block_tb = block1;
      core_encdec_tb = encdec;
      core_next_tb       = 1'b1;
      
      #(CLK_PERIOD);
      core_next_tb       = 0;
      wait_ready();

      if (core_result_tb == expected1)
        begin
          $display("*** TC %0d first block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d first block NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected1);
          $display("Got:      0x%032x", core_result_tb);
          $display("");

          error_ctr = error_ctr + 1;
        end

      // second block
      core_block_tb = block2;
      core_next_tb       = 1'b1;
      
      #(CLK_PERIOD);
      core_next_tb       = 0;
      wait_ready();
      
      if (core_result_tb == expected2)
        begin
          $display("*** TC %0d second block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d second block NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected2);
          $display("Got:      0x%032x", core_result_tb);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // cbc_mode_dual_block_test




  //----------------------------------------------------------------
  // cbc_mode_quadratic_block_test()
  //
  // Perform CBC mode encryption or decryption quadratic block test.
  //----------------------------------------------------------------
  task cbc_mode_quadratic_block_test(input [7 : 0]   tc_number,
                                  input           encdec,
                                  input [255 : 0] key,
                                  input           key_length,
                                  input [127 : 0] IV,
                                  input [127 : 0] block1,
                                  input [127 : 0] block2,
                                  input [127 : 0] block3,
                                  input [127 : 0] block4,
                                  input [127 : 0] expected1,
                                  input [127 : 0] expected2,
                                  input [127 : 0] expected3,
                                  input [127 : 0] expected4
                                  );
    reg [31  : 0] start_time;
    reg [31 : 0] end_time;
    
    begin
      $display("*** TC %0d CBC mode FOUR BLOCK test started.", tc_number);
      tc_ctr = tc_ctr + 1;


      if (encdec==0)
        $display("*** DECRYPTION *** ");
      else
        $display("*** ENCRYPTION *** ");

      start_time = cycle_ctr;
      init_key(key, key_length);
      
      core_IV_tb = IV;
      IV_updated_tb = 1'b1;
      
      #CLK_PERIOD;
      IV_updated_tb = 0;
      // first block
      core_block_tb = block1;
      core_encdec_tb = encdec;
      core_next_tb       = 1'b1;
      
      #(CLK_PERIOD);
      core_next_tb       = 0;
      wait_ready();

      if (core_result_tb == expected1)
        begin
          $display("*** TC %0d first block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d first block NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected1);
          $display("Got:      0x%032x", core_result_tb);
          $display("");

          error_ctr = error_ctr + 1;
        end

      // second block
      core_block_tb = block2;
      core_next_tb       = 1'b1;
      
      #(CLK_PERIOD);
      core_next_tb       = 0;
      wait_ready();
      
      if (core_result_tb == expected2)
        begin
          $display("*** TC %0d second block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d second block NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected2);
          $display("Got:      0x%032x", core_result_tb);
          $display("");

          error_ctr = error_ctr + 1;
        end

      // third block
      core_block_tb = block3;
      core_next_tb       = 1'b1;
      
      #(CLK_PERIOD);
      core_next_tb       = 0;
      wait_ready();
      
      if (core_result_tb == expected3)
        begin
          $display("*** TC %0d third block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d third block NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected3);
          $display("Got:      0x%032x", core_result_tb);
          $display("");

          error_ctr = error_ctr + 1;
        end

      // final block
      core_block_tb = block4;
      core_next_tb       = 1'b1;
      
      #(CLK_PERIOD);
      core_next_tb       = 0;
      wait_ready();
      
      if (core_result_tb == expected4)
        begin
          $display("*** TC %0d fourth block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d fourth block NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected4);
          $display("Got:      0x%032x", core_result_tb);
          $display("");

          error_ctr = error_ctr + 1;
        end
      
      end_time = cycle_ctr - start_time;

    end
  endtask // cbc_mode_quat_block_test

  
  //----------------------------------------------------------------
  // doe_cbc_test()
  //
  //
  // Main test task will perform complete test of DOE.
  // Test vectors copied from the follwing documents.
  //
  // https://datatracker.ietf.org/doc/html/rfc3602
  // 
  //
  //----------------------------------------------------------------
  task doe_cbc_test;
    reg [255 : 0] nist_doe_key    ;
    

    reg [127 : 0] nist_IV0;

    reg [127 : 0] nist_plaintext0;

    reg [127 : 0] nist_plaintext1;

    reg [127 : 0] nist_plaintext2;

    reg [127 : 0] nist_plaintext3;

    reg [127 : 0] nist_cbc_128_enc_expected0;

    reg [127 : 0] nist_cbc_128_enc_expected1;

    reg [127 : 0] nist_cbc_128_enc_expected2;

    reg [127 : 0] nist_cbc_128_enc_expected3;

    reg [127 : 0] nist_cbc_256_enc_expected0;

    reg [127 : 0] nist_cbc_256_enc_expected1;

    reg [127 : 0] nist_cbc_256_enc_expected2;

    reg [127 : 0] nist_cbc_256_enc_expected3;

    begin
      nist_doe_key               = 256'hc286696d887c9aa0611bbb3e2025a45a00000000000000000000000000000000;
      nist_IV0                   = 128'h562e17996d093d28ddb3ba695a2e6f58;
      nist_plaintext0            = 128'h000102030405060708090a0b0c0d0e0f;
      nist_cbc_128_enc_expected0 = 128'hd296cd94c2cccf8a3a863028b5e1dc0a;

      $display("CBC 128 bit key single block tests");
      $display("---------------------");
      cbc_mode_single_block_test(8'h01, DOE_ENCIPHER, nist_doe_key    , DOE_128_BIT_KEY, nist_IV0,
                                 nist_plaintext0, nist_cbc_128_enc_expected0);
      $display("---------------------");
      cbc_mode_single_block_test(8'h01, DOE_DECIPHER, nist_doe_key    , DOE_128_BIT_KEY, nist_IV0,
                                 nist_cbc_128_enc_expected0, nist_plaintext0);

      $display("---------------------");
      
      nist_doe_key               = 256'h56e47a38c5598974bc46903dba29034900000000000000000000000000000000;
      nist_IV0                   = 128'h8ce82eefbea0da3c44699ed7db51b7d9;
      nist_plaintext0            = 128'ha0a1a2a3a4a5a6a7a8a9aaabacadaeaf;
      nist_cbc_128_enc_expected0 = 128'hc30e32ffedc0774e6aff6af0869f71aa;

      cbc_mode_single_block_test(8'h02, DOE_ENCIPHER, nist_doe_key    , DOE_128_BIT_KEY, nist_IV0,
                                 nist_plaintext0, nist_cbc_128_enc_expected0);
      $display("---------------------");
      cbc_mode_single_block_test(8'h03, DOE_DECIPHER, nist_doe_key    , DOE_128_BIT_KEY, nist_IV0,
                                 nist_cbc_128_enc_expected0, nist_plaintext0);
      $display("---------------------");
      
      nist_doe_key               = 256'hc286696d887c9aa0611bbb3e2025a45a00000000000000000000000000000000;
      nist_IV0                   = 128'h562e17996d093d28ddb3ba695a2e6f58;
      nist_plaintext0            = 128'h000102030405060708090a0b0c0d0e0f;
      nist_plaintext1            = 128'h101112131415161718191a1b1c1d1e1f;
      nist_cbc_128_enc_expected0 = 128'hd296cd94c2cccf8a3a863028b5e1dc0a;
      nist_cbc_128_enc_expected1 = 128'h7586602d253cfff91b8266bea6d61ab1;
      $display("---------------------");
      cbc_mode_double_block_test(8'h04, DOE_ENCIPHER, nist_doe_key    , DOE_128_BIT_KEY, nist_IV0,
                                 nist_plaintext0,
                                 nist_plaintext1,
                                 nist_cbc_128_enc_expected0,
                                 nist_cbc_128_enc_expected1);

      $display("---------------------");
      cbc_mode_double_block_test(8'h05, DOE_DECIPHER, nist_doe_key    , DOE_128_BIT_KEY, nist_IV0,
                                 nist_cbc_128_enc_expected0,
                                 nist_cbc_128_enc_expected1,
                                 nist_plaintext0,
                                 nist_plaintext1);
      $display("---------------------");      
      nist_doe_key               = 256'h56e47a38c5598974bc46903dba29034900000000000000000000000000000000;
      nist_IV0                   = 128'h8ce82eefbea0da3c44699ed7db51b7d9;
      nist_plaintext0            = 128'ha0a1a2a3a4a5a6a7a8a9aaabacadaeaf;
      nist_plaintext1            = 128'hb0b1b2b3b4b5b6b7b8b9babbbcbdbebf;
      nist_plaintext2            = 128'hc0c1c2c3c4c5c6c7c8c9cacbcccdcecf;
      nist_plaintext3            = 128'hd0d1d2d3d4d5d6d7d8d9dadbdcdddedf;
      nist_cbc_128_enc_expected0 = 128'hc30e32ffedc0774e6aff6af0869f71aa;
      nist_cbc_128_enc_expected1 = 128'h0f3af07a9a31a9c684db207eb0ef8e4e;
      nist_cbc_128_enc_expected2 = 128'h35907aa632c3ffdf868bb7b29d3d46ad;
      nist_cbc_128_enc_expected3 = 128'h83ce9f9a102ee99d49a53e87f4c3da55;

      cbc_mode_quadratic_block_test(8'h06, DOE_ENCIPHER, nist_doe_key    , DOE_128_BIT_KEY, nist_IV0,
                                 nist_plaintext0,
                                 nist_plaintext1,
                                 nist_plaintext2,
                                 nist_plaintext3,
                                 nist_cbc_128_enc_expected0,
                                 nist_cbc_128_enc_expected1,
                                 nist_cbc_128_enc_expected2,
                                 nist_cbc_128_enc_expected3);
      $display("---------------------");
      cbc_mode_quadratic_block_test(8'h07, DOE_DECIPHER, nist_doe_key    , DOE_128_BIT_KEY, nist_IV0,
                                 nist_cbc_128_enc_expected0,
                                 nist_cbc_128_enc_expected1,
                                 nist_cbc_128_enc_expected2,
                                 nist_cbc_128_enc_expected3,
                                 nist_plaintext0,
                                 nist_plaintext1,
                                 nist_plaintext2,
                                 nist_plaintext3);

      $display("---------------------");

      nist_doe_key               = 256'h603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4;
      nist_IV0                   = 128'h000102030405060708090A0B0C0D0E0F;
      nist_plaintext0            = 128'h6bc1bee22e409f96e93d7e117393172a;
      nist_cbc_128_enc_expected0 = 128'hf58c4c04d6e5f1ba779eabfb5f7bfbd6;

      $display("CBC 256 bit key single block tests");
      
      cbc_mode_single_block_test(8'h08, DOE_ENCIPHER, nist_doe_key, DOE_256_BIT_KEY, nist_IV0,
                                 nist_plaintext0, nist_cbc_128_enc_expected0);

      $display("---------------------");

    end
  endtask // doe_cbc_test

  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -= Testbench for DOE CBC started =-");
      $display("    ==============================");
      $display("");

      init_sim();
      reset_dut();

      doe_cbc_test();

      display_test_results();
      
      $display("");
      $display("*** DOE simulation done. ***");
      $finish;
    end // main

endmodule // doe_tb
