//======================================================================
//
// doe_tb.v
// --------
// Testbench for the doe top level wrapper.
//
//
// Author: Joachim Strombergson
// Copyright (c) 2014, Secworks Sweden AB
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or
// without modification, are permitted provided that the following
// conditions are met:
//
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
// FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
// COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
// BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
// STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
// ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
//======================================================================

module doe_tb();

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG     = 0;

  parameter CLK_HALF_PERIOD = 1;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  // The DUT address map.
  parameter BASE_ADDR        = 32'h60000000;

  parameter ADDR_NAME        = BASE_ADDR + 32'h00000000;
  parameter ADDR_VERSION     = BASE_ADDR + 32'h00000008;

  parameter ADDR_CTRL        = BASE_ADDR + 32'h00000010;
  parameter CTRL_INIT_BIT    = 0;
  parameter CTRL_NEXT_BIT    = 1;
  parameter CTRL_ENCDEC_BIT  = 2;
  parameter CTRL_KEYLEN_BIT  = 3;

  parameter ADDR_STATUS      = BASE_ADDR + 32'h00000018;
  parameter STATUS_READY_BIT = 0;
  parameter STATUS_VALID_BIT = 1;

  parameter ADDR_CONFIG      = BASE_ADDR + 32'h00000020;

  parameter ADDR_KEY0        = BASE_ADDR + 32'h00000040;
  parameter ADDR_KEY1        = BASE_ADDR + 32'h00000048;
  parameter ADDR_KEY2        = BASE_ADDR + 32'h00000050;
  parameter ADDR_KEY3        = BASE_ADDR + 32'h00000058;

  parameter ADDR_BLOCK0      = BASE_ADDR + 32'h00000080;
  parameter ADDR_BLOCK1      = BASE_ADDR + 32'h00000088;

  parameter ADDR_RESULT0     = BASE_ADDR + 32'h00000100;
  parameter ADDR_RESULT1     = BASE_ADDR + 32'h00000108;

  parameter DOE_128_BIT_KEY  = 0;
  parameter DOE_256_BIT_KEY  = 1;

  parameter DOE_DECIPHER     = 1'b0;
  parameter DOE_ENCIPHER     = 1'b1;


  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0]  cycle_ctr;
  reg [63 : 0]  error_ctr;
  reg [63 : 0]  tc_ctr;

  reg [63 : 0]  read_data;
  reg [127 : 0] result_data;

  reg           clk_tb;
  reg           reset_n_tb;
  reg           cs_tb;
  reg           we_tb;
  reg [31  : 0] address_tb;
  reg [63 : 0]  write_data_tb;
  wire [63 : 0] read_data_tb;


  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  doe dut(
           .clk(clk_tb),
           .reset_n(reset_n_tb),
           .cs(cs_tb),
           .we(we_tb),
           .address(address_tb),
           .write_data(write_data_tb),
           .read_data(read_data_tb)
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
      $display("ctrl_reg:   init   = 0x%01x, next   = 0x%01x", dut.init_reg, dut.next_reg);
      $display("config_reg: encdec = 0x%01x, length = 0x%01x ", dut.encdec_reg, dut.keylen_reg);
      $display("");

      $display("block: 0x%08x, 0x%08x, 0x%08x, 0x%08x",
               dut.block_reg[0], dut.block_reg[1], dut.block_reg[2], dut.block_reg[3]);
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
        end
      else
        begin
          $display("*** %02d tests completed - %02d test cases did not complete successfully.",
                   tc_ctr, error_ctr);
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

      clk_tb        = 0;
      reset_n_tb    = 1;

      cs_tb         = 0;
      we_tb         = 0;
      address_tb    = 32'h0;
      write_data_tb = 64'h0;
    end
  endtask // init_sim


  //----------------------------------------------------------------
  // write_word()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_word(input [31 : 0] address,
                  input [63 : 0] word);
    begin
      if (DEBUG)
        begin
          $display("*** Writing 0x%08x to 0x%02x.", word, address);
          $display("");
        end

      address_tb = address;
      write_data_tb = word;
      cs_tb = 1;
      we_tb = 1;
      #(2 * CLK_PERIOD);
      cs_tb = 0;
      we_tb = 0;
    end
  endtask // write_word


  //----------------------------------------------------------------
  // write_block()
  //
  // Write the given block to the dut.
  //----------------------------------------------------------------
  task write_block(input [127 : 0] block);
    begin
      write_word(ADDR_BLOCK0, block[127  :  64]);
      write_word(ADDR_BLOCK1, block[63   :   0]);
    end
  endtask // write_block


  //----------------------------------------------------------------
  // read_word()
  //
  // Read a data word from the given address in the DUT.
  // the word read will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_word(input [31 : 0]  address);
    begin
      address_tb = address;
      cs_tb = 1;
      we_tb = 0;
      #(CLK_PERIOD);
      read_data = read_data_tb;
      cs_tb = 0;

      if (DEBUG)
        begin
          $display("*** Reading 0x%08x from 0x%02x.", read_data, address);
          $display("");
        end
    end
  endtask // read_word


  //----------------------------------------------------------------
  // read_result()
  //
  // Read the result block in the dut.
  //----------------------------------------------------------------
  task read_result;
    begin
      read_word(ADDR_RESULT0);
      result_data[127 : 064] = read_data;
      read_word(ADDR_RESULT1);
      result_data[063 : 000] = read_data;
    end
  endtask // read_result


  //----------------------------------------------------------------
  // init_key()
  //
  // init the key in the dut by writing the given key and
  // key length and then trigger init processing.
  //----------------------------------------------------------------
  task init_key(input [255 : 0] key, input key_length);
    begin
      if (DEBUG)
        begin
          $display("key length: 0x%01x", key_length);
          $display("Initializing key expansion for key: 0x%016x", key);
        end

      write_word(ADDR_KEY0, key[255  : 192]);
      write_word(ADDR_KEY1, key[191  : 128]);
      write_word(ADDR_KEY2, key[127  :  64]);
      write_word(ADDR_KEY3, key[63   :   0]);

      if (key_length)
        begin
          write_word(ADDR_CONFIG, 8'h02);
        end
      else
        begin
          write_word(ADDR_CONFIG, 8'h00);
        end

      write_word(ADDR_CTRL, 8'h01);

      #(100 * CLK_PERIOD);
    end
  endtask // init_key


  //----------------------------------------------------------------
  // ecb_mode_single_block_test()
  //
  // Perform ECB mode encryption or decryption single block test.
  //----------------------------------------------------------------
  task ecb_mode_single_block_test(input [7 : 0]   tc_number,
                                  input           encdec,
                                  input [255 : 0] key,
                                  input           key_length,
                                  input [127 : 0] block,
                                  input [127 : 0] expected);
    begin
      $display("*** TC %0d ECB mode test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      init_key(key, key_length);
      write_block(block);
      dump_dut_state();

      write_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ encdec));
      write_word(ADDR_CTRL, 8'h02);

      #(100 * CLK_PERIOD);

      read_result();

      if (result_data == expected)
        begin
          $display("*** TC %0d successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // ecb_mode_single_block_test


  //----------------------------------------------------------------
  // doe_test()
  //
  // Main test task will perform complete NIST test of DOE.
  // Test vectors copied from the follwing NIST documents.
  //
  // NIST SP 800-38A:
  // http://csrc.nist.gov/publications/nistpubs/800-38a/sp800-38a.pdf
  //
  // NIST FIPS-197, Appendix C:
  // https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197.pdf
  //----------------------------------------------------------------
  task doe_test;
    reg [255 : 0] nist_doe128_key1;
    reg [255 : 0] nist_doe128_key2;
    reg [255 : 0] nist_doe256_key1;
    reg [255 : 0] nist_doe256_key2;

    reg [127 : 0] nist_plaintext0;
    reg [127 : 0] nist_plaintext1;
    reg [127 : 0] nist_plaintext2;
    reg [127 : 0] nist_plaintext3;
    reg [127 : 0] nist_plaintext4;

    reg [127 : 0] nist_ecb_128_enc_expected0;
    reg [127 : 0] nist_ecb_128_enc_expected1;
    reg [127 : 0] nist_ecb_128_enc_expected2;
    reg [127 : 0] nist_ecb_128_enc_expected3;
    reg [127 : 0] nist_ecb_128_enc_expected4;

    reg [127 : 0] nist_ecb_256_enc_expected0;
    reg [127 : 0] nist_ecb_256_enc_expected1;
    reg [127 : 0] nist_ecb_256_enc_expected2;
    reg [127 : 0] nist_ecb_256_enc_expected3;
    reg [127 : 0] nist_ecb_256_enc_expected4;

    begin
      nist_doe128_key1 = 256'h2b7e151628aed2a6abf7158809cf4f3c00000000000000000000000000000000;
      nist_doe128_key2 = 256'h000102030405060708090a0b0c0d0e0f00000000000000000000000000000000;
      nist_doe256_key1 = 256'h603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4;
      nist_doe256_key2 = 256'h000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f;

      nist_plaintext0 = 128'h6bc1bee22e409f96e93d7e117393172a;
      nist_plaintext1 = 128'hae2d8a571e03ac9c9eb76fac45af8e51;
      nist_plaintext2 = 128'h30c81c46a35ce411e5fbc1191a0a52ef;
      nist_plaintext3 = 128'hf69f2445df4f9b17ad2b417be66c3710;
      nist_plaintext4 = 128'h00112233445566778899aabbccddeeff;

      nist_ecb_128_enc_expected0 = 128'h3ad77bb40d7a3660a89ecaf32466ef97;
      nist_ecb_128_enc_expected1 = 128'hf5d3d58503b9699de785895a96fdbaaf;
      nist_ecb_128_enc_expected2 = 128'h43b1cd7f598ece23881b00e3ed030688;
      nist_ecb_128_enc_expected3 = 128'h7b0c785e27e8ad3f8223207104725dd4;
      nist_ecb_128_enc_expected4 = 128'h69c4e0d86a7b0430d8cdb78070b4c55a;

      nist_ecb_256_enc_expected0 = 128'hf3eed1bdb5d2a03c064b5a7e3db181f8;
      nist_ecb_256_enc_expected1 = 128'h591ccb10d410ed26dc5ba74a31362870;
      nist_ecb_256_enc_expected2 = 128'hb6ed21b99ca6f4f9f153e7b1beafed1d;
      nist_ecb_256_enc_expected3 = 128'h23304b7a39f9f3ff067d8d8f9e24ecc7;
      nist_ecb_256_enc_expected4 = 128'h8ea2b7ca516745bfeafc49904b496089;


      $display("ECB 128 bit key tests");
      $display("---------------------");
      ecb_mode_single_block_test(8'h01, DOE_ENCIPHER, nist_doe128_key1, DOE_128_BIT_KEY,
                                 nist_plaintext0, nist_ecb_128_enc_expected0);

      ecb_mode_single_block_test(8'h02, DOE_ENCIPHER, nist_doe128_key1, DOE_128_BIT_KEY,
                                nist_plaintext1, nist_ecb_128_enc_expected1);

      ecb_mode_single_block_test(8'h03, DOE_ENCIPHER, nist_doe128_key1, DOE_128_BIT_KEY,
                                 nist_plaintext2, nist_ecb_128_enc_expected2);

      ecb_mode_single_block_test(8'h04, DOE_ENCIPHER, nist_doe128_key1, DOE_128_BIT_KEY,
                                 nist_plaintext3, nist_ecb_128_enc_expected3);


      ecb_mode_single_block_test(8'h05, DOE_DECIPHER, nist_doe128_key1, DOE_128_BIT_KEY,
                                 nist_ecb_128_enc_expected0, nist_plaintext0);

      ecb_mode_single_block_test(8'h06, DOE_DECIPHER, nist_doe128_key1, DOE_128_BIT_KEY,
                                 nist_ecb_128_enc_expected1, nist_plaintext1);

      ecb_mode_single_block_test(8'h07, DOE_DECIPHER, nist_doe128_key1, DOE_128_BIT_KEY,
                                 nist_ecb_128_enc_expected2, nist_plaintext2);

      ecb_mode_single_block_test(8'h08, DOE_DECIPHER, nist_doe128_key1, DOE_128_BIT_KEY,
                                 nist_ecb_128_enc_expected3, nist_plaintext3);


      ecb_mode_single_block_test(8'h09, DOE_ENCIPHER, nist_doe128_key2, DOE_128_BIT_KEY,
                                 nist_plaintext4, nist_ecb_128_enc_expected4);

      ecb_mode_single_block_test(8'h0a, DOE_DECIPHER, nist_doe128_key2, DOE_128_BIT_KEY,
                                 nist_ecb_128_enc_expected4, nist_plaintext4);


      $display("");
      $display("ECB 256 bit key tests");
      $display("---------------------");
      ecb_mode_single_block_test(8'h10, DOE_ENCIPHER, nist_doe256_key1, DOE_256_BIT_KEY,
                                 nist_plaintext0, nist_ecb_256_enc_expected0);

      ecb_mode_single_block_test(8'h11, DOE_ENCIPHER, nist_doe256_key1, DOE_256_BIT_KEY,
                                 nist_plaintext1, nist_ecb_256_enc_expected1);

      ecb_mode_single_block_test(8'h12, DOE_ENCIPHER, nist_doe256_key1, DOE_256_BIT_KEY,
                                 nist_plaintext2, nist_ecb_256_enc_expected2);

      ecb_mode_single_block_test(8'h13, DOE_ENCIPHER, nist_doe256_key1, DOE_256_BIT_KEY,
                                 nist_plaintext3, nist_ecb_256_enc_expected3);


      ecb_mode_single_block_test(8'h14, DOE_DECIPHER, nist_doe256_key1, DOE_256_BIT_KEY,
                                 nist_ecb_256_enc_expected0, nist_plaintext0);

      ecb_mode_single_block_test(8'h15, DOE_DECIPHER, nist_doe256_key1, DOE_256_BIT_KEY,
                                 nist_ecb_256_enc_expected1, nist_plaintext1);

      ecb_mode_single_block_test(8'h16, DOE_DECIPHER, nist_doe256_key1, DOE_256_BIT_KEY,
                                 nist_ecb_256_enc_expected2, nist_plaintext2);

      ecb_mode_single_block_test(8'h17, DOE_DECIPHER, nist_doe256_key1, DOE_256_BIT_KEY,
                                 nist_ecb_256_enc_expected3, nist_plaintext3);


      ecb_mode_single_block_test(8'h18, DOE_ENCIPHER, nist_doe256_key2, DOE_256_BIT_KEY,
                                 nist_plaintext4, nist_ecb_256_enc_expected4);

      ecb_mode_single_block_test(8'h19, DOE_DECIPHER, nist_doe256_key2, DOE_256_BIT_KEY,
                                 nist_ecb_256_enc_expected4, nist_plaintext4);
    end
  endtask // doe_test


  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -= Testbench for DOE started =-");
      $display("    ==============================");
      $display("");

      init_sim();
      dump_dut_state();
      reset_dut();
      dump_dut_state();

      doe_test();

      display_test_results();

      $display("");
      $display("*** DOE simulation done. ***");
      $finish;
    end // main
endmodule // doe_tb

//======================================================================
// EOF doe_tb.v
//======================================================================
