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
// aes_ctrl_tb.sv
// --------
// AES testbench for the AES AHb_lite interface controller.
//
//
//======================================================================

module aes_ctrl_64bit_tb();

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

  parameter AES_128_BIT_KEY = 0;
  parameter AES_256_BIT_KEY = 1;

  parameter AES_DECIPHER = 1'b0;
  parameter AES_ENCIPHER = 1'b1;

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  parameter AHB_ADDR_WIDTH = 32;
  parameter AHB_DATA_WIDTH = 64;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0]  cycle_ctr;
  reg [63 : 0]  error_ctr;
  reg [63 : 0]  tc_ctr;

  reg           clk_tb;
  reg           reset_n_tb;

  reg [AHB_ADDR_WIDTH-1:0]  hadrr_i_tb;
  reg [AHB_DATA_WIDTH-1:0]  hwdata_i_tb;
  reg           hsel_i_tb;
  reg           hwrite_i_tb; 
  reg           hmastlock_i_tb;
  reg           hready_i_tb;
  reg [1:0]     htrans_i_tb;
  reg [3:0]     hprot_i_tb;
  reg [2:0]     hburst_i_tb;
  reg [2:0]     hsize_i_tb;

  wire          hresp_o_tb;
  wire          hreadyout_o_tb;
  wire [AHB_DATA_WIDTH-1:0] hrdata_o_tb;

  reg [63 : 0]  read_data;
  reg [127 : 0] result_data;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  aes_ctrl #(
             .AHB_DATA_WIDTH(64),
             .AHB_ADDR_WIDTH(32),
             .BYPASS_HSEL(0)
            )
            dut (
             .clk(clk_tb),
             .reset_n(reset_n_tb),

             .hadrr_i(hadrr_i_tb),
             .hwdata_i(hwdata_i_tb),
             .hsel_i(hsel_i_tb),
             .hwrite_i(hwrite_i_tb),
             .hmastlock_i(hmastlock_i_tb),
             .hready_i(hready_i_tb),
             .htrans_i(htrans_i_tb),
             .hprot_i(hprot_i_tb),
             .hburst_i(hburst_i_tb),
             .hsize_i(hsize_i_tb),

             .hresp_o(hresp_o_tb),
             .hreadyout_o(hreadyout_o_tb),
             .hrdata_o(hrdata_o_tb)
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
      reset_n_tb    = 0;

      hadrr_i_tb      = 'Z;
      hwdata_i_tb     = 'Z;
      hsel_i_tb       = 0;
      hwrite_i_tb     = 0;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 3'b011;
    end
  endtask // init_sim


  //----------------------------------------------------------------
  // check_name_version()
  //
  // Read the name and version from the DUT.
  //----------------------------------------------------------------
  task check_name_version;
    reg [63 : 0] name;
    reg [63 : 0] version;
    begin

      read_single_word(ADDR_NAME);
      name = read_data;
      read_single_word(ADDR_VERSION);
      version = read_data;

      $display("DUT name: %c%c%c%c%c%c%c%c",
               name[15 :  8], name[7  :  0],
               name[31 : 24], name[23 : 16], 
               name[47 : 40], name[39 : 32],
               name[63 : 56], name[55 : 48]);
      $display("DUT version: %c%c%c%c%c%c%c%c",
               version[15 :  8], version[7  :  0],
               version[31 : 24], version[23 : 16],
               version[47 : 40], version[39 : 32],
               version[63 : 56], version[55 : 48]);
    end
  endtask // check_name_version

  //----------------------------------------------------------------
  // write_single_word()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_single_word(input [31 : 0]  address,
                  input [63 : 0] word);
    begin
      hsel_i_tb       = 1;
      hadrr_i_tb      = address;
      hwrite_i_tb     = 1;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_BUSY;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 3'b011;
      #(CLK_PERIOD);

      hadrr_i_tb      = 'Z;
      hwdata_i_tb     = word;
      hwrite_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
    end
  endtask // write_single_word


  //----------------------------------------------------------------
  // write_block()
  //
  // Write the given block to the dut.
  //----------------------------------------------------------------
  task write_block(input [127 : 0] block);
    begin
      write_single_word(ADDR_BLOCK0, block[127  :  64]);
      write_single_word(ADDR_BLOCK1, block[63   :   0]);
    end
  endtask // write_block


  //----------------------------------------------------------------
  // read_word()
  //
  // Read a data word from the given address in the DUT.
  // the word read will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_single_word(input [31 : 0]  address);
    begin
      hsel_i_tb       = 1;
      hadrr_i_tb      = address;
      hwrite_i_tb     = 0;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_BUSY;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 3'b011;
      #(CLK_PERIOD);
      
      hwdata_i_tb     = 0;
      hadrr_i_tb     = 'Z;
      htrans_i_tb     = AHB_HTRANS_IDLE;

      #(CLK_PERIOD);
      read_data = hrdata_o_tb;
      hsel_i_tb       = 0;
    end
  endtask // read_word



  //----------------------------------------------------------------
  // read_result()
  //
  // Read the result block in the dut.
  //----------------------------------------------------------------
  task read_result;
    begin
      read_single_word(ADDR_RESULT0);
      result_data[127 : 64] = read_data;
      read_single_word(ADDR_RESULT1);
      result_data[63  :  0] = read_data;
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
      write_single_word(ADDR_KEY0, key[255  : 192]);
      write_single_word(ADDR_KEY1, key[191  : 128]);
      write_single_word(ADDR_KEY2, key[127  :  64]);
      write_single_word(ADDR_KEY3, key[63   :   0]);

      if (key_length)
          write_single_word(ADDR_CONFIG, 8'h02);
      else
          write_single_word(ADDR_CONFIG, 8'h00);

      write_single_word(ADDR_CTRL, 8'h01);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

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

      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ encdec));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;
      
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
  // aes_test()
  //
  // Main test task will perform complete NIST test of AES.
  // Test vectors copied from the follwing NIST documents.
  //
  // NIST SP 800-38A:
  // http://csrc.nist.gov/publications/nistpubs/800-38a/sp800-38a.pdf
  //
  // NIST FIPS-197, Appendix C:
  // https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197.pdf
  //----------------------------------------------------------------
  task aes_test;
    reg [255 : 0] nist_aes128_key1;
    reg [255 : 0] nist_aes128_key2;
    reg [255 : 0] nist_aes256_key1;
    reg [255 : 0] nist_aes256_key2;

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
      nist_aes128_key1 = 256'h2b7e151628aed2a6abf7158809cf4f3c00000000000000000000000000000000;
      nist_aes128_key2 = 256'h000102030405060708090a0b0c0d0e0f00000000000000000000000000000000;
      nist_aes256_key1 = 256'h603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4;
      nist_aes256_key2 = 256'h000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f;

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
      ecb_mode_single_block_test(8'h01, AES_ENCIPHER, nist_aes128_key1, AES_128_BIT_KEY,
                                 nist_plaintext0, nist_ecb_128_enc_expected0);

      ecb_mode_single_block_test(8'h02, AES_ENCIPHER, nist_aes128_key1, AES_128_BIT_KEY,
                                nist_plaintext1, nist_ecb_128_enc_expected1);

      ecb_mode_single_block_test(8'h03, AES_ENCIPHER, nist_aes128_key1, AES_128_BIT_KEY,
                                 nist_plaintext2, nist_ecb_128_enc_expected2);

      ecb_mode_single_block_test(8'h04, AES_ENCIPHER, nist_aes128_key1, AES_128_BIT_KEY,
                                 nist_plaintext3, nist_ecb_128_enc_expected3);


      ecb_mode_single_block_test(8'h05, AES_DECIPHER, nist_aes128_key1, AES_128_BIT_KEY,
                                 nist_ecb_128_enc_expected0, nist_plaintext0);

      ecb_mode_single_block_test(8'h06, AES_DECIPHER, nist_aes128_key1, AES_128_BIT_KEY,
                                 nist_ecb_128_enc_expected1, nist_plaintext1);

      ecb_mode_single_block_test(8'h07, AES_DECIPHER, nist_aes128_key1, AES_128_BIT_KEY,
                                 nist_ecb_128_enc_expected2, nist_plaintext2);

      ecb_mode_single_block_test(8'h08, AES_DECIPHER, nist_aes128_key1, AES_128_BIT_KEY,
                                 nist_ecb_128_enc_expected3, nist_plaintext3);


      ecb_mode_single_block_test(8'h09, AES_ENCIPHER, nist_aes128_key2, AES_128_BIT_KEY,
                                 nist_plaintext4, nist_ecb_128_enc_expected4);

      ecb_mode_single_block_test(8'h0a, AES_DECIPHER, nist_aes128_key2, AES_128_BIT_KEY,
                                 nist_ecb_128_enc_expected4, nist_plaintext4);


      $display("");
      $display("ECB 256 bit key tests");
      $display("---------------------");
      ecb_mode_single_block_test(8'h10, AES_ENCIPHER, nist_aes256_key1, AES_256_BIT_KEY,
                                 nist_plaintext0, nist_ecb_256_enc_expected0);

      ecb_mode_single_block_test(8'h11, AES_ENCIPHER, nist_aes256_key1, AES_256_BIT_KEY,
                                 nist_plaintext1, nist_ecb_256_enc_expected1);

      ecb_mode_single_block_test(8'h12, AES_ENCIPHER, nist_aes256_key1, AES_256_BIT_KEY,
                                 nist_plaintext2, nist_ecb_256_enc_expected2);

      ecb_mode_single_block_test(8'h13, AES_ENCIPHER, nist_aes256_key1, AES_256_BIT_KEY,
                                 nist_plaintext3, nist_ecb_256_enc_expected3);


      ecb_mode_single_block_test(8'h14, AES_DECIPHER, nist_aes256_key1, AES_256_BIT_KEY,
                                 nist_ecb_256_enc_expected0, nist_plaintext0);

      ecb_mode_single_block_test(8'h15, AES_DECIPHER, nist_aes256_key1, AES_256_BIT_KEY,
                                 nist_ecb_256_enc_expected1, nist_plaintext1);

      ecb_mode_single_block_test(8'h16, AES_DECIPHER, nist_aes256_key1, AES_256_BIT_KEY,
                                 nist_ecb_256_enc_expected2, nist_plaintext2);

      ecb_mode_single_block_test(8'h17, AES_DECIPHER, nist_aes256_key1, AES_256_BIT_KEY,
                                 nist_ecb_256_enc_expected3, nist_plaintext3);


      ecb_mode_single_block_test(8'h18, AES_ENCIPHER, nist_aes256_key2, AES_256_BIT_KEY,
                                 nist_plaintext4, nist_ecb_256_enc_expected4);

      ecb_mode_single_block_test(8'h19, AES_DECIPHER, nist_aes256_key2, AES_256_BIT_KEY,
                                 nist_ecb_256_enc_expected4, nist_plaintext4);
    end
  endtask // aes_test


  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -= Testbench for AES started =-");
      $display("    ==============================");
      $display("");

      init_sim();
      reset_dut();

      check_name_version();

      aes_test();

      display_test_results();
      
      $display("");
      $display("*** AES simulation done. ***");
      $finish;
    end // main

endmodule // aes_tb
