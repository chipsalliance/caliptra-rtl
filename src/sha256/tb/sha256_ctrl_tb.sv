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
// sha256_ctrl_tb.sv
// --------
// sha256 testbench for the sha256 AHb_lite interface controller.
//
//
//======================================================================

module sha256_ctrl_tb();

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG = 0;

  parameter CLK_HALF_PERIOD = 2;
  parameter CLK_PERIOD = 2 * CLK_HALF_PERIOD;

  // The address map.

  parameter ADDR_NAME0       = 32'h00000000;
  parameter ADDR_NAME1       = 32'h00000004;
  parameter ADDR_VERSION0    = 32'h00000008;
  parameter ADDR_VERSION1    = 32'h0000000c;

  parameter ADDR_CTRL        = 32'h00000010;
  parameter CTRL_INIT_VALUE  = 2'h1;
  parameter CTRL_NEXT_VALUE  = 2'h2;

  parameter ADDR_STATUS      = 32'h00000018;
  parameter STATUS_READY_BIT = 0;
  parameter STATUS_VALID_BIT = 1;

  parameter ADDR_BLOCK0    = 32'h00000080;
  parameter ADDR_BLOCK1    = 32'h00000084;
  parameter ADDR_BLOCK2    = 32'h00000088;
  parameter ADDR_BLOCK3    = 32'h0000008c;
  parameter ADDR_BLOCK4    = 32'h00000090;
  parameter ADDR_BLOCK5    = 32'h00000094;
  parameter ADDR_BLOCK6    = 32'h00000098;
  parameter ADDR_BLOCK7    = 32'h0000009c;
  parameter ADDR_BLOCK8    = 32'h000000a0;
  parameter ADDR_BLOCK9    = 32'h000000a4;
  parameter ADDR_BLOCK10   = 32'h000000a8;
  parameter ADDR_BLOCK11   = 32'h000000ac;
  parameter ADDR_BLOCK12   = 32'h000000b0;
  parameter ADDR_BLOCK13   = 32'h000000b4;
  parameter ADDR_BLOCK14   = 32'h000000b8;
  parameter ADDR_BLOCK15   = 32'h000000bc;

  parameter ADDR_DIGEST0   = 32'h00000100;
  parameter ADDR_DIGEST1   = 32'h00000104;
  parameter ADDR_DIGEST2   = 32'h00000108;
  parameter ADDR_DIGEST3   = 32'h0000010c;
  parameter ADDR_DIGEST4   = 32'h00000110;
  parameter ADDR_DIGEST5   = 32'h00000114;
  parameter ADDR_DIGEST6   = 32'h00000118;
  parameter ADDR_DIGEST7   = 32'h0000011c;

  parameter SHA224_MODE    = 0;
  parameter SHA256_MODE    = 1;

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  parameter AHB_ADDR_WIDTH = 32;
  parameter AHB_DATA_WIDTH = 32;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [31 : 0] cycle_ctr;
  reg [31 : 0] error_ctr;
  reg [31 : 0] tc_ctr;

  reg           clk_tb;
  reg           reset_n_tb;
  reg           cptra_pwrgood_tb;

  reg [AHB_ADDR_WIDTH-1:0]  haddr_i_tb;
  reg [AHB_DATA_WIDTH-1:0]  hwdata_i_tb;
  reg           hsel_i_tb;
  reg           hwrite_i_tb; 
  reg           hready_i_tb;
  reg [1:0]     htrans_i_tb;
  reg [2:0]     hsize_i_tb;

  wire          hresp_o_tb;
  wire          hreadyout_o_tb;
  wire [AHB_DATA_WIDTH-1:0] hrdata_o_tb;

  reg [31 : 0]  read_data;
  reg [255 : 0] digest_data;

  //bind coverage file
  sha256_ctrl_cov_bind i_sha256_ctrl_cov_bind();

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  sha256_ctrl #(
             .AHB_DATA_WIDTH(32),
             .AHB_ADDR_WIDTH(32)
            )
            dut (
             .clk(clk_tb),
             .reset_n(reset_n_tb),
             .cptra_pwrgood(cptra_pwrgood_tb),

             .haddr_i(haddr_i_tb),
             .hwdata_i(hwdata_i_tb),
             .hsel_i(hsel_i_tb),
             .hwrite_i(hwrite_i_tb),
             .hready_i(hready_i_tb),
             .htrans_i(htrans_i_tb),
             .hsize_i(hsize_i_tb),

             .hresp_o(hresp_o_tb),
             .hreadyout_o(hreadyout_o_tb),
             .hrdata_o(hrdata_o_tb),

             .error_intr(),
             .notif_intr(),
             .debugUnlock_or_scan_mode_switch()
            );


  //----------------------------------------------------------------
  // clk_gen
  //
  // Clock generator process.
  //----------------------------------------------------------------
  always
    begin : clk_gen
      #CLK_HALF_PERIOD 
      clk_tb = !clk_tb;
    end // clk_gen


  //----------------------------------------------------------------
  // sys_monitor
  //
  // Generates a cycle counter and displays information about
  // the dut as needed.
  //----------------------------------------------------------------
  always
    begin : sys_monitor
      #(CLK_PERIOD);
      cycle_ctr = cycle_ctr + 1;
    end


  //----------------------------------------------------------------
  // reset_dut()
  //
  // Toggles reset to force the DUT into a well defined state.
  //----------------------------------------------------------------
    task reset_dut;
    begin
      $display("*** Toggle reset.");
      cptra_pwrgood_tb = '0;
      reset_n_tb = 0;

      #(2 * CLK_PERIOD);
      cptra_pwrgood_tb = 1;

      #(2 * CLK_PERIOD);
      reset_n_tb = 1;
    end
  endtask // reset_dut


  //----------------------------------------------------------------
  // init_sim()
  //
  // Initialize all counters and testbed functionality as well
  // as setting the DUT inputs to defined values.
  //----------------------------------------------------------------
  task init_sim;
    begin
      cycle_ctr = '0;
      error_ctr = '0;
      tc_ctr    = '0;

      clk_tb        = 0;
      reset_n_tb    = 0;
      cptra_pwrgood_tb = 0;

      haddr_i_tb      = 0;
      hwdata_i_tb     = 0;
      hsel_i_tb       = 0;
      hwrite_i_tb     = 0;
      hready_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hsize_i_tb      = 3'b011;
    end
  endtask // init_dut


  //----------------------------------------------------------------
  // display_test_result()
  //
  // Display the accumulated test results.
  //----------------------------------------------------------------
  task display_test_result;
    begin
      if (error_ctr == 0)
        begin
          $display("*** All %02d test cases completed successfully.", tc_ctr);
          $display("* TESTCASE PASSED");
        end
      else
        begin
          $display("*** %02d test cases completed.", tc_ctr);
          $display("*** %02d errors detected during testing.", error_ctr);
          $display("* TESTCASE FAILED");
        end
    end
  endtask // display_test_result


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
      read_data = 0;
      #(CLK_PERIOD);

      while (read_data == 0)
        begin
          read_single_word(ADDR_STATUS);
        end
    end
  endtask // wait_ready



  //----------------------------------------------------------------
  // write_single_word()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_single_word(input [31 : 0]  address,
                  input [31 : 0] word);
    begin
      hsel_i_tb       = 1;
      haddr_i_tb      = address;
      hwrite_i_tb     = 1;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hsize_i_tb      = 3'b010;
      #(CLK_PERIOD);

      haddr_i_tb      = 'Z;
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
  task write_block(input [511 : 0] block);
    begin
      write_single_word(ADDR_BLOCK0 , block[511  : 480]);
      write_single_word(ADDR_BLOCK1 , block[479  : 448]);
      write_single_word(ADDR_BLOCK2 , block[447  : 416]);
      write_single_word(ADDR_BLOCK3 , block[415  : 384]);
      write_single_word(ADDR_BLOCK4 , block[383  : 352]);
      write_single_word(ADDR_BLOCK5 , block[351  : 320]);
      write_single_word(ADDR_BLOCK6 , block[319  : 288]);
      write_single_word(ADDR_BLOCK7 , block[287  : 256]);
      write_single_word(ADDR_BLOCK8 , block[255  : 224]);
      write_single_word(ADDR_BLOCK9 , block[223  : 192]);
      write_single_word(ADDR_BLOCK10, block[191  : 160]);
      write_single_word(ADDR_BLOCK11, block[159  : 128]);
      write_single_word(ADDR_BLOCK12, block[127  :  96]);
      write_single_word(ADDR_BLOCK13, block[95   :  64]);
      write_single_word(ADDR_BLOCK14, block[63   :  32]);
      write_single_word(ADDR_BLOCK15, block[31   :   0]);
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
      haddr_i_tb      = address;
      hwrite_i_tb     = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hsize_i_tb      = 3'b010;
      #(CLK_PERIOD);
      
      hwdata_i_tb     = 0;
      haddr_i_tb     = 'Z;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      read_data = hrdata_o_tb;    
    end
  endtask // read_word


  //----------------------------------------------------------------
  // check_name_version()
  //
  // Read the name and version from the DUT.
  //----------------------------------------------------------------
  task check_name_version;
    reg [31 : 0] name0;
    reg [31 : 0] name1;
    reg [31 : 0] version0;
    reg [31 : 0] version1;
    begin

      read_single_word(ADDR_NAME0);
      name0 = hrdata_o_tb;
      read_single_word(ADDR_NAME1);
      name1 = hrdata_o_tb;
      read_single_word(ADDR_VERSION0);
      version0 = hrdata_o_tb;
      read_single_word(ADDR_VERSION1);
      version1 = hrdata_o_tb;

      $display("DUT name: %c%c%c%c%c%c%c%c",
               name0[15 :  8], name0[7  :  0],
               name0[31 : 24], name0[23 : 16], 
               name1[15 :  8], name1[7  :  0],
               name1[31 : 24], name1[23 : 16]);
      $display("DUT version: %c%c%c%c%c%c%c%c",
               version0[15 :  8], version0[7  :  0],
               version0[31 : 24], version0[23 : 16],
               version1[15 :  8], version1[7  :  0],
               version1[31 : 24], version1[23 : 16]);
    end
  endtask // check_name_version


  //----------------------------------------------------------------
  // read_digest()
  //
  // Read the digest in the dut. The resulting digest will be
  // available in the global variable digest_data.
  //----------------------------------------------------------------
  task read_digest;
    begin
      read_single_word(ADDR_DIGEST0);
      digest_data[255 : 224] = hrdata_o_tb;
      read_single_word(ADDR_DIGEST1);
      digest_data[223 : 192] = hrdata_o_tb;
      read_single_word(ADDR_DIGEST2);
      digest_data[191 : 160] = hrdata_o_tb;
      read_single_word(ADDR_DIGEST3);
      digest_data[159 : 128] = hrdata_o_tb;
      read_single_word(ADDR_DIGEST4);
      digest_data[127 :  96] = hrdata_o_tb;
      read_single_word(ADDR_DIGEST5);
      digest_data[95  :  64] = hrdata_o_tb;
      read_single_word(ADDR_DIGEST6);
      digest_data[63  :  32] = hrdata_o_tb;
      read_single_word(ADDR_DIGEST7);
      digest_data[31  :   0] = hrdata_o_tb;
    end
  endtask // read_digest


  //----------------------------------------------------------------
  // single_block_test()
  //
  //
  // Perform test of a single block digest.
  //----------------------------------------------------------------
  task single_block_test(input           mode,
                         input [511 : 0] block,
                         input [255 : 0] expected);
    
    reg [31 : 0] start_time;
    reg [31 : 0] end_time;

    begin
      $display("*** TC%01d - Single block test started.", tc_ctr);

      write_block(block);

      write_single_word(ADDR_CTRL, {mode, CTRL_INIT_VALUE});
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);

      start_time = cycle_ctr;

      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);
      read_digest();

      write_single_word(ADDR_CTRL, {28'h0, 1'b1, 3'b0}); //zeroize

      // We need to ignore the LSW in SHA224 mode.
      if (mode == SHA224_MODE)
        digest_data[31 : 0] = 32'h0;

      if (digest_data == expected)
        begin
          $display("TC%01d: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR.", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end
      $display("*** TC%01d - Single block test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // single_block_test


  //----------------------------------------------------------------
  // double_block_test()
  //
  //
  // Perform test of a double block digest. Note that we check
  // the digests for both the first and final block.
  //----------------------------------------------------------------
  task double_block_test(input           mode,
                         input [511 : 0] block0,
                         input [255 : 0] expected0,
                         input [511 : 0] block1,
                         input [255 : 0] expected1
                        );
    begin
      $display("*** TC%01d - Double block test started.", tc_ctr);

      // First block
      write_block(block0);

      write_single_word(ADDR_CTRL, {mode, CTRL_INIT_VALUE});
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      read_digest();

      // We need to ignore the LSW in SHA224 mode.
      if (mode == SHA224_MODE)
        digest_data[31 : 0] = 32'h0;

      if (digest_data == expected0)
        begin
          $display("TC%01d first block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in first digest", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected0);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      // Final block
      write_block(block1);

      write_single_word(ADDR_CTRL, {mode, CTRL_NEXT_VALUE});
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      read_digest();

      write_single_word(ADDR_CTRL, {28'h0, 1'b1, 3'b0}); //zeroize

      // We need to ignore the LSW in SHA224 mode.
      if (mode == SHA224_MODE)
        digest_data[31 : 0] = 32'h0;

      if (digest_data == expected1)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected1);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - Double block test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // double_block_test


  //----------------------------------------------------------------
  // continuous_cmd_test()
  //
  //
  // Perform test of a double block digest.
  //----------------------------------------------------------------
  task continuous_cmd_test(input         mode,
                         input [511 : 0] block0,
                         input [255 : 0] expected0,
                         input [511 : 0] block1,
                         input [255 : 0] expected1
                        );
    reg [31 : 0] start_time;
    reg [31 : 0] end_time;

    begin
      $display("*** TC%01d - continuous command test started.", tc_ctr);

      start_time = cycle_ctr;

      // First block
      write_block(block0);

      write_single_word(ADDR_CTRL, {mode, CTRL_INIT_VALUE});
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);

      for (int i=0; i<10; i++)
        begin
          write_single_word(ADDR_CTRL, {29'h0, mode, CTRL_INIT_VALUE});
          #CLK_PERIOD;
          write_single_word(ADDR_CTRL, {29'h0, mode, CTRL_NEXT_VALUE});
          #CLK_PERIOD;
        end

      wait_ready();
      
      // Final block
      write_block(block1);

      write_single_word(ADDR_CTRL, {mode, CTRL_NEXT_VALUE});
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);

      for (int i=0; i<10; i++)
        begin
          write_single_word(ADDR_CTRL, {29'h0, mode, CTRL_INIT_VALUE});
          #CLK_PERIOD;
          write_single_word(ADDR_CTRL, {29'h0, mode, CTRL_NEXT_VALUE});
          #CLK_PERIOD;
        end

      wait_ready();

      read_digest();

      end_time = cycle_ctr - start_time;
      $display("*** processing time = %01d cycles", end_time);
      if (digest_data == expected1)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected1);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - Continuous command test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // continuous_cmd_test


  //----------------------------------------------------------------
  // zeroize_test()
  //
  //----------------------------------------------------------------
  task zeroize_test(input           mode,
                    input [511 : 0] block0,
                    input [255 : 0] expected0,
                    input [511 : 0] block1,
                    input [255 : 0] expected1
                  );
    begin

      $display("*** TC%01d - zeroize test started.", tc_ctr);

      // First test: assert zeroize when engine is working 
      write_block(block0);

      write_single_word(ADDR_CTRL, {28'h0, 1'b0, mode, CTRL_INIT_VALUE});
      #(10 * CLK_PERIOD);

      write_single_word(ADDR_CTRL, {28'h0, 1'b1, 3'b0}); //zeroize
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      wait_ready();
      read_digest();
      if (digest_data == 0)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, 0);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end
      tc_ctr = tc_ctr + 1;

      // Second test: assert zeroize with INIT
      write_block(block0);

      write_single_word(ADDR_CTRL, {28'h0, 1'b1, mode, CTRL_INIT_VALUE}); //zeroize
      #CLK_PERIOD;
      hsel_i_tb       = 0;
      #(CLK_PERIOD);

      wait_ready();
      read_digest();
      if (digest_data == 0)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, 0);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end
      tc_ctr = tc_ctr + 1;

      // Third test: assert zeroize with NEXT      
      write_block(block0);

      write_single_word(ADDR_CTRL, {28'h0, 1'b1, mode, CTRL_NEXT_VALUE}); //zeroize
      #CLK_PERIOD;
      hsel_i_tb       = 0;
      #(CLK_PERIOD);

      wait_ready();
      read_digest();
      if (digest_data == 0)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, 0);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end
      tc_ctr = tc_ctr + 1;

      // Forth test: assert zeroize after NEXT      
      write_block(block0);

      write_single_word(ADDR_CTRL, {mode, CTRL_NEXT_VALUE});
      #(10 * CLK_PERIOD);

      write_single_word(ADDR_CTRL, {28'h0, 1'b1, 3'b0}); //zeroize
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      wait_ready();
      read_digest();
      if (digest_data == 0)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, 0);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - zeroize test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // zeroize_test

  //----------------------------------------------------------------
  // sha224_tests()
  //
  // Run test cases for sha224.
  // Test cases taken from:
  // http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA224.pdf
  //----------------------------------------------------------------
  task sha224_tests;
    begin : sha224_tests_block
      reg [511 : 0] tc0;
      reg [255 : 0] res0;

      reg [511 : 0] tc1_0;
      reg [255 : 0] res1_0;
      reg [511 : 0] tc1_1;
      reg [255 : 0] res1_1;

      $display("*** Testcases for sha224 functionality started.");

      tc0 = 512'h61626380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018;

      res0 = 256'h23097D223405D8228642A477BDA255B32AADBCE4BDA0B3F7E36C9DA700000000;
      single_block_test(SHA224_MODE, tc0, res0);

      tc1_0 = 512'h6162636462636465636465666465666765666768666768696768696A68696A6B696A6B6C6A6B6C6D6B6C6D6E6C6D6E6F6D6E6F706E6F70718000000000000000;
      res1_0 = 256'h8250e65dbcf62f8466659c3333e5e91a10c8b7b0953927691f1419c200000000;
      tc1_1 = 512'h000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001C0;
      res1_1 = 256'h75388b16512776cc5dba5da1fd890150b0c6455cb4f58b195252252500000000;
      double_block_test(SHA224_MODE, tc1_0, res1_0, tc1_1, res1_1);

      $display("*** Testcases for sha224 functionality completed.");
    end
  endtask // sha224_tests


  //----------------------------------------------------------------
  // sha256_tests()
  //
  // Run test cases for sha256.
  // Test cases taken from:
  // http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA256.pdf
  //----------------------------------------------------------------
  task sha256_tests;
    begin : sha256_tests_block
      reg [511 : 0] tc0;
      reg [255 : 0] res0;

      reg [511 : 0] tc1_0;
      reg [255 : 0] res1_0;
      reg [511 : 0] tc1_1;
      reg [255 : 0] res1_1;

      $display("*** Testcases for sha256 functionality started.");

      tc0 = 512'h61626380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018;
      res0 = 256'hBA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD;
      single_block_test(SHA256_MODE, tc0, res0);

      tc1_0 = 512'h6162636462636465636465666465666765666768666768696768696A68696A6B696A6B6C6A6B6C6D6B6C6D6E6C6D6E6F6D6E6F706E6F70718000000000000000;
      res1_0 = 256'h85E655D6417A17953363376A624CDE5C76E09589CAC5F811CC4B32C1F20E533A;
      tc1_1 = 512'h000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001C0;
      res1_1 = 256'h248D6A61D20638B8E5C026930C3E6039A33CE45964FF2167F6ECEDD419DB06C1;
      double_block_test(SHA256_MODE, tc1_0, res1_0, tc1_1, res1_1);

      continuous_cmd_test(SHA256_MODE, tc1_0, res1_0, tc1_1, res1_1);

      zeroize_test(SHA256_MODE, tc1_0, res1_0, tc1_1, res1_1);

      $display("*** Testcases for sha256 functionality completed.");
    end
  endtask // sha256_tests



  //----------------------------------------------------------------
  // issue_test()
  //----------------------------------------------------------------
  task issue_test;
    reg           mode;
    reg [511 : 0] block0;
    reg [511 : 0] block1;
    reg [511 : 0] block2;
    reg [511 : 0] block3;
    reg [511 : 0] block4;
    reg [511 : 0] block5;
    reg [511 : 0] block6;
    reg [511 : 0] block7;
    reg [511 : 0] block8;
    reg [255 : 0] expected;
    begin : issue_test;
      mode = SHA256_MODE;

      block0 = 512'h6b900001_496e2074_68652061_72656120_6f662049_6f542028_496e7465_726e6574_206f6620_5468696e_6773292c_206d6f72_6520616e_64206d6f_7265626f_6f6d2c20;
      block1 = 512'h69742068_61732062_65656e20_6120756e_69766572_73616c20_636f6e73_656e7375_73207468_61742064_61746120_69732074_69732061_206e6577_20746563_686e6f6c;
      block2 = 512'h6f677920_74686174_20696e74_65677261_74657320_64656365_6e747261_6c697a61_74696f6e_2c496e20_74686520_61726561_206f6620_496f5420_28496e74_65726e65;
      block3 = 512'h74206f66_20546869_6e677329_2c206d6f_72652061_6e64206d_6f726562_6f6f6d2c_20697420_68617320_6265656e_20612075_6e697665_7273616c_20636f6e_73656e73;
      block4 = 512'h75732074_68617420_64617461_20697320_74697320_61206e65_77207465_63686e6f_6c6f6779_20746861_7420696e_74656772_61746573_20646563_656e7472_616c697a;
      block5 = 512'h6174696f_6e2c496e_20746865_20617265_61206f66_20496f54_2028496e_7465726e_6574206f_66205468_696e6773_292c206d_6f726520_616e6420_6d6f7265_626f6f6d;
      block6 = 512'h2c206974_20686173_20626565_6e206120_756e6976_65727361_6c20636f_6e73656e_73757320_74686174_20646174_61206973_20746973_2061206e_65772074_6563686e;
      block7 = 512'h6f6c6f67_79207468_61742069_6e746567_72617465_73206465_63656e74_72616c69_7a617469_6f6e2c49_6e207468_65206172_6561206f_6620496f_54202849_6e746572;
      block8 = 512'h6e657420_6f662054_68696e67_73292c20_6d6f7265_20616e64_206d6f72_65800000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_000010e8;

      expected = 256'h7758a30bbdfc9cd92b284b05e9be9ca3d269d3d149e7e82ab4a9ed5e81fbcf9d;

      $display("Running test for 9 block issue.");
      tc_ctr = tc_ctr + 1;
      write_block(block0);
      write_single_word(ADDR_CTRL, {mode, CTRL_INIT_VALUE});
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();

      write_block(block1);
      write_single_word(ADDR_CTRL, {mode, CTRL_NEXT_VALUE});
      #CLK_PERIOD;
      hsel_i_tb       = 0;      
      #(CLK_PERIOD);
      wait_ready();

      write_block(block2);
      write_single_word(ADDR_CTRL, {mode, CTRL_NEXT_VALUE});
      #CLK_PERIOD;
      hsel_i_tb       = 0;      
      #(CLK_PERIOD);
      wait_ready();

      write_block(block3);
      write_single_word(ADDR_CTRL, {mode, CTRL_NEXT_VALUE});
      #CLK_PERIOD;
      hsel_i_tb       = 0;      
      #(CLK_PERIOD);
      wait_ready();

      write_block(block4);
      write_single_word(ADDR_CTRL, {mode, CTRL_NEXT_VALUE});
      #CLK_PERIOD;
      hsel_i_tb       = 0;      
      #(CLK_PERIOD);
      wait_ready();

      write_block(block5);
      write_single_word(ADDR_CTRL, {mode, CTRL_NEXT_VALUE});
      #CLK_PERIOD;
      hsel_i_tb       = 0;      
      #(CLK_PERIOD);
      wait_ready();

      write_block(block6);
      write_single_word(ADDR_CTRL, {mode, CTRL_NEXT_VALUE});
      #CLK_PERIOD;
      hsel_i_tb       = 0;      
      #(CLK_PERIOD);
      wait_ready();

      write_block(block7);
      write_single_word(ADDR_CTRL, {mode, CTRL_NEXT_VALUE});
      #CLK_PERIOD;
      hsel_i_tb       = 0;      
      #(CLK_PERIOD);
      wait_ready();

      write_block(block8);
      write_single_word(ADDR_CTRL, {mode, CTRL_NEXT_VALUE});
      #CLK_PERIOD;
      hsel_i_tb       = 0;      
      #(CLK_PERIOD);
      wait_ready();

      read_digest();
      if (digest_data == expected)
        begin
          $display("Digest ok.");
        end
      else
        begin
          $display("ERROR in digest");
          $display("Expected: 0x%064x", expected);
          $display("Got:      0x%064x", digest_data);
          error_ctr = error_ctr + 1;
        end
    end
  endtask // issue_test


  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -- Testbench for sha256 started --");

      init_sim();
      reset_dut();

      check_name_version();
      sha224_tests();
      sha256_tests();
      issue_test();

      display_test_result();

      $display("   -- Testbench for sha256 done. --");
      $finish;
    end // main
endmodule // sha256_ctrl_tb

//======================================================================
// EOF sha256_ctrl_tb.sv
//======================================================================
