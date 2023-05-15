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

`default_nettype none
`include "caliptra_reg_defines.svh"

module sha256_random_test();

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG = 0;

  parameter CLK_HALF_PERIOD = 2;
  parameter CLK_PERIOD = 2 * CLK_HALF_PERIOD;

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
  reg [255 : 0] expected;

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
             .cptra_pwrgood(reset_n_tb),

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
             .notif_intr()
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
      reset_n_tb = 0;

      #(2 * CLK_PERIOD);

      @(posedge clk_tb);
      reset_n_tb = 1;

      #(2 * CLK_PERIOD);

      @(posedge clk_tb);
      $display("");
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
      read_single_word(`SHA256_REG_SHA256_STATUS);
      while (hrdata_o_tb == 0)
        begin
          read_single_word(`SHA256_REG_SHA256_STATUS);
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
      hsel_i_tb       <= 1;
      haddr_i_tb      <= address;
      hwrite_i_tb     <= 1;
      hready_i_tb     <= 1;
      htrans_i_tb     <= AHB_HTRANS_NONSEQ;
      hsize_i_tb      <= 3'b010;
      
      @(posedge clk_tb);
      haddr_i_tb      <= 'Z;
      hwdata_i_tb     <= word;
      hwrite_i_tb     <= 0;
      htrans_i_tb     <= AHB_HTRANS_IDLE;
      wait(hreadyout_o_tb == 1'b1);

      @(posedge clk_tb);
      hsel_i_tb       <= 0;
    end
  endtask // write_single_word



  //----------------------------------------------------------------
  // write_block()
  //
  // Write the given block to the dut.
  //----------------------------------------------------------------
  task write_block(input [511 : 0] block);
    begin
      write_single_word(`SHA256_REG_SHA256_BLOCK_0 , block[511  : 480]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_1 , block[479  : 448]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_2 , block[447  : 416]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_3 , block[415  : 384]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_4 , block[383  : 352]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_5 , block[351  : 320]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_6 , block[319  : 288]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_7 , block[287  : 256]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_8 , block[255  : 224]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_9 , block[223  : 192]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_10, block[191  : 160]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_11, block[159  : 128]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_12, block[127  :  96]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_13, block[95   :  64]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_14, block[63   :  32]);
      write_single_word(`SHA256_REG_SHA256_BLOCK_15, block[31   :   0]);
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
      hsel_i_tb       <= 1;
      haddr_i_tb      <= address;
      hwrite_i_tb     <= 0;
      hready_i_tb     <= 1;
      htrans_i_tb     <= AHB_HTRANS_NONSEQ;
      hsize_i_tb      <= 3'b010;
      
      @(posedge clk_tb);
      hwdata_i_tb     <= 0;
      haddr_i_tb      <= 'Z;
      htrans_i_tb     <= AHB_HTRANS_IDLE;
      wait(hreadyout_o_tb == 1'b1);

      @(posedge clk_tb);
      hsel_i_tb       <= 0;      
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

      read_single_word(`SHA256_REG_SHA256_NAME_0);
      name0 = hrdata_o_tb;
      read_single_word(`SHA256_REG_SHA256_NAME_1);
      name1 = hrdata_o_tb;
      read_single_word(`SHA256_REG_SHA256_VERSION_0);
      version0 = hrdata_o_tb;
      read_single_word(`SHA256_REG_SHA256_VERSION_1);
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
      read_single_word(`SHA256_REG_SHA256_DIGEST_0);
      digest_data[255 : 224] = hrdata_o_tb;
      read_single_word(`SHA256_REG_SHA256_DIGEST_1);
      digest_data[223 : 192] = hrdata_o_tb;
      read_single_word(`SHA256_REG_SHA256_DIGEST_2);
      digest_data[191 : 160] = hrdata_o_tb;
      read_single_word(`SHA256_REG_SHA256_DIGEST_3);
      digest_data[159 : 128] = hrdata_o_tb;
      read_single_word(`SHA256_REG_SHA256_DIGEST_4);
      digest_data[127 :  96] = hrdata_o_tb;
      read_single_word(`SHA256_REG_SHA256_DIGEST_5);
      digest_data[95  :  64] = hrdata_o_tb;
      read_single_word(`SHA256_REG_SHA256_DIGEST_6);
      digest_data[63  :  32] = hrdata_o_tb;
      read_single_word(`SHA256_REG_SHA256_DIGEST_7);
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
      $display("Block: 0x%0128x", block);

      write_block(block);

      if (mode)
        write_single_word(`SHA256_REG_SHA256_CTRL, (`SHA256_REG_SHA256_CTRL_MODE_MASK + `SHA256_REG_SHA256_CTRL_INIT_MASK));
      else
        write_single_word(`SHA256_REG_SHA256_CTRL, `SHA256_REG_SHA256_CTRL_INIT_MASK);

      start_time = cycle_ctr;
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);
      read_digest();

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
  // sha256_predictor()
  //
  // 
  //----------------------------------------------------------------

  task sha256_predictor([415 : 0] block);
        string file_name;
        string file_name_bak;
        string line_read;
        string tmp_str1;
        string tmp_str2;
        int fd_w, fd_all_a;
        int    fd_r;
        
        reg [255:0] tmp;
    begin
        //Write block to file
        file_name = "sha256_test_vector.txt";
        file_name_bak = "sha256_test_vectors_all.txt"; 
        fd_w = $fopen(file_name, "w");
        fd_all_a = $fopen(file_name_bak, "a");
        if(!fd_w) $display("**SHA256** Cannot open file %s", file_name);
        if(!fd_all_a) $display("**SHA256** Cannot open file %s", file_name_bak);
        $fdisplay(fd_w, "BLOCK = %h", block);
        $fdisplay(fd_all_a, "BLOCK = %h", block);
        $fdisplay(fd_all_a, "=======================================");

        $fclose(fd_w);
        $fclose(fd_all_a);

        //Read digest from file
        $system("python ./sha256_test_gen.py");
        file_name = "expected_digest.txt";

        fd_r = $fopen(file_name, "r");
        if(!fd_r) $display("**SHA256_predictor** Cannot open file %s", file_name);

        //Get digest:
        void'($fgets(line_read, fd_r));
        void'($sscanf(line_read, "%s %s %h", tmp_str1, tmp_str2, tmp));

        while (tmp_str1 != "DIGEST") begin
            void'($fgets(line_read, fd_r));
            void'($sscanf(line_read, "%s %s %h", tmp_str1, tmp_str2, tmp));
        end

        expected = tmp;
        $fclose(fd_r);
    end
  endtask


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

      $display("*** Testcases for sha256 functionality started.");

      //for (int i = 0; i < 10; i++) begin: test_vector_loop
        tc0 = {$urandom(), $urandom(), $urandom(), $urandom(), $urandom(), $urandom(), $urandom(), $urandom(),
               $urandom(), $urandom(), $urandom(), $urandom(), $urandom(), 32'h80000000, 64'h00000000_000001A0};
        
        sha256_predictor(tc0[511 : 96]);
        res0 = expected;
        single_block_test(SHA256_MODE, tc0, res0);
      //end

      $display("*** Testcases for sha256 functionality completed.");
    end
  endtask // sha256_tests




  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -- Testbench for randomized sha256 started --");

      init_sim();
      reset_dut();

      sha256_tests();

      display_test_result();

      $display("   -- Testbench for randomized sha256 done. --");
      $finish;
    end // main
endmodule // sha256_ctrl_tb

//======================================================================
// EOF sha256_randomized_tb.sv
//======================================================================
