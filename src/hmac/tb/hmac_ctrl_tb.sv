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
// hmac_ctrl_tb.sv
// --------
// HMAC testbench for the hmac AHb_lite interface controller.
//
//
// 
//======================================================================

`include "caliptra_reg_defines.svh"
`include "caliptra_reg_field_defines.svh"

module hmac_ctrl_tb();

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG = 0;

  parameter CLK_HALF_PERIOD = 2;
  parameter CLK_PERIOD = 2 * CLK_HALF_PERIOD;

  parameter CTRL_INIT_VALUE  = `HMAC_REG_HMAC512_CTRL_INIT_MASK;
  parameter CTRL_NEXT_VALUE  = `HMAC_REG_HMAC512_CTRL_NEXT_MASK;
  
  parameter HMAC512_MODE     = (1'b1 << `HMAC_REG_HMAC512_CTRL_MODE_LOW) & `HMAC_REG_HMAC512_CTRL_MODE_MASK;
  parameter HMAC384_MODE     = (1'b0 << `HMAC_REG_HMAC512_CTRL_MODE_LOW) & `HMAC_REG_HMAC512_CTRL_MODE_MASK;

  parameter CTRL_ZEROIZE  = `HMAC_REG_HMAC512_CTRL_ZEROIZE_MASK;

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  parameter AHB_ADDR_WIDTH = 32;
  parameter AHB_DATA_WIDTH = 32;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0] cycle_ctr;
  reg [63 : 0] error_ctr;
  reg [63 : 0] tc_ctr;

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

  reg [63 : 0]  read_data;
  reg [511 : 0] digest_data;

  //bind coverage file
  hmac_ctrl_cov_bind i_hmac_ctrl_cov_bind();

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  hmac_ctrl #(
             .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH)
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

             .kv_read(),
             .kv_write(),
             .kv_rd_resp('x),
             .kv_wr_resp('x),
             .busy_o(),
             .error_intr(),
             .notif_intr(),
             .debugUnlock_or_scan_mode_switch('0)
            );


  //----------------------------------------------------------------
  // clk_gen
  //
  // Clock generator process.
  //----------------------------------------------------------------
  always
    begin : clk_gen
      #CLK_HALF_PERIOD clk_tb = !clk_tb;
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
  // Randomize function
  //
  // 
  //----------------------------------------------------------------
  function logic [383 : 0] random_gen();
    return { $random, $random, $random, $random, $random, $random,
             $random, $random, $random, $random, $random, $random};
  endfunction

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
          read_single_word(`HMAC_REG_HMAC512_STATUS);
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
  task write_block(input [1023 : 0] block);
    begin
      write_single_word(`HMAC_REG_HMAC512_BLOCK_0, block[1023: 992]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_1,  block[991: 960]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_2,  block[959: 928]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_3,  block[927: 896]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_4,  block[895: 864]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_5,  block[863: 832]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_6,  block[831: 800]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_7,  block[799: 768]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_8,  block[767: 736]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_9,  block[735: 704]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_10, block[703: 672]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_11, block[671: 640]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_12, block[639: 608]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_13, block[607: 576]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_14, block[575: 544]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_15, block[543: 512]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_16, block[511: 480]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_17, block[479: 448]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_18, block[447: 416]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_19, block[415: 384]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_20, block[383: 352]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_21, block[351: 320]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_22, block[319: 288]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_23, block[287: 256]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_24, block[255: 224]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_25, block[223: 192]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_26, block[191: 160]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_27, block[159: 128]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_28, block[127: 96 ]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_29, block[95 : 64 ]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_30, block[63 : 32 ]);
      write_single_word(`HMAC_REG_HMAC512_BLOCK_31, block[31 : 0  ]);
      
    end
  endtask // write_block


  //----------------------------------------------------------------
  // hmac_write_key()
  //
  // Write the given key to the dut.
  //----------------------------------------------------------------
  task hmac_write_key(input [511 : 0] key);
    begin
      write_single_word(`HMAC_REG_HMAC512_KEY_0,  key[511: 480]);
      write_single_word(`HMAC_REG_HMAC512_KEY_1,  key[479: 448]);
      write_single_word(`HMAC_REG_HMAC512_KEY_2,  key[447: 416]);
      write_single_word(`HMAC_REG_HMAC512_KEY_3,  key[415: 384]);
      write_single_word(`HMAC_REG_HMAC512_KEY_4,  key[383: 352]);
      write_single_word(`HMAC_REG_HMAC512_KEY_5,  key[351: 320]);
      write_single_word(`HMAC_REG_HMAC512_KEY_6,  key[319: 288]);
      write_single_word(`HMAC_REG_HMAC512_KEY_7,  key[287: 256]);
      write_single_word(`HMAC_REG_HMAC512_KEY_8,  key[255: 224]);
      write_single_word(`HMAC_REG_HMAC512_KEY_9,  key[223: 192]);
      write_single_word(`HMAC_REG_HMAC512_KEY_10, key[191: 160]);
      write_single_word(`HMAC_REG_HMAC512_KEY_11, key[159: 128]);
      write_single_word(`HMAC_REG_HMAC512_KEY_12, key[127: 96 ]);
      write_single_word(`HMAC_REG_HMAC512_KEY_13, key[95 : 64 ]);
      write_single_word(`HMAC_REG_HMAC512_KEY_14, key[63 : 32 ]);
      write_single_word(`HMAC_REG_HMAC512_KEY_15, key[31 : 0  ]);
    end
  endtask // hmac384_write_key

  //----------------------------------------------------------------
  // write_seed()
  //
  // Write the given seed to the dut.
  //----------------------------------------------------------------
  task write_seed(input [383 : 0] seed);
    begin
      write_single_word(`HMAC_REG_HMAC512_LFSR_SEED_0,  seed[383: 352]);
      write_single_word(`HMAC_REG_HMAC512_LFSR_SEED_1,  seed[351: 320]);
      write_single_word(`HMAC_REG_HMAC512_LFSR_SEED_2,  seed[319: 288]);
      write_single_word(`HMAC_REG_HMAC512_LFSR_SEED_3,  seed[287: 256]);
      write_single_word(`HMAC_REG_HMAC512_LFSR_SEED_4,  seed[255: 224]);
      write_single_word(`HMAC_REG_HMAC512_LFSR_SEED_5,  seed[223: 192]);
      write_single_word(`HMAC_REG_HMAC512_LFSR_SEED_6,  seed[191: 160]);
      write_single_word(`HMAC_REG_HMAC512_LFSR_SEED_7,  seed[159: 128]);
      write_single_word(`HMAC_REG_HMAC512_LFSR_SEED_8,  seed[127: 96 ]);
      write_single_word(`HMAC_REG_HMAC512_LFSR_SEED_9,  seed[95 : 64 ]);
      write_single_word(`HMAC_REG_HMAC512_LFSR_SEED_10, seed[63 : 32 ]);
      write_single_word(`HMAC_REG_HMAC512_LFSR_SEED_11, seed[31 : 0  ]);
    end
  endtask // write_seed

  //----------------------------------------------------------------
  // read_single_word()
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
  endtask // read_single_word


  //----------------------------------------------------------------
  // check_name_version()
  //
  // Read the name and version from the DUT.
  //----------------------------------------------------------------
  task check_name_version;
    reg [63 : 0] name;
    reg [63 : 0] version;
    begin

      read_single_word(`HMAC_REG_HMAC512_NAME_0);
      name = read_data;
      read_single_word(`HMAC_REG_HMAC512_VERSION_0);
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
  // hmac_read_digest()
  //
  // Read the digest in the dut. The resulting digest will be
  // available in the global variable digest_data.
  //----------------------------------------------------------------
  task hmac_read_digest;
    begin
      read_single_word(`HMAC_REG_HMAC512_TAG_0);
      digest_data[511 : 480] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_1);
      digest_data[479 : 448] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_2);
      digest_data[447 : 416] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_3);
      digest_data[415 : 384] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_4);
      digest_data[383 : 352] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_5);
      digest_data[351 : 320] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_6);
      digest_data[319 : 288] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_7);
      digest_data[287 : 256] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_8);
      digest_data[255 : 224] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_9);
      digest_data[223 : 192] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_10);
      digest_data[191 : 160] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_11);
      digest_data[159 : 128] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_12);
      digest_data[127 : 96] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_13);
      digest_data[95 : 64] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_14);
      digest_data[63 :  32] = read_data;
      read_single_word(`HMAC_REG_HMAC512_TAG_15);
      digest_data[31  :   0] = read_data;
    end
  endtask // hmac_read_digest

  //----------------------------------------------------------------
  // hmac_single_block_test()
  //
  //
  // Perform test of a single block digest.
  //----------------------------------------------------------------
  task hmac_single_block_test(input [31:0] mode,
                         input [511 : 0] key,
                         input [1023: 0] block,
                         input [383: 0]  seed,
                         input [511 : 0] expected
                        );
    begin
      reg [31  : 0] start_time;
      reg [31 : 0] end_time;

      start_time = cycle_ctr;

      $display("*** TC%01d - Single block test started.", tc_ctr);

      hmac_write_key(key);
      write_block(block);
      write_seed(seed);
      
      write_single_word(`HMAC_REG_HMAC512_CTRL, mode | CTRL_INIT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      hmac_read_digest();

      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);

      write_single_word(`HMAC_REG_HMAC512_CTRL, CTRL_ZEROIZE); //zeroize

      if (digest_data == expected)
        begin
          $display("TC%01d: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR.", tc_ctr);
          $display("TC%01d: Expected: 0x%0128x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%0128x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end
      
      $display("*** TC%01d - Single block test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // hmac_single_block_test


  //----------------------------------------------------------------
  // hmac_double_block_test()
  //
  //
  // Perform test of a double block digest. Note that we check
  // the digests for both the first and final block.
  //----------------------------------------------------------------
  task hmac_double_block_test(input [31:0] mode,
                         input [511 : 0] key,
                         input [1023: 0] block0,
                         input [1023: 0] block1,
                         input [383: 0]  seed,
                         input [511 : 0] expected
                        );
    begin
      reg [31  : 0] start_time;
      reg [31 : 0] end_time;

      start_time = cycle_ctr;
      $display("*** TC%01d - Double block test started.", tc_ctr);

      hmac_write_key(key);

      // First block
      write_block(block0);

      write_seed(seed);

      write_single_word(`HMAC_REG_HMAC512_CTRL, mode | CTRL_INIT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();

      // Final block
      write_block(block1);

      write_single_word(`HMAC_REG_HMAC512_CTRL, mode | CTRL_NEXT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      hmac_read_digest();

      write_single_word(`HMAC_REG_HMAC512_CTRL, CTRL_ZEROIZE); //zeroize

      end_time = cycle_ctr - start_time;
      $display("*** Double block test processing time = %01d cycles", end_time);

      if (digest_data == expected)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%0128x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%0128x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - Double block test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // hmac_double_block_test


  //----------------------------------------------------------------
  // continuous_cmd_test()
  //
  //
  // Perform test of a double block digest.
  //----------------------------------------------------------------
  task continuous_cmd_test(input [31:0] mode,
                         input [511 : 0] key,
                         input [1023: 0] block0,
                         input [1023: 0] block1,
                         input [383: 0]  seed,
                         input [511 : 0] expected
                        );
    begin
      reg [31  : 0] start_time;
      reg [31 : 0] end_time;

      start_time = cycle_ctr;
      $display("*** TC%01d - continuous_cmd_test started.", tc_ctr);

      hmac_write_key(key);

      // First block
      write_block(block0);

      write_seed(seed);

      write_single_word(`HMAC_REG_HMAC512_CTRL, mode | CTRL_INIT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);

      for (int i=0; i<10; i++)
        begin
          write_single_word(`HMAC_REG_HMAC512_CTRL, mode | CTRL_INIT_VALUE);
          #CLK_PERIOD;
          write_single_word(`HMAC_REG_HMAC512_CTRL, mode | CTRL_NEXT_VALUE);
          #CLK_PERIOD;
        end

      #(CLK_PERIOD);
      wait_ready();

      // Final block
      write_block(block1);

      write_single_word(`HMAC_REG_HMAC512_CTRL, mode | CTRL_NEXT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);

      for (int i=0; i<10; i++)
        begin
          write_single_word(`HMAC_REG_HMAC512_CTRL, mode | CTRL_INIT_VALUE);
          #CLK_PERIOD;
          write_single_word(`HMAC_REG_HMAC512_CTRL, mode | CTRL_NEXT_VALUE);
          #CLK_PERIOD;
        end

      #(CLK_PERIOD);
      wait_ready();
      hmac_read_digest();

      write_single_word(`HMAC_REG_HMAC512_CTRL, CTRL_ZEROIZE); //zeroize

      end_time = cycle_ctr - start_time;
      $display("*** continuous_cmd_test processing time = %01d cycles", end_time);

      if (digest_data == expected)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%0128x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%0128x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - continuous_cmd_test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // continuous_cmd_test

  //----------------------------------------------------------------
  // zeroize_test()
  //
  //----------------------------------------------------------------
  task zeroize_test(input [31:0] mode,
                    input [511 : 0] key,
                    input [1023: 0] block0,
                    input [1023: 0] block1,
                    input [383: 0]  seed,
                    input [511 : 0] expected
                  );
    begin

      $display("*** TC%01d - zeroize test started.", tc_ctr);

      // First test: assert zeroize when engine is working
      hmac_write_key(key);
      
      write_block(block0);

      write_seed(seed);

      write_single_word(`HMAC_REG_HMAC512_CTRL, mode | CTRL_INIT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      for (int i=0; i<10; i++)
        begin
          #(CLK_PERIOD);
        end

      write_single_word(`HMAC_REG_HMAC512_CTRL, CTRL_ZEROIZE); //zeroize

      wait_ready();
      hmac_read_digest();
      if (digest_data == 0)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%0128x", tc_ctr, 0);
          $display("TC%01d: Got:      0x%0128x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end
      tc_ctr = tc_ctr + 1;

      // Second test: assert zeroize with INIT
      hmac_write_key(key);
      
      write_block(block0);

      write_seed(seed);

      write_single_word(`HMAC_REG_HMAC512_CTRL, CTRL_ZEROIZE | mode | CTRL_INIT_VALUE); //zeroize
      #CLK_PERIOD;
      hsel_i_tb       = 0;
      #(CLK_PERIOD);

      wait_ready();
      hmac_read_digest();
      if (digest_data == 0)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%0128x", tc_ctr, 0);
          $display("TC%01d: Got:      0x%0128x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end
      tc_ctr = tc_ctr + 1;

      // Third test: assert zeroize with NEXT
      hmac_write_key(key);
      
      write_block(block0);

      write_seed(seed);

      write_single_word(`HMAC_REG_HMAC512_CTRL, CTRL_ZEROIZE | mode | CTRL_NEXT_VALUE); //zeroize
      #CLK_PERIOD;
      hsel_i_tb       = 0;
      #(CLK_PERIOD);

      wait_ready();
      hmac_read_digest();
      if (digest_data == 0)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%0128x", tc_ctr, 0);
          $display("TC%01d: Got:      0x%0128x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end
      tc_ctr = tc_ctr + 1;

      // Forth test: assert zeroize after NEXT
      hmac_write_key(key);
      
      write_block(block0);

      write_seed(seed);

      write_single_word(`HMAC_REG_HMAC512_CTRL, mode | CTRL_NEXT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      for (int i=0; i<10; i++)
        begin
          #(CLK_PERIOD);
        end

      write_single_word(`HMAC_REG_HMAC512_CTRL, CTRL_ZEROIZE); //zeroize

      wait_ready();
      hmac_read_digest();
      if (digest_data == 0)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%0128x", tc_ctr, 0);
          $display("TC%01d: Got:      0x%0128x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - zeroize test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // zeroize_test

  //----------------------------------------------------------------
  // hmac384_tests()
  //
  // Run test cases for hmac.
  // Test cases taken from:
  // https://datatracker.ietf.org/doc/html/rfc4868#section-2.7 
  //----------------------------------------------------------------
  task hmac384_tests;
    begin : hmac384_tests_block
      reg [383 : 0] key0;
      reg [1023: 0] data0;
      reg [383 : 0] seed0;
      reg [383 : 0] expected0;

      reg [383 : 0] key1;
      reg [1023: 0] data1;
      reg [383 : 0] seed1;
      reg [383 : 0] expected1;

      reg [383 : 0] key2;
      reg [1023: 0] data2;
      reg [383 : 0] seed2;
      reg [383 : 0] expected2;

      reg [383 : 0] key3;
      reg [1023: 0] data3;
      reg [383 : 0] seed3;
      reg [383 : 0] expected3;

      reg [383 : 0] key4;
      reg [1023: 0] data40;
      reg [1023: 0] data41;
      reg [383 : 0] seed4;
      reg [383 : 0] expected4;

      

      $display("\n\n*** Testcases for PRF-HMAC-SHA-384 functionality started.");

      key0 = 384'h0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b;
      data0 = 1024'h4869205468657265800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000440;
      expected0 = 384'hb6a8d5636f5c6a7224f9977dcf7ee6c7fb6d0c48cbdee9737a959796489bddbc4c5df61d5b3297b4fb68dab9f1b582c2;
      seed0 = random_gen();

      key1      = 384'h4a6566654a6566654a6566654a6566654a6566654a6566654a6566654a6566654a6566654a6566654a6566654a656665  ;
      data1 = 1024'h7768617420646f2079612077616e7420666f72206e6f7468696e673f800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004e0;
      expected1 = 384'h2c7353974f1842fd66d53c452ca42122b28c0b594cfb184da86a368e9b8e16f5349524ca4e82400cbde0686d403371c9;
      seed1 = random_gen();

      key2      = 384'haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;
      data2 = 1024'hdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000590;
      expected2 = 384'h809f439be00274321d4a538652164b53554a508184a0c3160353e3428597003d35914a18770f9443987054944b7c4b4a;
      seed2 = random_gen();

      key3      = 384'h0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f200a0b0c0d0e0f10111213141516171819;
      data3     = 1024'hcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000590;
      expected3 = 384'h5b540085c6e6358096532b2493609ed1cb298f774f87bb5c2ebf182c83cc7428707fb92eab2536a5812258228bc96687;
      seed3 = random_gen();
            
      hmac_single_block_test(HMAC384_MODE, {key0, 128'b0}, data0, seed0, {expected0, 128'b0});

      hmac_single_block_test(HMAC384_MODE, {key1, 128'b0}, data1, seed1, {expected1, 128'b0});

      hmac_single_block_test(HMAC384_MODE, {key2, 128'b0}, data2, seed2, {expected2, 128'b0});

      hmac_single_block_test(HMAC384_MODE, {key3, 128'b0}, data3, seed3, {expected3, 128'b0});

      key4   = 384'h1e6a3e8998be7c36c5a511c4f03fcfba543d678f1000e2f6a61c2a95f79bb006fc782a679a0b890e3374b20df710f6c2;
      data40 = 1024'hdbf031b43f84bcf3cc9339e65c3659151d3061dd2d5fb0b2d37fbe4fca4ea373b567ae3513ea095013efc7b19f6851ad73c26176034964999c2c3cf2fd58561a9f791839a2199f2a9405edd0478ac64a9557aec86940d465d90364489e4d32f168ce2eefec74eb7e653f8da640308f72f0bd7b1a698c683870c7439869b969ae;
      data41 = 1024'hbea9f4f6bacdc04d4ec4f6bcc17874940336c7899553800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008b0;
      expected4 = 384'h8aba65c07793e1d8a709fbda35ae71804dc0741166dda5746fb3b1c0e91957bbd0d539a469c2ea3577b75d5c0f150ce7;
      seed4 = random_gen();

      hmac_double_block_test(HMAC384_MODE, {key4, 128'b0}, data40, data41, seed4, {expected4, 128'b0});

      continuous_cmd_test(HMAC384_MODE, {key4, 128'b0}, data40, data41, seed4, {expected4, 128'b0});

      zeroize_test(HMAC384_MODE, {key4, 128'b0}, data40, data41, seed4, {expected4, 128'b0});
      
      $display("*** Testcases for PRF-HMAC-SHA-384 functionality completed.");
    end
  endtask // hmac384_tests

  //----------------------------------------------------------------
  // hmac512_tests()
  //
  // Run test cases for hmac.
  // Test cases taken from:
  // https://datatracker.ietf.org/doc/html/rfc4868#section-2.7 
  //----------------------------------------------------------------
  task hmac512_tests;
    begin : hmac512_tests_block
      reg [511 : 0] key0;
      reg [1023: 0] data0;
      reg [383 : 0] seed0;
      reg [511 : 0] expected0;

      reg [511 : 0] key1;
      reg [1023: 0] data1;
      reg [383 : 0] seed1;
      reg [511 : 0] expected1;

      reg [511 : 0] key2;
      reg [1023: 0] data2;
      reg [383 : 0] seed2;
      reg [511 : 0] expected2;

      reg [511 : 0] key3;
      reg [1023: 0] data3;
      reg [383 : 0] seed3;
      reg [511 : 0] expected3;

      reg [511 : 0] key4;
      reg [1023: 0] data40;
      reg [1023: 0] data41;
      reg [383 : 0] seed4;
      reg [511 : 0] expected4;

      

      $display("\n\n*** Testcases for PRF-HMAC-SHA-512 functionality started.");
                      
      key0 =  {4{128'h0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b}};
      data0 = 1024'h4869205468657265800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000440;
      expected0 = 512'h637edc6e01dce7e6742a99451aae82df23da3e92439e590e43e761b33e910fb8ac2878ebd5803f6f0b61dbce5e251ff8789a4722c1be65aea45fd464e89f8f5b;
      seed0 = random_gen();

      key1      = {4{128'h4a6566654a6566654a6566654a656665}};
      data1 = 1024'h7768617420646f2079612077616e7420666f72206e6f7468696e673f800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004e0;
      expected1 = 512'hcb370917ae8a7ce28cfd1d8f4705d6141c173b2a9362c15df235dfb251b154546aa334ae9fb9afc2184932d8695e397bfa0ffb93466cfcceaae38c833b7dba38;
      seed1 = random_gen();

      key2      = {4{128'haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa}};
      data2 = 1024'hdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000590;
      expected2 = 512'h2ee7acd783624ca9398710f3ee05ae41b9f9b0510c87e49e586cc9bf961733d8623c7b55cebefccf02d5581acc1c9d5fb1ff68a1de45509fbe4da9a433922655;
      seed2 = random_gen();

      key3      = 512'h0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40;
      data3     = 1024'hcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000590;
      expected3 = 512'h5e6688e5a3daec826ca32eaea224eff5e700628947470e13ad01302561bab108b8c48cbc6b807dcfbd850521a685babc7eae4a2a2e660dc0e86b931d65503fd2;
      seed3 = random_gen();
            
      hmac_single_block_test(HMAC512_MODE, key0, data0, seed0, expected0);

      hmac_single_block_test(HMAC512_MODE, key1, data1, seed1, expected1);

      hmac_single_block_test(HMAC512_MODE, key2, data2, seed2, expected2);

      hmac_single_block_test(HMAC512_MODE, key3, data3, seed3, expected3);

      //Key4=sha512('haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)
      key4   = 512'he1b52c4ff8ce9c4b60bd8ec785ab7bf3dffc7023f7c51588f96b94eeba80ca3b9b9ed05ab2ac8797bb7039d681f2e41fcfe6dddab2e95122d9c716c2b8406bd4;
      data40 = 1024'h5468697320697320612074657374207573696e672061206c6172676572207468616e20626c6f636b2d73697a65206b657920616e642061206c6172676572207468616e20626c6f636b2d73697a6520646174612e20546865206b6579206e6565647320746f20626520686173686564206265666f7265206265696e6720757365;
      data41 = 1024'h642062792074686520484d414320616c676f726974686d2e80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008C0;
      expected4 = 512'he37b6a775dc87dbaa4dfa9f96e5e3ffddebd71f8867289865df5a32d20cdc944b6022cac3c4982b10d5eeb55c3e4de15134676fb6de0446065c97440fa8c6a58;
      seed4 = random_gen();

      hmac_double_block_test(HMAC512_MODE, key4, data40, data41, seed4, expected4);

      continuous_cmd_test(HMAC512_MODE, key4, data40, data41, seed4, expected4);

      zeroize_test(HMAC512_MODE, key4, data40, data41, seed4, expected4);
      
      $display("*** Testcases for PRF-HMAC-SHA-512 functionality completed.");
    end
  endtask // hmac_tests

  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -- Testbench for HMAC started --");

      init_sim();
      reset_dut();

      check_name_version();
      hmac384_tests();
      hmac512_tests();

      display_test_result();

      $display("   -- Testbench for HMAC done. --");
      $finish;
    end // main
endmodule // hmac_ctrl_tb

//======================================================================
// EOF hmac_ctrl_tb.sv
//======================================================================
