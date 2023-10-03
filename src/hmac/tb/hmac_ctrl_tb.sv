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

module hmac_ctrl_tb();

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG = 0;

  parameter CLK_HALF_PERIOD = 2;
  parameter CLK_PERIOD = 2 * CLK_HALF_PERIOD;

  // The address map.
  parameter BASE_ADDR        = 32'h10010000;

  parameter ADDR_NAME        = BASE_ADDR + 32'h00000000;
  parameter ADDR_VERSION     = BASE_ADDR + 32'h00000008;

  parameter ADDR_CTRL        = BASE_ADDR + 32'h00000010;
  parameter CTRL_INIT_VALUE  = 2'h1;
  parameter CTRL_NEXT_VALUE  = 2'h2;

  parameter ADDR_STATUS      = BASE_ADDR + 32'h00000018;
  parameter STATUS_READY_BIT = 0;
  parameter STATUS_VALID_BIT = 1;

  parameter ADDR_KEY0        = BASE_ADDR + 32'h00000040;
  parameter ADDR_KEY1        = BASE_ADDR + 32'h00000044;
  parameter ADDR_KEY2        = BASE_ADDR + 32'h00000048;
  parameter ADDR_KEY3        = BASE_ADDR + 32'h0000004C;
  parameter ADDR_KEY4        = BASE_ADDR + 32'h00000050;
  parameter ADDR_KEY5        = BASE_ADDR + 32'h00000054;
  parameter ADDR_KEY6        = BASE_ADDR + 32'h00000058;
  parameter ADDR_KEY7        = BASE_ADDR + 32'h0000005C;
  parameter ADDR_KEY8        = BASE_ADDR + 32'h00000060;
  parameter ADDR_KEY9        = BASE_ADDR + 32'h00000064;
  parameter ADDR_KEY10       = BASE_ADDR + 32'h00000068;
  parameter ADDR_KEY11       = BASE_ADDR + 32'h0000006C;

  parameter ADDR_BLOCK0      = BASE_ADDR + 32'h00000080;
  parameter ADDR_BLOCK1      = BASE_ADDR + 32'h00000084;
  parameter ADDR_BLOCK2      = BASE_ADDR + 32'h00000088;
  parameter ADDR_BLOCK3      = BASE_ADDR + 32'h0000008C;
  parameter ADDR_BLOCK4      = BASE_ADDR + 32'h00000090;
  parameter ADDR_BLOCK5      = BASE_ADDR + 32'h00000094;
  parameter ADDR_BLOCK6      = BASE_ADDR + 32'h00000098;
  parameter ADDR_BLOCK7      = BASE_ADDR + 32'h0000009C;
  parameter ADDR_BLOCK8      = BASE_ADDR + 32'h000000a0;
  parameter ADDR_BLOCK9      = BASE_ADDR + 32'h000000a4;
  parameter ADDR_BLOCK10     = BASE_ADDR + 32'h000000a8;
  parameter ADDR_BLOCK11     = BASE_ADDR + 32'h000000aC;
  parameter ADDR_BLOCK12     = BASE_ADDR + 32'h000000b0;
  parameter ADDR_BLOCK13     = BASE_ADDR + 32'h000000b4;
  parameter ADDR_BLOCK14     = BASE_ADDR + 32'h000000b8;
  parameter ADDR_BLOCK15     = BASE_ADDR + 32'h000000bC;
  parameter ADDR_BLOCK16     = BASE_ADDR + 32'h000000c0;
  parameter ADDR_BLOCK17     = BASE_ADDR + 32'h000000c4;
  parameter ADDR_BLOCK18     = BASE_ADDR + 32'h000000c8;
  parameter ADDR_BLOCK19     = BASE_ADDR + 32'h000000cC;
  parameter ADDR_BLOCK20     = BASE_ADDR + 32'h000000d0;
  parameter ADDR_BLOCK21     = BASE_ADDR + 32'h000000d4;
  parameter ADDR_BLOCK22     = BASE_ADDR + 32'h000000d8;
  parameter ADDR_BLOCK23     = BASE_ADDR + 32'h000000dC;
  parameter ADDR_BLOCK24     = BASE_ADDR + 32'h000000e0;
  parameter ADDR_BLOCK25     = BASE_ADDR + 32'h000000e4;
  parameter ADDR_BLOCK26     = BASE_ADDR + 32'h000000e8;
  parameter ADDR_BLOCK27     = BASE_ADDR + 32'h000000eC;
  parameter ADDR_BLOCK28     = BASE_ADDR + 32'h000000f0;
  parameter ADDR_BLOCK29     = BASE_ADDR + 32'h000000f4;
  parameter ADDR_BLOCK30     = BASE_ADDR + 32'h000000f8;
  parameter ADDR_BLOCK31     = BASE_ADDR + 32'h000000fC;

  parameter ADDR_TAG0        =  BASE_ADDR + 32'h00000100;
  parameter ADDR_TAG1        =  BASE_ADDR + 32'h00000104;
  parameter ADDR_TAG2        =  BASE_ADDR + 32'h00000108;
  parameter ADDR_TAG3        =  BASE_ADDR + 32'h0000010C;
  parameter ADDR_TAG4        =  BASE_ADDR + 32'h00000110;
  parameter ADDR_TAG5        =  BASE_ADDR + 32'h00000114;
  parameter ADDR_TAG6        =  BASE_ADDR + 32'h00000118;
  parameter ADDR_TAG7        =  BASE_ADDR + 32'h0000011C;
  parameter ADDR_TAG8        =  BASE_ADDR + 32'h00000120;
  parameter ADDR_TAG9        =  BASE_ADDR + 32'h00000124;
  parameter ADDR_TAG10       =  BASE_ADDR + 32'h00000128;
  parameter ADDR_TAG11       =  BASE_ADDR + 32'h0000012C;

  parameter ADDR_LFSR_SEED0  =  BASE_ADDR + 32'h00000130;
  parameter ADDR_LFSR_SEED1  =  BASE_ADDR + 32'h00000134;
  parameter ADDR_LFSR_SEED2  =  BASE_ADDR + 32'h00000138;
  parameter ADDR_LFSR_SEED3  =  BASE_ADDR + 32'h0000013C;
  parameter ADDR_LFSR_SEED4  =  BASE_ADDR + 32'h00000140;

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
  reg [383 : 0] digest_data;

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
  function logic [159 : 0] random_gen();
    return { $random, $random, $random, $random, $random};
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
  task write_block(input [1023 : 0] block);
    begin
      write_single_word(ADDR_BLOCK0, block[1023: 992]);
      write_single_word(ADDR_BLOCK1,  block[991: 960]);
      write_single_word(ADDR_BLOCK2,  block[959: 928]);
      write_single_word(ADDR_BLOCK3,  block[927: 896]);
      write_single_word(ADDR_BLOCK4,  block[895: 864]);
      write_single_word(ADDR_BLOCK5,  block[863: 832]);
      write_single_word(ADDR_BLOCK6,  block[831: 800]);
      write_single_word(ADDR_BLOCK7,  block[799: 768]);
      write_single_word(ADDR_BLOCK8,  block[767: 736]);
      write_single_word(ADDR_BLOCK9,  block[735: 704]);
      write_single_word(ADDR_BLOCK10, block[703: 672]);
      write_single_word(ADDR_BLOCK11, block[671: 640]);
      write_single_word(ADDR_BLOCK12, block[639: 608]);
      write_single_word(ADDR_BLOCK13, block[607: 576]);
      write_single_word(ADDR_BLOCK14, block[575: 544]);
      write_single_word(ADDR_BLOCK15, block[543: 512]);
      write_single_word(ADDR_BLOCK16, block[511: 480]);
      write_single_word(ADDR_BLOCK17, block[479: 448]);
      write_single_word(ADDR_BLOCK18, block[447: 416]);
      write_single_word(ADDR_BLOCK19, block[415: 384]);
      write_single_word(ADDR_BLOCK20, block[383: 352]);
      write_single_word(ADDR_BLOCK21, block[351: 320]);
      write_single_word(ADDR_BLOCK22, block[319: 288]);
      write_single_word(ADDR_BLOCK23, block[287: 256]);
      write_single_word(ADDR_BLOCK24, block[255: 224]);
      write_single_word(ADDR_BLOCK25, block[223: 192]);
      write_single_word(ADDR_BLOCK26, block[191: 160]);
      write_single_word(ADDR_BLOCK27, block[159: 128]);
      write_single_word(ADDR_BLOCK28, block[127: 96 ]);
      write_single_word(ADDR_BLOCK29, block[95 : 64 ]);
      write_single_word(ADDR_BLOCK30, block[63 : 32 ]);
      write_single_word(ADDR_BLOCK31, block[31 : 0  ]);
      
    end
  endtask // write_block


  //----------------------------------------------------------------
  // write_key()
  //
  // Write the given key to the dut.
  //----------------------------------------------------------------
  task write_key(input [383 : 0] key);
    begin
      write_single_word(ADDR_KEY0,  key[383: 352]);
      write_single_word(ADDR_KEY1,  key[351: 320]);
      write_single_word(ADDR_KEY2,  key[319: 288]);
      write_single_word(ADDR_KEY3,  key[287: 256]);
      write_single_word(ADDR_KEY4,  key[255: 224]);
      write_single_word(ADDR_KEY5,  key[223: 192]);
      write_single_word(ADDR_KEY6,  key[191: 160]);
      write_single_word(ADDR_KEY7,  key[159: 128]);
      write_single_word(ADDR_KEY8,  key[127: 96 ]);
      write_single_word(ADDR_KEY9,  key[95 : 64 ]);
      write_single_word(ADDR_KEY10, key[63 : 32 ]);
      write_single_word(ADDR_KEY11, key[31 : 0  ]);
    end
  endtask // write_key

  //----------------------------------------------------------------
  // write_seed()
  //
  // Write the given seed to the dut.
  //----------------------------------------------------------------
  task write_seed(input [159 : 0] seed);
    begin
      write_single_word(ADDR_LFSR_SEED0, seed[159: 128]);
      write_single_word(ADDR_LFSR_SEED1, seed[127: 96 ]);
      write_single_word(ADDR_LFSR_SEED2, seed[95 : 64 ]);
      write_single_word(ADDR_LFSR_SEED3, seed[63 : 32 ]);
      write_single_word(ADDR_LFSR_SEED4, seed[31 : 0  ]);
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
  // read_digest()
  //
  // Read the digest in the dut. The resulting digest will be
  // available in the global variable digest_data.
  //----------------------------------------------------------------
  task read_digest;
    begin
      read_single_word(ADDR_TAG0);
      digest_data[383 : 352] = read_data;
      read_single_word(ADDR_TAG1);
      digest_data[351 : 320] = read_data;
      read_single_word(ADDR_TAG2);
      digest_data[319 : 288] = read_data;
      read_single_word(ADDR_TAG3);
      digest_data[287 : 256] = read_data;
      read_single_word(ADDR_TAG4);
      digest_data[255 : 224] = read_data;
      read_single_word(ADDR_TAG5);
      digest_data[223 : 192] = read_data;
      read_single_word(ADDR_TAG6);
      digest_data[191 : 160] = read_data;
      read_single_word(ADDR_TAG7);
      digest_data[159 : 128] = read_data;
      read_single_word(ADDR_TAG8);
      digest_data[127 : 96] = read_data;
      read_single_word(ADDR_TAG9);
      digest_data[95 : 64] = read_data;
      read_single_word(ADDR_TAG10);
      digest_data[63 :  32] = read_data;
      read_single_word(ADDR_TAG11);
      digest_data[31  :   0] = read_data;
    end
  endtask // read_digest


  //----------------------------------------------------------------
  // single_block_test()
  //
  //
  // Perform test of a single block digest.
  //----------------------------------------------------------------
  task single_block_test(input [383 : 0] key,
                         input [1023: 0] block,
                         input [159: 0]  seed,
                         input [383 : 0] expected
                        );
    begin
      reg [31  : 0] start_time;
      reg [31 : 0] end_time;
      reg [31 : 0] data_in_time;

      start_time = cycle_ctr;

      $display("*** TC%01d - Single block test started.", tc_ctr);

      write_key(key);

      write_block(block);

      write_seed(seed);

      data_in_time = cycle_ctr - start_time;
      $display("***       DATA IN processing time = %01d cycles", data_in_time);

      write_single_word(ADDR_CTRL, CTRL_INIT_VALUE);

      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      data_in_time = cycle_ctr;
      read_digest();

      write_single_word(ADDR_CTRL, {29'h0, 1'b1, 2'b0}); //zeroize

      data_in_time = cycle_ctr - data_in_time;
      $display("***       DATA OUT processing time = %01d cycles", data_in_time);
      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);

      if (digest_data == expected)
        begin
          $display("TC%01d: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR.", tc_ctr);
          $display("TC%01d: Expected: 0x%096x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%096x", tc_ctr, digest_data);
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
  task double_block_test(input [383 : 0] key,
                         input [1023: 0] block0,
                         input [1023: 0] block1,
                         input [159: 0]  seed,
                         input [383 : 0] expected
                        );
    begin
      reg [31  : 0] start_time;
      reg [31 : 0] end_time;

      start_time = cycle_ctr;
      $display("*** TC%01d - Double block test started.", tc_ctr);

      write_key(key);

      // First block
      write_block(block0);

      write_seed(seed);

      write_single_word(ADDR_CTRL, CTRL_INIT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();

      // Final block
      write_block(block1);

      write_single_word(ADDR_CTRL, CTRL_NEXT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      read_digest();

      write_single_word(ADDR_CTRL, {29'h0, 1'b1, 2'b0}); //zeroize

      end_time = cycle_ctr - start_time;
      $display("*** Double block test processing time = %01d cycles", end_time);

      if (digest_data == expected)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%096x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%096x", tc_ctr, digest_data);
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
  task continuous_cmd_test(input [383 : 0] key,
                         input [1023: 0] block0,
                         input [1023: 0] block1,
                         input [159: 0]  seed,
                         input [383 : 0] expected
                        );
    begin
      reg [31  : 0] start_time;
      reg [31 : 0] end_time;

      start_time = cycle_ctr;
      $display("*** TC%01d - continuous_cmd_test started.", tc_ctr);

      write_key(key);

      // First block
      write_block(block0);

      write_seed(seed);

      write_single_word(ADDR_CTRL, CTRL_INIT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);

      for (int i=0; i<10; i++)
        begin
          write_single_word(ADDR_CTRL, CTRL_INIT_VALUE);
          #CLK_PERIOD;
          write_single_word(ADDR_CTRL, CTRL_NEXT_VALUE);
          #CLK_PERIOD;
        end

      #(CLK_PERIOD);
      wait_ready();

      // Final block
      write_block(block1);

      write_single_word(ADDR_CTRL, CTRL_NEXT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);

      for (int i=0; i<10; i++)
        begin
          write_single_word(ADDR_CTRL, CTRL_INIT_VALUE);
          #CLK_PERIOD;
          write_single_word(ADDR_CTRL, CTRL_NEXT_VALUE);
          #CLK_PERIOD;
        end

      #(CLK_PERIOD);
      wait_ready();
      read_digest();

      write_single_word(ADDR_CTRL, {29'h0, 1'b1, 2'b0}); //zeroize

      end_time = cycle_ctr - start_time;
      $display("*** continuous_cmd_test processing time = %01d cycles", end_time);

      if (digest_data == expected)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%096x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%096x", tc_ctr, digest_data);
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
  task zeroize_test(input [383 : 0] key,
                    input [1023: 0] block0,
                    input [1023: 0] block1,
                    input [159: 0]  seed,
                    input [383 : 0] expected
                  );
    begin

      $display("*** TC%01d - zeroize test started.", tc_ctr);

      // First test: assert zeroize when engine is working
      write_key(key);
      
      write_block(block0);

      write_seed(seed);

      write_single_word(ADDR_CTRL, CTRL_INIT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      for (int i=0; i<10; i++)
        begin
          #(CLK_PERIOD);
        end

      write_single_word(ADDR_CTRL, {29'h0, 1'b1, 2'b0}); //zeroize

      wait_ready();
      read_digest();
      if (digest_data == 0)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%096x", tc_ctr, 0);
          $display("TC%01d: Got:      0x%096x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end
      tc_ctr = tc_ctr + 1;

      // Second test: assert zeroize with INIT
      write_key(key);
      
      write_block(block0);

      write_seed(seed);

      write_single_word(ADDR_CTRL, {29'h0, 1'b1, CTRL_INIT_VALUE}); //zeroize
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
          $display("TC%01d: Expected: 0x%096x", tc_ctr, 0);
          $display("TC%01d: Got:      0x%096x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end
      tc_ctr = tc_ctr + 1;

      // Third test: assert zeroize with NEXT
      write_key(key);
      
      write_block(block0);

      write_seed(seed);

      write_single_word(ADDR_CTRL, {29'h0, 1'b1, CTRL_NEXT_VALUE}); //zeroize
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
          $display("TC%01d: Expected: 0x%096x", tc_ctr, 0);
          $display("TC%01d: Got:      0x%096x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end
      tc_ctr = tc_ctr + 1;

      // Forth test: assert zeroize after NEXT
      write_key(key);
      
      write_block(block0);

      write_seed(seed);

      write_single_word(ADDR_CTRL, CTRL_NEXT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      for (int i=0; i<10; i++)
        begin
          #(CLK_PERIOD);
        end

      write_single_word(ADDR_CTRL, {29'h0, 1'b1, 2'b0}); //zeroize

      wait_ready();
      read_digest();
      if (digest_data == 0)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%096x", tc_ctr, 0);
          $display("TC%01d: Got:      0x%096x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - zeroize test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // zeroize_test

  //----------------------------------------------------------------
  // hmac_tests()
  //
  // Run test cases for hmac.
  // Test cases taken from:
  // https://datatracker.ietf.org/doc/html/rfc4868#section-2.7 
  //----------------------------------------------------------------
  task hmac_tests;
    begin : hmac_tests_block
      reg [383 : 0] key0;
      reg [1023: 0] data0;
      reg [159 : 0] seed0;
      reg [383 : 0] expected0;

      reg [383 : 0] key1;
      reg [1023: 0] data1;
      reg [159 : 0] seed1;
      reg [383 : 0] expected1;

      reg [383 : 0] key2;
      reg [1023: 0] data2;
      reg [159 : 0] seed2;
      reg [383 : 0] expected2;

      reg [383 : 0] key3;
      reg [1023: 0] data3;
      reg [159 : 0] seed3;
      reg [383 : 0] expected3;

      reg [383 : 0] key4;
      reg [1023: 0] data40;
      reg [1023: 0] data41;
      reg [159 : 0] seed4;
      reg [383 : 0] expected4;

      

      $display("*** Testcases for PRF-HMAC-SHA-384 functionality started.");

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
            
      single_block_test(key0, data0, seed0, expected0);

      single_block_test(key1, data1, seed1, expected1);

      single_block_test(key2, data2, seed2, expected2);

      single_block_test(key3, data3, seed3, expected3);

      key4   = 384'h1e6a3e8998be7c36c5a511c4f03fcfba543d678f1000e2f6a61c2a95f79bb006fc782a679a0b890e3374b20df710f6c2;
      data40 = 1024'hdbf031b43f84bcf3cc9339e65c3659151d3061dd2d5fb0b2d37fbe4fca4ea373b567ae3513ea095013efc7b19f6851ad73c26176034964999c2c3cf2fd58561a9f791839a2199f2a9405edd0478ac64a9557aec86940d465d90364489e4d32f168ce2eefec74eb7e653f8da640308f72f0bd7b1a698c683870c7439869b969ae;
      data41 = 1024'hbea9f4f6bacdc04d4ec4f6bcc17874940336c7899553800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008b0;
      expected4 = 384'h8aba65c07793e1d8a709fbda35ae71804dc0741166dda5746fb3b1c0e91957bbd0d539a469c2ea3577b75d5c0f150ce7;
      seed4 = random_gen();

      double_block_test(key4, data40, data41, seed4, expected4);

      continuous_cmd_test(key4, data40, data41, seed4, expected4);

      zeroize_test(key4, data40, data41, seed4, expected4);
      
      $display("*** Testcases for PRF-HMAC-SHA-384 functionality completed.");
    end
  endtask // hmac_tests


  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -- Testbench for PRF-HMAC-SHA-384 started --");

      init_sim();
      reset_dut();

      check_name_version();
      hmac_tests();

      display_test_result();

      $display("   -- Testbench for PRF-HMAC-SHA-384 done. --");
      $finish;
    end // main
endmodule // hmac_ctrl_tb

//======================================================================
// EOF hmac_ctrl_tb.sv
//======================================================================
