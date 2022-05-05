//======================================================================
//
// hmac_ctrl_tb.sv
// --------
// HMAC testbench for the hmac AHb_lite interface controller.
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module hmac_ctrl_tb();

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG = 0;

  parameter CLK_HALF_PERIOD = 2;
  parameter CLK_PERIOD = 2 * CLK_HALF_PERIOD;

  // The address map.
  parameter BASE_ADDR        = 32'h70000000;

  parameter ADDR_NAME        = BASE_ADDR + 32'h00000000;
  parameter ADDR_VERSION     = BASE_ADDR + 32'h00000008;

  parameter ADDR_CTRL        = BASE_ADDR + 32'h00000010;
  parameter CTRL_INIT_VALUE  = 8'h01;
  parameter CTRL_NEXT_VALUE  = 8'h02;
  parameter CTRL_MODE_VALUE  = 8'h04;

  parameter ADDR_STATUS      = BASE_ADDR + 32'h00000018;
  parameter STATUS_READY_BIT = 0;
  parameter STATUS_VALID_BIT = 1;

  parameter ADDR_KEY0        = BASE_ADDR + 32'h00000040;
  parameter ADDR_KEY1        = BASE_ADDR + 32'h00000048;
  parameter ADDR_KEY2        = BASE_ADDR + 32'h00000050;
  parameter ADDR_KEY3        = BASE_ADDR + 32'h00000058;

  parameter ADDR_BLOCK0      = BASE_ADDR + 32'h00000080;
  parameter ADDR_BLOCK1      = BASE_ADDR + 32'h00000088;
  parameter ADDR_BLOCK2      = BASE_ADDR + 32'h00000090;
  parameter ADDR_BLOCK3      = BASE_ADDR + 32'h00000098;
  parameter ADDR_BLOCK4      = BASE_ADDR + 32'h000000a0;
  parameter ADDR_BLOCK5      = BASE_ADDR + 32'h000000a8;
  parameter ADDR_BLOCK6      = BASE_ADDR + 32'h000000b0;
  parameter ADDR_BLOCK7      = BASE_ADDR + 32'h000000b8;

  parameter ADDR_TAG0        = BASE_ADDR + 32'h00000100;
  parameter ADDR_TAG1        = BASE_ADDR + 32'h00000108;
  parameter ADDR_TAG2        = BASE_ADDR + 32'h00000110;
  parameter ADDR_TAG3        = BASE_ADDR + 32'h00000118;

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  parameter AHB_ADDR_WIDTH = 32;
  parameter AHB_DATA_WIDTH = 64;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0] cycle_ctr;
  reg [63 : 0] error_ctr;
  reg [63 : 0] tc_ctr;

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
  reg [255 : 0] digest_data;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  hmac_ctrl #(
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
  // reset_dut()
  //
  // Toggles reset to force the DUT into a well defined state.
  //----------------------------------------------------------------
  task reset_dut;
    begin
      $display("*** Toggle reset.");
      reset_n_tb = 0;
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

      hadrr_i_tb      = 0;
      hwdata_i_tb     = 0;
      hsel_i_tb       = 0;
      hwrite_i_tb     = 0;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
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
        end
      else
        begin
          $display("*** %02d test cases completed.", tc_ctr);
          $display("*** %02d errors detected during testing.", error_ctr);
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
  task write_block(input [511 : 0] block);
    begin
      write_single_word(ADDR_BLOCK0,  block[511 : 448]);
      write_single_word(ADDR_BLOCK1,  block[447 : 384]);
      write_single_word(ADDR_BLOCK2,  block[383 : 320]);
      write_single_word(ADDR_BLOCK3,  block[319 : 256]);
      write_single_word(ADDR_BLOCK4,  block[255 : 192]);
      write_single_word(ADDR_BLOCK5,  block[191 : 128]);
      write_single_word(ADDR_BLOCK6,  block[127 :  64]);
      write_single_word(ADDR_BLOCK7,  block[63  :   0]);
    end
  endtask // write_block


  //----------------------------------------------------------------
  // write_key()
  //
  // Write the given key to the dut.
  //----------------------------------------------------------------
  task write_key(input [255 : 0] key);
    begin
      write_single_word(ADDR_KEY0,  key[255 : 192]);
      write_single_word(ADDR_KEY1,  key[191 : 128]);
      write_single_word(ADDR_KEY2,  key[127 :  64]);
      write_single_word(ADDR_KEY3,  key[63  :   0]);
    end
  endtask // write_key

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
      digest_data[255 : 192] = read_data;
      read_single_word(ADDR_TAG1);
      digest_data[191 : 128] = read_data;
      read_single_word(ADDR_TAG2);
      digest_data[127 :  64] = read_data;
      read_single_word(ADDR_TAG3);
      digest_data[63  :   0] = read_data;
    end
  endtask // read_digest


  //----------------------------------------------------------------
  // single_block_test()
  //
  //
  // Perform test of a single block digest.
  //----------------------------------------------------------------
  task single_block_test(input [255 : 0] key,
                         input [511 : 0] block,
                         input [255 : 0] expected
                        );
    begin
      $display("*** TC%01d - Single block test started.", tc_ctr);

      write_key(key);

      write_block(block);

      write_single_word(ADDR_CTRL, CTRL_INIT_VALUE);

      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      read_digest();

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
  task double_block_test(input [255 : 0] key,
                         input [511 : 0] block0,
                         input [511 : 0] block1,
                         input [255 : 0] expected
                        );
    begin
      $display("*** TC%01d - Double block test started.", tc_ctr);

      write_key(key);

      // First block
      write_block(block0);

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

      if (digest_data == expected)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - Double block test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // double_block_test


  //----------------------------------------------------------------
  // hmac_tests()
  //
  // Run test cases for hmac.
  // Test cases taken from:
  // http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA256.pdf
  //----------------------------------------------------------------
  task hmac_tests;
    begin : hmac_tests_block
      reg [255 : 0] key0;
      reg [511 : 0] data0;
      reg [255 : 0] expected0;

      reg [255 : 0] key1;
      reg [511 : 0] data1;
      reg [255 : 0] expected1;

      reg [255 : 0] key2;
      reg [511 : 0] data2;
      reg [255 : 0] expected2;

      reg [255 : 0] key3;
      reg [511 : 0] data3;
      reg [255 : 0] expected3;

      reg [255 : 0] key4;
      reg [511 : 0] data4_0;
      reg [511 : 0] data4_1;
      reg [255 : 0] expected4;

      $display("*** Testcases for HMAC-SHA-256-128 functionality started.");

      key0 = 256'h0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b;
      data0 = 512'h48692054686572658000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000240;
      expected0 = 256'h198a607eb44bfbc69903a0f1cf2bbdc5ba0aa3f3d9ae3c1c7a3b1696a0b68cf7;

      key1 = 256'h4a6566654a6566654a6566654a6566654a6566654a6566654a6566654a656665;
      data1 = 512'h7768617420646f2079612077616e7420666f72206e6f7468696e673f8000000000000000000000000000000000000000000000000000000000000000000002e0;
      expected1 = 256'h167f928588c5cc2eef8e3093caa0e87c9ff566a14794aa61648d81621a2a40c6;

      key2 = 256'haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;
      data2 = 512'hdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd8000000000000000000000000390;
      expected2 = 256'hcdcb1220d1ecccea91e53aba3092f962e549fe6ce9ed7fdc43191fbde45c30b0;

      key3 = 256'h0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20;
      data3 = 512'hcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd8000000000000000000000000390;
      expected3 = 256'h372efcf9b40b35c2115b1346903d2ef42fced46f0846e7257bb156d3d7b30d3f;
      
      key4 = 256'h0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20;
      data4_0 = 512'hddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddcdcdcdcdcdcdcdcdcdcdcdcdcdcd;
      data4_1 = 512'hcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd80000000000000000000000000000000000000000000000000000520;
      expected4 = 256'h7a3437d7bab9788715503f45ee2e404e33d3cfd4098a93829d961641bb2875e8;

      single_block_test(key0, data0, expected0);

      single_block_test(key1, data1, expected1);

      single_block_test(key2, data2, expected2);

      single_block_test(key3, data3, expected3);

      double_block_test(key4, data4_0, data4_1, expected4);
      
      $display("*** Testcases for HMAC-SHA-256-128 functionality completed.");
    end
  endtask // hmac_tests


  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -- Testbench for HMAC-SHA-256-128 started --");

      init_sim();
      reset_dut();

      check_name_version();
      hmac_tests();

      display_test_result();

      $display("   -- Testbench for HMAC-SHA-256-128 done. --");
      $finish;
    end // main
endmodule // hmac_ctrl_tb

//======================================================================
// EOF hmac_ctrl_tb.sv
//======================================================================
