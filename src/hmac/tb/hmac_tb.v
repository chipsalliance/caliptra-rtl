//======================================================================
//
// hmac_tb.v
// -----------
// Testbench for the HMAC-SHA-256-128 top level wrapper.
//
//
// Author: Mojtaba Bisheh Niasar
// All rights reserved.
//
//
//======================================================================

`default_nettype none

module hmac_tb();

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

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0] cycle_ctr;
  reg [63 : 0] error_ctr;
  reg [63 : 0] tc_ctr;

  reg           clk_tb;
  reg           reset_n_tb;
  reg           cs_tb;
  reg           we_tb;
  reg [31 : 0]  address_tb;
  reg [63 : 0]  write_data_tb;
  wire [63 : 0] read_data_tb;

  reg [63 : 0]  read_data;
  reg [255 : 0] digest_data;


  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  hmac dut(
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
      #(2 * CLK_HALF_PERIOD);
      cycle_ctr = cycle_ctr + 1;
    end


  //----------------------------------------------------------------
  // dump_dut_state()
  //
  // Dump the state of the dump when needed.
  //----------------------------------------------------------------
  task dump_dut_state;
    begin
      $display("State of DUT");
      $display("------------");
      $display("Inputs and outputs:");
      $display("cs = 0x%01x, we = 0x%01x",
               dut.cs, dut.we);
      $display("address = 0x%08x", dut.address);
      $display("write_data = 0x%08x, read_data = 0x%08x",
               dut.write_data, dut.read_data);
      $display("tmp_read_data = 0x%08x", dut.tmp_read_data);
      $display("");

      $display("Control and status:");
      $display("ctrl = 0x%02x, status = 0x%02x",
               {dut.next_reg, dut.init_reg},
               {dut.tag_valid_reg, dut.ready_reg});
      $display("");

      $display("Message block:");
      $display("block0  = 0x%08x, block1  = 0x%08x, block2  = 0x%08x,  block3  = 0x%08x",
               dut.block_reg[00], dut.block_reg[01], dut.block_reg[02], dut.block_reg[03]);
      $display("block4  = 0x%08x, block5  = 0x%08x, block6  = 0x%08x,  block7  = 0x%08x",
               dut.block_reg[04], dut.block_reg[05], dut.block_reg[06], dut.block_reg[07]);
      $display("");

      $display("TAG:");
      $display("tag = 0x%064x", dut.tag_reg);
      $display("");

    end
  endtask // dump_dut_state


  //----------------------------------------------------------------
  // reset_dut()
  //
  // Toggles reset to force the DUT into a well defined state.
  //----------------------------------------------------------------
  task reset_dut;
    begin
      $display("*** Toggle reset.");
      reset_n_tb = 0;
      #(4 * CLK_HALF_PERIOD);
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
      cycle_ctr = 64'h0;
      error_ctr = 64'h0;
      tc_ctr = 64'h0;

      clk_tb = 0;
      reset_n_tb = 0;
      cs_tb = 0;
      we_tb = 0;
      address_tb = 32'h0;
      write_data_tb = 64'h0;
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

      while (read_data == 0)
        begin
          read_word(ADDR_STATUS);
        end
    end
  endtask // wait_ready


  //----------------------------------------------------------------
  // write_word()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_word(input [31 : 0]  address,
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
      #(CLK_PERIOD);
      cs_tb = 0;
      we_tb = 0;
    end
  endtask // write_word


  //----------------------------------------------------------------
  // write_block()
  //
  // Write the given block to the dut.
  //----------------------------------------------------------------
  task write_block(input [511 : 0] block);
    begin
      write_word(ADDR_BLOCK0,  block[511 : 448]);
      write_word(ADDR_BLOCK1,  block[447 : 384]);
      write_word(ADDR_BLOCK2,  block[383 : 320]);
      write_word(ADDR_BLOCK3,  block[319 : 256]);
      write_word(ADDR_BLOCK4,  block[255 : 192]);
      write_word(ADDR_BLOCK5,  block[191 : 128]);
      write_word(ADDR_BLOCK6,  block[127 :  64]);
      write_word(ADDR_BLOCK7,  block[63  :   0]);
    end
  endtask // write_block


  //----------------------------------------------------------------
  // write_key()
  //
  // Write the given key to the dut.
  //----------------------------------------------------------------
  task write_key(input [255 : 0] key);
    begin
      write_word(ADDR_KEY0,  key[255 : 192]);
      write_word(ADDR_KEY1,  key[191 : 128]);
      write_word(ADDR_KEY2,  key[127 :  64]);
      write_word(ADDR_KEY3,  key[63  :   0]);
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
  // check_name_version()
  //
  // Read the name and version from the DUT.
  //----------------------------------------------------------------
  task check_name_version;
    reg [63 : 0] name;
    reg [63 : 0] version;
    begin

      read_word(ADDR_NAME);
      name = read_data;
      read_word(ADDR_VERSION);
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
      read_word(ADDR_TAG0);
      digest_data[255 : 192] = read_data;
      read_word(ADDR_TAG1);
      digest_data[191 : 128] = read_data;
      read_word(ADDR_TAG2);
      digest_data[127 :  64] = read_data;
      read_word(ADDR_TAG3);
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
                         input [255 : 0] expected);
    begin
      $display("*** TC%01d - Single block test started.", tc_ctr);

      write_key(key);

      write_block(block);

      write_word(ADDR_CTRL, CTRL_INIT_VALUE);

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

      write_word(ADDR_CTRL, CTRL_INIT_VALUE);

      #(CLK_PERIOD);
      wait_ready();
      
      // Final block
      write_block(block1);

      write_word(ADDR_CTRL, CTRL_NEXT_VALUE);

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
  // https://datatracker.ietf.org/doc/html/rfc4868
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
endmodule // hmac_tb

//======================================================================
// EOF hmac_tb.v
//======================================================================
