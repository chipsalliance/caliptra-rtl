
module sha512_ctrl_tb();

//----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG = 0;

  parameter CLK_HALF_PERIOD = 1;
  parameter CLK_PERIOD      = 2*CLK_HALF_PERIOD;

  // The address map.
  parameter ADDR_NAME0           = 8'h00;
  parameter ADDR_NAME1           = 8'h01;
  parameter ADDR_VERSION         = 8'h02;

  parameter ADDR_CTRL            = 8'h08;
  parameter CTRL_INIT_BIT        = 0;
  parameter CTRL_NEXT_BIT        = 1;
  parameter CTRL_MODE_LOW_BIT    = 2;
  parameter CTRL_MODE_HIGH_BIT   = 3;
  parameter CTRL_WORK_FACTOR_BIT = 7;

  parameter ADDR_STATUS          = 8'h09;
  parameter STATUS_READY_BIT     = 0;
  parameter STATUS_VALID_BIT     = 1;

  parameter ADDR_WORK_FACTOR_NUM = 8'h0a;

  parameter ADDR_BLOCK0          = 8'h10;
  parameter ADDR_BLOCK1          = 8'h11;
  parameter ADDR_BLOCK2          = 8'h12;
  parameter ADDR_BLOCK3          = 8'h13;
  parameter ADDR_BLOCK4          = 8'h14;
  parameter ADDR_BLOCK5          = 8'h15;
  parameter ADDR_BLOCK6          = 8'h16;
  parameter ADDR_BLOCK7          = 8'h17;
  parameter ADDR_BLOCK8          = 8'h18;
  parameter ADDR_BLOCK9          = 8'h19;
  parameter ADDR_BLOCK10         = 8'h1a;
  parameter ADDR_BLOCK11         = 8'h1b;
  parameter ADDR_BLOCK12         = 8'h1c;
  parameter ADDR_BLOCK13         = 8'h1d;
  parameter ADDR_BLOCK14         = 8'h1e;
  parameter ADDR_BLOCK15         = 8'h1f;

  parameter ADDR_DIGEST0         = 8'h40;
  parameter ADDR_DIGEST1         = 8'h41;
  parameter ADDR_DIGEST2         = 8'h42;
  parameter ADDR_DIGEST3         = 8'h43;
  parameter ADDR_DIGEST4         = 8'h44;
  parameter ADDR_DIGEST5         = 8'h45;
  parameter ADDR_DIGEST6         = 8'h46;
  parameter ADDR_DIGEST7         = 8'h47;

  parameter MODE_SHA_512_224     = 2'h0;
  parameter MODE_SHA_512_256     = 2'h1;
  parameter MODE_SHA_384         = 2'h2;
  parameter MODE_SHA_512         = 2'h3;

  parameter CTRL_INIT_VALUE        = 2'h1;
  parameter CTRL_NEXT_VALUE        = 2'h2;
  parameter CTRL_WORK_FACTOR_VALUE = 1'h1;

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  parameter AHB_ADDR_WIDTH = 8;
  parameter AHB_DATA_WIDTH = 64;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [31 : 0]  cycle_ctr;
  reg [31 : 0]  error_ctr;
  reg [31 : 0]  tc_ctr;

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
  reg [511 : 0] digest_data;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  sha512_ctrl #(
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
      cycle_ctr = 32'h00000000;
      error_ctr = 32'h00000000;
      tc_ctr    = 32'h00000000;

      clk_tb        = 1;
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
  // read_word()
  //
  // Read a data word from the given address in the DUT.
  // the word read will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_single_word(input [7 : 0]  address);
    begin
      hadrr_i_tb      = address;
      hwdata_i_tb     = 0;
      hsel_i_tb       = 1;
      hwrite_i_tb     = 0;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_BUSY;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 3'b011;
      #(2*CLK_PERIOD);

      read_data = hrdata_o_tb;
      hsel_i_tb = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      //#(CLK_PERIOD);

      if (DEBUG)
        begin
          $display("*** Reading 0x%16x from 0x%02x.", read_data, address);
          $display("");
        end
    end
  endtask // read_word


  //----------------------------------------------------------------
  // write_single_word()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_single_word(input [7 : 0]  address,
                  input [63 : 0] word);
    begin
      if (DEBUG)
        begin
          $display("*** Writing 0x%16x to 0x%02x.", word, address);
          $display("");
        end

      hadrr_i_tb      = address;
      hwdata_i_tb     = 0;
      hsel_i_tb       = 1;
      hwrite_i_tb     = 1;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_BUSY;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 3'b011;
      #(CLK_PERIOD);

      hwdata_i_tb     = word;
      hwrite_i_tb     = 0;
      #(CLK_PERIOD);

      hsel_i_tb       = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      //#(CLK_PERIOD);
    end
  endtask // write_single_word


  //----------------------------------------------------------------
  // write_block()
  //
  // Write the given block to the dut.
  //----------------------------------------------------------------
  task write_block(input [1023 : 0] block);
    begin
      /*
      hwdata_i_tb     = 0;
      hsel_i_tb       = 1;
      hwrite_i_tb     = 1;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_BUSY;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 3'b011;
      hadrr_i_tb      = ADDR_BLOCK0;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[1023 : 960];
      hadrr_i_tb      = ADDR_BLOCK1;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[959  : 896];
      hadrr_i_tb      = ADDR_BLOCK2;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[895  : 832];
      hadrr_i_tb      = ADDR_BLOCK3;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[831  : 768];
      hadrr_i_tb      = ADDR_BLOCK4;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[767  : 704];
      hadrr_i_tb      = ADDR_BLOCK5;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[703  : 640];
      hadrr_i_tb      = ADDR_BLOCK6;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[639  : 576];
      hadrr_i_tb      = ADDR_BLOCK7;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[575  : 512];
      hadrr_i_tb      = ADDR_BLOCK8;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[511  : 448];
      hadrr_i_tb      = ADDR_BLOCK9;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[447  : 384];
      hadrr_i_tb      = ADDR_BLOCK10;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[383  : 320];
      hadrr_i_tb      = ADDR_BLOCK11;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[319  : 256];
      hadrr_i_tb      = ADDR_BLOCK12;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[255  : 192];
      hadrr_i_tb      = ADDR_BLOCK13;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[191  : 128];
      hadrr_i_tb      = ADDR_BLOCK14;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[127  :  64];
      hadrr_i_tb      = ADDR_BLOCK15;
      #(CLK_PERIOD);

      hwdata_i_tb     = block[63   :   0];
      hwrite_i_tb     = 0;
      #(CLK_PERIOD);

      hsel_i_tb       = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      */

      
      write_single_word(ADDR_BLOCK0,  block[1023 : 960]);
      write_single_word(ADDR_BLOCK1,  block[959  : 896]);
      write_single_word(ADDR_BLOCK2,  block[895  : 832]);
      write_single_word(ADDR_BLOCK3,  block[831  : 768]);
      write_single_word(ADDR_BLOCK4,  block[767  : 704]);
      write_single_word(ADDR_BLOCK5,  block[703  : 640]);
      write_single_word(ADDR_BLOCK6,  block[639  : 576]);
      write_single_word(ADDR_BLOCK7,  block[575  : 512]);
      write_single_word(ADDR_BLOCK8,  block[511  : 448]);
      write_single_word(ADDR_BLOCK9,  block[447  : 384]);
      write_single_word(ADDR_BLOCK10, block[383  : 320]);
      write_single_word(ADDR_BLOCK11, block[319  : 256]);
      write_single_word(ADDR_BLOCK12, block[255  : 192]);
      write_single_word(ADDR_BLOCK13, block[191  : 128]);
      write_single_word(ADDR_BLOCK14, block[127  :  64]);
      write_single_word(ADDR_BLOCK15, block[63   :   0]);
      
    end
  endtask // write_block


  //----------------------------------------------------------------
  // get_mask()
  //
  // Create the mask needed for a given mode.
  //----------------------------------------------------------------
  function [511 : 0] get_mask(input [1 : 0] mode);
    begin
      case (mode)
        MODE_SHA_512_224:
          begin
            if (DEBUG)
              begin
                $display("Mode MODE_SHA_512_224");
              end
            get_mask = {{7{32'hffffffff}}, {9{32'h00000000}}};
          end

        MODE_SHA_512_256:
          begin
            if (DEBUG)
              begin
                $display("Mode MODE_SHA_512_256");
              end
            get_mask = {{8{32'hffffffff}}, {8{32'h00000000}}};
          end

        MODE_SHA_384:
          begin
            if (DEBUG)
              begin
                $display("Mode MODE_SHA_512_384");
              end
            get_mask = {{12{32'hffffffff}}, {4{32'h00000000}}};
          end

        MODE_SHA_512:
          begin
            if (DEBUG)
              begin
                $display("Mode MODE_SHA_512");
              end
            get_mask = {16{32'hffffffff}};
          end
      endcase // case (mode)
    end
  endfunction // get_mask



  //----------------------------------------------------------------
  // single_block_test()
  //
  //
  // Perform test of a single block digest.
  //----------------------------------------------------------------
  task single_block_test(input [7 : 0]    tc_number,
                         input [1 : 0]    mode,
                         input [1023 : 0] block,
                         input [511 : 0]  expected);

    reg [511 : 0] mask;
    reg [511 : 0] masked_data;

    begin
      $display("*** TC%01d - Single block test started.", tc_ctr);

      write_block(block);
      write_single_word(ADDR_CTRL, {60'h000000000000000, mode, CTRL_INIT_VALUE});
      #(CLK_PERIOD);
      wait_ready();
      read_digest();

      mask = get_mask(mode);
      masked_data = digest_data & mask;

      if (DEBUG)
        begin
          $display("masked_data = 0x%0128x", masked_data);
        end

      if (masked_data == expected)
        begin
          $display("TC%01d: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR.", tc_ctr);
          $display("TC%01d: Expected: 0x%0128x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%0128x", tc_ctr, masked_data);
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
  task double_block_test(input [7 : 0]    tc_number,
                         input [1 : 0]    mode,
                         input [1023 : 0] block0,
                         input [1023 : 0] block1,
                         input [511 : 0]  expected0,
                         input [511 : 0]  expected1
                        );
    reg [511 : 0] mask;
    reg [511 : 0] masked_data1;
    //reg [31 :  0] ctrl_cmd;

    begin
      $display("*** TC%01d - Double block test started.", tc_ctr);

      // First block
      write_block(block0);
      write_single_word(ADDR_CTRL, {60'h000000000000000, mode, CTRL_INIT_VALUE});
      #(CLK_PERIOD);
      wait_ready();
      read_digest();

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
      write_single_word(ADDR_CTRL, {60'h000000000000000, mode, CTRL_NEXT_VALUE});
      #(CLK_PERIOD);
      wait_ready();
      read_digest();

      mask = get_mask(mode);
      masked_data1 = digest_data & mask;

      if (masked_data1 == expected1)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%0128x", tc_ctr, expected1);
          $display("TC%01d: Got:      0x%0128x", tc_ctr, masked_data1);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - Double block test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // double_block_test


  //----------------------------------------------------------------
  // work_factor_test()
  //
  // Perform test of the work factor function.
  //----------------------------------------------------------------
  task work_factor_test;
    reg [1023 : 0] my_block;
    reg [511 :  0] my_digest;
    reg [63 : 0]   my_ctrl_cmd;

    begin
      $display("*** TC%01d - Work factor test started.", tc_ctr);

      // Read out work factor number.
      read_single_word(ADDR_WORK_FACTOR_NUM);

      // Trying to change the work factor number.
      write_single_word(ADDR_WORK_FACTOR_NUM, 64'h0000000000000003);
      read_single_word(ADDR_WORK_FACTOR_NUM);

      // Set block to all zero
      my_block = {16{64'h0000000000000000}};
      write_block(my_block);

      // Set init+ work factor. We use SHA-512 mode.
      my_ctrl_cmd = 64'h0000000000000000 + (CTRL_WORK_FACTOR_VALUE << 7) +
                    (MODE_SHA_512 << 2) + CTRL_INIT_VALUE;
      write_single_word(ADDR_CTRL, my_ctrl_cmd);
      #(CLK_PERIOD);
      wait_ready();
      read_digest();

      $display("*** TC%01d - Work factor test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // work_factor_test



  //----------------------------------------------------------------
  // read_digest()
  //
  // Read the digest in the dut. The resulting digest will be
  // available in the global variable digest_data.
  //----------------------------------------------------------------
  task read_digest;
    begin
      hwdata_i_tb     = 0;
      hsel_i_tb       = 1;
      hwrite_i_tb     = 0;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_BUSY;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 3'b011;
      hadrr_i_tb      = ADDR_DIGEST0;
      #(CLK_PERIOD);

      read_data = hrdata_o_tb;
      hadrr_i_tb      = ADDR_DIGEST1;
      #(CLK_PERIOD);

      read_data = hrdata_o_tb;
      digest_data[511 : 448] = read_data;
      hadrr_i_tb      = ADDR_DIGEST2;
      #(CLK_PERIOD);

      read_data = hrdata_o_tb;
      digest_data[447 : 384] = read_data;
      hadrr_i_tb      = ADDR_DIGEST3;
      #(CLK_PERIOD);

      read_data = hrdata_o_tb;
      digest_data[383 : 320] = read_data;
      hadrr_i_tb      = ADDR_DIGEST4;
      #(CLK_PERIOD);

      read_data = hrdata_o_tb;
      digest_data[319 : 256] = read_data;
      hadrr_i_tb      = ADDR_DIGEST5;
      #(CLK_PERIOD);

      read_data = hrdata_o_tb;
      digest_data[255 : 192] = read_data;
      hadrr_i_tb      = ADDR_DIGEST6;
      #(CLK_PERIOD);  

      read_data = hrdata_o_tb;
      digest_data[191 : 128] = read_data;
      hadrr_i_tb      = ADDR_DIGEST7;
      #(CLK_PERIOD); 

      read_data = hrdata_o_tb;
      digest_data[127 :  64] = read_data;
      #(CLK_PERIOD); 

      read_data = hrdata_o_tb;
      digest_data[63  :   0] = read_data;
      #(CLK_PERIOD); 

      hsel_i_tb = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;

      /*
      read_single_word(ADDR_DIGEST0);
      digest_data[511 : 448] = read_data;
      read_single_word(ADDR_DIGEST1);
      digest_data[447 : 384] = read_data;
      read_single_word(ADDR_DIGEST2);
      digest_data[383 : 320] = read_data;
      read_single_word(ADDR_DIGEST3);
      digest_data[319 : 256] = read_data;
      read_single_word(ADDR_DIGEST4);
      digest_data[255 : 192] = read_data;
      read_single_word(ADDR_DIGEST5);
      digest_data[191 : 128] = read_data;
      read_single_word(ADDR_DIGEST6);
      digest_data[127 :  64] = read_data;
      read_single_word(ADDR_DIGEST7);
      digest_data[63  :   0] = read_data;
      */
    end
  endtask // read_digest


  //----------------------------------------------------------------
  // check_name_version()
  //
  // Read the name and version from the DUT.
  //----------------------------------------------------------------
  task check_name_version;
    reg [63 : 0] name0;
    reg [63 : 0] name1;
    reg [63 : 0] version;
    begin

      read_single_word(ADDR_NAME0);
      name0 = read_data;
      read_single_word(ADDR_NAME1);
      name1 = read_data;
      read_single_word(ADDR_VERSION);
      version = read_data;

      $display("DUT name: %c%c%c%c%c%c%c%c",
               name0[31 : 24], name0[23 : 16], name0[15 : 8], name0[7 : 0],
               name1[31 : 24], name1[23 : 16], name1[15 : 8], name1[7 : 0]);
      $display("DUT version: %c%c%c%c",
               version[31 : 24], version[23 : 16], version[15 : 8], version[7 : 0]);
    end
  endtask // check_name_version




  //----------------------------------------------------------------
  // sha512_test
  // The main test functionality.
  //
  // Test cases taken from:
  // http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA_All.pdf
  //----------------------------------------------------------------
  initial
    begin : sha512_test
      reg [1024 : 0] single_block;
      reg [511 : 0]  tc1_expected;
      reg [511 : 0]  tc2_expected;
      reg [511 : 0]  tc3_expected;
      reg [511 : 0]  tc4_expected;

      reg [1024 : 0] double_block_one;
      reg [1024 : 0] double_block_two;
      reg [511 : 0]  tc5_expected;
      reg [511 : 0]  tc6_expected;
      reg [511 : 0]  tc7_expected;
      reg [511 : 0]  tc8_expected;
      reg [511 : 0]  tc9_expected;
      reg [511 : 0]  tc10_expected;
      reg [511 : 0]  tc11_expected;
      reg [511 : 0]  tc12_expected;

      $display("   -- Testbench for sha512 started --");

      init_sim();
      reset_dut();
      check_name_version();


      // Single block test mesage.
      single_block = 1024'h6162638000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018;

      // SHA-512 single block digest and test.
      tc1_expected = 512'hDDAF35A193617ABACC417349AE20413112E6FA4E89A97EA20A9EEEE64B55D39A2192992A274FC1A836BA3C23A3FEEBBD454D4423643CE80E2A9AC94FA54CA49F;
      single_block_test(8'h01, MODE_SHA_512, single_block, tc1_expected);

      // SHA-512_224 single block digest and test.
      tc2_expected = {224'h4634270F707B6A54DAAE7530460842E20E37ED265CEEE9A43E8924AA, {9{32'h00000000}}};
      single_block_test(8'h02, MODE_SHA_512_224, single_block, tc2_expected);

      // SHA-512_256 single block digest and test.
      tc3_expected = {256'h53048E2681941EF99B2E29B76B4C7DABE4C2D0C634FC6D46E0E2F13107E7AF23, {8{32'h00000000}}};
      single_block_test(8'h03, MODE_SHA_512_256, single_block, tc3_expected);

      // SHA-384 single block digest and test.
      tc4_expected = {384'hCB00753F45A35E8BB5A03D699AC65007272C32AB0EDED1631A8B605A43FF5BED8086072BA1E7CC2358BAECA134C825A7, {4{32'h00000000}}};
      single_block_test(8'h04, MODE_SHA_384, single_block, tc4_expected);


      // Two block test message.
      double_block_one = 1024'h61626364656667686263646566676869636465666768696A6465666768696A6B65666768696A6B6C666768696A6B6C6D6768696A6B6C6D6E68696A6B6C6D6E6F696A6B6C6D6E6F706A6B6C6D6E6F70716B6C6D6E6F7071726C6D6E6F707172736D6E6F70717273746E6F70717273747580000000000000000000000000000000;
      double_block_two = 1024'h0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000380;

      // SHA-512 two block digests and test.
      tc5_expected = 512'h4319017A2B706E69CD4B05938BAE5E890186BF199F30AA956EF8B71D2F810585D787D6764B20BDA2A26014470973692000EC057F37D14B8E06ADD5B50E671C72;
      tc6_expected = 512'h8E959B75DAE313DA8CF4F72814FC143F8F7779C6EB9F7FA17299AEADB6889018501D289E4900F7E4331B99DEC4B5433AC7D329EEB6DD26545E96E55B874BE909;
      double_block_test(8'h05, MODE_SHA_512, double_block_one, double_block_two, tc5_expected, tc6_expected);

      // SHA-512_224 two block digests and test.
      tc7_expected = 512'h9606CB2DB7823CE75FE35E2674A8F9EF1417ED9E89C412BB54EA29664586108625852563EED495096DEBAAE2F4737FD75319224B135486F8E6C0F55E700C35B3;
      tc8_expected = {224'h23FEC5BB94D60B23308192640B0C453335D664734FE40E7268674AF9, {9{32'h00000000}}};
      double_block_test(8'h06, MODE_SHA_512_224, double_block_one, double_block_two, tc7_expected, tc8_expected);

      // SHA-512_256 two block digests and test.
      tc9_expected = 512'h8DD99EB081311F8BCBBBC42CC7AFB288E8E9408730419D1E953FF7A2B194048DAE24175483C44C7C809B348E8E88E3ECBF2EA614CEED9C5B51807937F11867E1;
      tc10_expected = {256'h3928E184FB8690F840DA3988121D31BE65CB9D3EF83EE6146FEAC861E19B563A, {8{32'h00000000}}};
      double_block_test(8'h07, MODE_SHA_512_256, double_block_one, double_block_two, tc9_expected, tc10_expected);

      // SHA-384 two block digests and test.
      tc11_expected = 512'h2A7F1D895FD58E0BEAAE96D1A673C741015A2173796C1A88F6352CA156ACAFF7C662113E9EBB4D6417B61A85E2CCF0A937EB9A6660FEB5198F2EBE9A81E6A2C5;
      tc12_expected = {384'h09330C33F71147E83D192FC782CD1B4753111B173B3B05D22FA08086E3B0F712FCC7C71A557E2DB966C3E9FA91746039, {4{32'h00000000}}};
      double_block_test(8'h08, MODE_SHA_384, double_block_one, double_block_two, tc11_expected, tc12_expected);

      // Work factor test.
      work_factor_test();

      display_test_result();
      
      $display("   -- Testbench for sha512 done. --");
      $finish;
  end //sha512_test

endmodule