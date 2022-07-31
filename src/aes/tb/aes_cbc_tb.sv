//======================================================================
//
// aes_ctrl_tb.sv
// --------
// AES testbench for the AES AHb_lite interface controller.
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module aes_cbc_tb();

//----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG     = 0;

  parameter CLK_HALF_PERIOD = 1;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  // The DUT address map.
  parameter BASE_ADDR        = 32'h60000000;

  parameter ADDR_NAME0        = BASE_ADDR + 32'h00000000;
  parameter ADDR_NAME1        = BASE_ADDR + 32'h00000004;
  parameter ADDR_VERSION0     = BASE_ADDR + 32'h00000008;
  parameter ADDR_VERSION1     = BASE_ADDR + 32'h0000000c;

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
  parameter ADDR_KEY1        = BASE_ADDR + 32'h00000044;
  parameter ADDR_KEY2        = BASE_ADDR + 32'h00000048;
  parameter ADDR_KEY3        = BASE_ADDR + 32'h0000004c;
  parameter ADDR_KEY4        = BASE_ADDR + 32'h00000050;
  parameter ADDR_KEY5        = BASE_ADDR + 32'h00000054;
  parameter ADDR_KEY6        = BASE_ADDR + 32'h00000058;
  parameter ADDR_KEY7        = BASE_ADDR + 32'h0000005c;

  parameter ADDR_BLOCK0      = BASE_ADDR + 32'h00000080;
  parameter ADDR_BLOCK1      = BASE_ADDR + 32'h00000084;
  parameter ADDR_BLOCK2      = BASE_ADDR + 32'h00000088;
  parameter ADDR_BLOCK3      = BASE_ADDR + 32'h0000008c;

  parameter ADDR_IV0         = BASE_ADDR + 32'h00000110;
  parameter ADDR_IV1         = BASE_ADDR + 32'h00000114;
  parameter ADDR_IV2         = BASE_ADDR + 32'h00000118;
  parameter ADDR_IV3         = BASE_ADDR + 32'h0000011c;

  parameter ADDR_RESULT0     = BASE_ADDR + 32'h00000100;
  parameter ADDR_RESULT1     = BASE_ADDR + 32'h00000104;
  parameter ADDR_RESULT2     = BASE_ADDR + 32'h00000108;
  parameter ADDR_RESULT3     = BASE_ADDR + 32'h0000010c;

  parameter AES_128_BIT_KEY = 0;
  parameter AES_256_BIT_KEY = 1;

  parameter AES_DECIPHER = 1'b0;
  parameter AES_ENCIPHER = 1'b1;

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  parameter AHB_ADDR_WIDTH = 32;
  parameter AHB_DATA_WIDTH = 32;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0]  cycle_ctr;
  reg [63 : 0]  error_ctr;
  reg [63 : 0]  tc_ctr;
  reg [63 : 0]  temp_ctr;

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

  reg [31 : 0]  read_data;
  reg [127 : 0] result_data;
  reg [127 : 0] tmp;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  aes_ctrl #(
             .AHB_DATA_WIDTH(32),
             .AHB_ADDR_WIDTH(32),
             .BYPASS_HSEL(0)
            )
            dut (
             .clk(clk_tb),
             .reset_n(reset_n_tb),

             .haddr_i(hadrr_i_tb),
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

      read_single_word(ADDR_NAME0);
      name[31 : 0] = read_data;
      read_single_word(ADDR_NAME1);
      name[63 : 32] = read_data;
      read_single_word(ADDR_VERSION0);
      version[31 : 0] = read_data;
      read_single_word(ADDR_VERSION1);
      version[63 : 32] = read_data;

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
                  input [31 : 0] word);
    begin
      hsel_i_tb       = 1;
      hadrr_i_tb      = address;
      hwrite_i_tb     = 1;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 3'b010;
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
      write_single_word(ADDR_BLOCK0, block[127  :  96]);
      write_single_word(ADDR_BLOCK1, block[95   :  64]);
      write_single_word(ADDR_BLOCK2, block[63   :  32]);
      write_single_word(ADDR_BLOCK3, block[31   :   0]);
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
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 3'b010;
      #(CLK_PERIOD);
      
      hwdata_i_tb     = 0;
      hadrr_i_tb     = 'Z;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      read_data = hrdata_o_tb;
    end
  endtask // read_word

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
  // read_result()
  //
  // Read the result block in the dut.
  //----------------------------------------------------------------
  task read_result;
    begin
      read_single_word(ADDR_RESULT0);
      result_data[127 : 96] = read_data;
      read_single_word(ADDR_RESULT1);
      result_data[95  : 64] = read_data;
      read_single_word(ADDR_RESULT2);
      result_data[63  : 32] = read_data;
      read_single_word(ADDR_RESULT3);
      result_data[31  :  0] = read_data;
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
      write_single_word(ADDR_KEY0, key[255  : 224]);
      write_single_word(ADDR_KEY1, key[223  : 192]);
      write_single_word(ADDR_KEY2, key[191  : 160]);
      write_single_word(ADDR_KEY3, key[159  : 128]);
      write_single_word(ADDR_KEY4, key[127  :  96]);
      write_single_word(ADDR_KEY5, key[95   :  64]);
      write_single_word(ADDR_KEY6, key[63   :  32]);
      write_single_word(ADDR_KEY7, key[31   :   0]);

      if (key_length)
          write_single_word(ADDR_CONFIG, 8'h02);
      else
          write_single_word(ADDR_CONFIG, 8'h00);

      write_single_word(ADDR_CTRL, 8'h01);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(8 * CLK_PERIOD);
      wait_ready();
      
      // temp_ctr = 0;
      // while (temp_ctr < 100)
      //   begin
      //     #CLK_PERIOD;
      //     read_single_word(ADDR_STATUS);
      //     temp_ctr = temp_ctr + 1;
      //   end
    end
  endtask // init_key

  //----------------------------------------------------------------
  // write_IV()
  //
  // This task writes IV value for the CBC mode.
  //----------------------------------------------------------------
  task write_IV(input [127 : 0] IV);
    begin
      write_single_word(ADDR_IV0, IV[127  :  96]);
      write_single_word(ADDR_IV1, IV[95   :  64]);
      write_single_word(ADDR_IV2, IV[63   :  32]);
      write_single_word(ADDR_IV3, IV[31   :   0]);
    end
  endtask // write_IV



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
      write_IV(IV);
      write_block(block);

      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ encdec));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;
      
      // #(100 * CLK_PERIOD);

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);
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

      // first block
      write_IV(IV);
      write_block(block1);
      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ encdec));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** first block test processing time = %01d cycles", end_time);
      read_result();

      if (result_data == expected1)
        begin
          $display("*** TC %0d first block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d first block NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected1);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end


      // second block
      write_block(block2);
      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ encdec));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** second block test processing time = %01d cycles", end_time);
      read_result();

      if (result_data == expected2)
        begin
          $display("*** TC %0d second block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d second block NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected2);
          $display("Got:      0x%032x", result_data);
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
      write_IV(IV);

      // first block
      write_block(block1);      
      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ encdec));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** first block test processing time = %01d cycles", end_time);
      read_result();

      if (result_data == expected1)
        begin
          $display("*** TC %0d first block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d first block NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected1);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end


      // second block
      write_block(block2);
      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ encdec));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** second block test processing time = %01d cycles", end_time);
      read_result();

      if (result_data == expected2)
        begin
          $display("*** TC %0d second block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d second block NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected2);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end

      // second block
      write_block(block3);
      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ encdec));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** third block test processing time = %01d cycles", end_time);
      read_result();

      if (result_data == expected3)
        begin
          $display("*** TC %0d third block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d third block NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected3);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end

      // final block
      write_block(block4);

      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ encdec));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** final block test processing time = %01d cycles", end_time);
      read_result();

      if (result_data == expected4)
        begin
          $display("*** TC %0d final block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d final block NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected4);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // cbc_mode_quat_block_test

  //----------------------------------------------------------------
  // cbc_mode_sequential_quadratic_block_test()
  //
  // Perform CBC mode encryption and decryption quadratic block test.
  //----------------------------------------------------------------
  task cbc_mode_sequential_quadratic_block_test
                                (input [7 : 0]   tc_number,
                                  input [255 : 0] key,
                                  input           key_length,
                                  input [127 : 0] IV,
                                  input [127 : 0] block1,
                                  input [127 : 0] block2,
                                  input [127 : 0] block3,
                                  input [127 : 0] block4
                                  );
    reg [31  : 0] start_time;
    reg [31 : 0] end_time;
    reg encdec;
    
    begin
      $display("*** TC %0d CBC mode FOUR BLOCK SEQUENTIAL test started.", tc_number);
      tc_ctr = tc_ctr + 1;


      

      start_time = cycle_ctr;
      init_key(key, key_length);
      write_IV(IV);

      // first block
      $display("*** ENCRYPTION *** ");
      write_block(block1);      
      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ AES_ENCIPHER));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** first block encryption processing time = %01d cycles", end_time);
      read_result();

      tmp=result_data;
      $display("Plaintext:           0x%032x", block1);
      $display("Encrypted DATA:      0x%032x", result_data);


      $display("*** DECRYPTION *** ");
      write_block(tmp);      
      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ AES_DECIPHER));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** first block decryption processing time = %01d cycles", end_time);
      read_result();
      $display("Ciphertext:          0x%032x", tmp);
      $display("Decrypted DATA:      0x%032x", result_data);


      if (result_data == block1)
        begin
          $display("*** TC %0d first block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d first block NOT successful.", tc_number);
          $display("Expected: 0x%032x", block1);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end


      // second block
      $display("*** ENCRYPTION *** ");
      write_block(block2);      
      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ AES_ENCIPHER));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** second block encryption processing time = %01d cycles", end_time);
      read_result();

      tmp=result_data;
      $display("Plaintext:           0x%032x", block2);
      $display("Encrypted DATA:      0x%032x", result_data);


      $display("*** DECRYPTION *** ");
      write_block(tmp);      
      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ AES_DECIPHER));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** second block decryption processing time = %01d cycles", end_time);
      read_result();
      $display("Ciphertext:          0x%032x", tmp);
      $display("Decrypted DATA:      0x%032x", result_data);


      if (result_data == block2)
        begin
          $display("*** TC %0d second block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d second block NOT successful.", tc_number);
          $display("Expected: 0x%032x", block2);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end

      // third block
      $display("*** ENCRYPTION *** ");
      write_block(block3);      
      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ AES_ENCIPHER));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** third block encryption processing time = %01d cycles", end_time);
      read_result();

      tmp=result_data;
      $display("Plaintext:           0x%032x", block3);
      $display("Encrypted DATA:      0x%032x", result_data);


      $display("*** DECRYPTION *** ");
      write_block(tmp);      
      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ AES_DECIPHER));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** third block decryption processing time = %01d cycles", end_time);
      read_result();
      $display("Ciphertext:          0x%032x", tmp);
      $display("Decrypted DATA:      0x%032x", result_data);


      if (result_data == block3)
        begin
          $display("*** TC %0d third block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d third block NOT successful.", tc_number);
          $display("Expected: 0x%032x", block3);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end

      // final block
      $display("*** ENCRYPTION *** ");
      write_block(block4);      
      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ AES_ENCIPHER));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** final block encryption processing time = %01d cycles", end_time);
      read_result();

      tmp=result_data;
      $display("Plaintext:           0x%032x", block4);
      $display("Encrypted DATA:      0x%032x", result_data);


      $display("*** DECRYPTION *** ");
      write_block(tmp);      
      write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ AES_DECIPHER));
      write_single_word(ADDR_CTRL, 8'h02);
      
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      end_time = cycle_ctr - start_time;
      $display("*** final block decryption processing time = %01d cycles", end_time);
      read_result();
      $display("Ciphertext:          0x%032x", tmp);
      $display("Decrypted DATA:      0x%032x", result_data);


      if (result_data == block4)
        begin
          $display("*** TC %0d final block successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d final block NOT successful.", tc_number);
          $display("Expected: 0x%032x", block4);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end


    end
  endtask // cbc_mode_sequential_quadratic_block_test

  //----------------------------------------------------------------
  // cbc_mode_kat_vector_test()
  //
  // Perform CBC mode encryption or decryption vector test using the known answer vectors
  //----------------------------------------------------------------

  task cbc_mode_kat_vector_test(input [7 : 0]   tc_number,
                                  input           encdec,
                                  input           key_length,
                                  input [63  : 0] vector_cnt);
    reg [31  : 0] start_time;
    reg [31  : 0] end_time;
    reg [127 : 0] block;
    reg [127 : 0] expected;
    reg [255 : 0] key;
    reg [127 : 0] IV;

    string        line_read;
    string        tmp_str1;
    string        tmp_str2;

    int cyc_cnt;
    int fd_r;

    begin
      
      cyc_cnt = 0;
      fd_r = $fopen("/home/t-stevenlian/AHA_workspaces/aes_vector/Caliptra/src/aes/tb/CBCVarTxt256_clean.txt","r");
      if(fd_r) $display("file opened successfully!");

      $display("*** TC %0d CBC mode test started.", tc_number);
      if (encdec==0)
        $display("*** DECRYPTION *** ");
      else
        $display("*** ENCRYPTION *** ");

      start_time = cycle_ctr;

      while (cyc_cnt < (vector_cnt)) begin

        tc_ctr = tc_ctr + 1;

        // gets key and IV
        $fgets(line_read,fd_r);
        $fgets(line_read,fd_r);
        $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, key);
        $fgets(line_read,fd_r);
        $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, IV);
        // $display("*** key is: %h", key);
        // $display("*** IV is: %h", IV);

        // initialize key and IV
        init_key(key, key_length);
        write_IV(IV);

        // gets text input and expected output
        if (encdec==0)
        begin
          $fgets(line_read,fd_r);
          $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, expected);
          $fgets(line_read,fd_r);
          $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, block);
        end
        else
        begin
          $fgets(line_read,fd_r);
          $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, block);
          $fgets(line_read,fd_r);
          $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, expected);
        end
        // $display("*** block is: %h", block);
        // $display("*** expected is: %h", expected);

        // write block
        write_block(block);

        write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ encdec));
        write_single_word(ADDR_CTRL, 8'h02);
        
        #CLK_PERIOD;
        hsel_i_tb       = 0;

        #(CLK_PERIOD);
        wait_ready();
        read_result();

        if (result_data == expected)
          begin
            $display("*** TC %0d cycle %0d successful.", tc_number, cyc_cnt);
            $display("");
          end
        else
          begin
            $display("*** ERROR: TC %0d cycle %0d NOT successful.", tc_number, cyc_cnt);
            $display("Expected: 0x%032x", expected);
            $display("Got:      0x%032x", result_data);
            $display("");

            error_ctr = error_ctr + 1;
          end
        
        cyc_cnt = cyc_cnt + 1;

        // skips a line
        $fgets(line_read,fd_r);
      end 

      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);

      $fclose(fd_r);
      
    end
  endtask // cbc_mode_kat_vector_test

  //----------------------------------------------------------------
  // cbc_mode_mmt_vector_test()
  //
  // Perform CBC mode encryption or decryption test using multiblock message (10) vectors
  //----------------------------------------------------------------

  task cbc_mode_mmt_vector_test(input [7 : 0]   tc_number,
                                  input           encdec,
                                  input           key_length);
    reg [31  : 0] start_time;
    reg [31  : 0] end_time;
    reg [127 : 0] block;
    reg [127 : 0] expected;
    reg [1279: 0] block_all;
    reg [1279: 0] expected_all;
    reg [255 : 0] key;
    reg [127 : 0] IV;

    string        line_read;
    string        tmp_str1;
    string        tmp_str2;

    int cyc_cnt;
    int cnt_tmp;
    int fd_r;

    begin
      
      cyc_cnt = 0;
      // for some reason, $fopen only recognizes the absolute path
      // change it to your path before running!!
      fd_r = $fopen("/home/t-stevenlian/AHA_workspaces/aes_vector/Caliptra/src/aes/tb/CBCMMT256_clean.txt","r");
      if(fd_r) $display("file opened successfully!");

      $display("*** TC %0d CBC mode test started.", tc_number);
      if (encdec==0) begin
        $display("*** DECRYPTION *** ");
        // skips certain number of lines
        while (cnt_tmp <= 120) begin
          cnt_tmp = cnt_tmp + 1;
          $fgets(line_read,fd_r);
        end
      end
      else begin
        $display("*** ENCRYPTION *** ");
        while (cnt_tmp <= 58) begin
          cnt_tmp = cnt_tmp + 1;
          $fgets(line_read,fd_r);
        end
      end 
      
      // gets key and IV
      $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, key);
      $fgets(line_read,fd_r);
      $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, IV);
      // $display("*** key is: %h", key);
      // $display("*** IV is: %h", IV);

      // gets text input and expected output
      $fgets(line_read,fd_r);
      $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, block_all);
      $fgets(line_read,fd_r);
      $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, expected_all);
      // $display("*** block_all is: %h", block_all);
      // $display("*** expected_all is: %h", expected_all);

      start_time = cycle_ctr;
      // initialize key and IV
      init_key(key, key_length);
      write_IV(IV);

      while (cyc_cnt < 9) begin

        tc_ctr = tc_ctr + 1;

        block = block_all[1279:1152];
        block_all = block_all << 128;
        expected = expected_all[1279:1152];
        expected_all = expected_all << 128;

        // write block
        write_block(block);

        write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ encdec));
        write_single_word(ADDR_CTRL, 8'h02);
        
        #CLK_PERIOD;
        hsel_i_tb       = 0;

        #(CLK_PERIOD);
        wait_ready();
        read_result();

        if (result_data == expected)
          begin
            $display("*** TC %0d cycle %0d successful.", tc_number, cyc_cnt);
            $display("");
          end
        else
          begin
            $display("*** ERROR: TC %0d cycle %0d NOT successful.", tc_number, cyc_cnt);
            $display("Expected: 0x%032x", expected);
            $display("Got:      0x%032x", result_data);
            $display("");

            error_ctr = error_ctr + 1;
          end
        
        cyc_cnt = cyc_cnt + 1;

      end 

      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);

      $fclose(fd_r);
      
    end
  endtask // cbc_mode_mmt_vector_test

  //----------------------------------------------------------------
  // aes_cbc_test()
  //
  //
  // Main test task will perform complete test of AES.
  // Test vectors copied from the follwing documents.
  //
  // https://datatracker.ietf.org/doc/html/rfc3602
  // 
  //
  //----------------------------------------------------------------
  task aes_cbc_test;
    reg [255 : 0] nist_aes128_key0;
    

    reg [127 : 0] nist_IV0;

    reg [127 : 0] nist_plaintext0;

    reg [127 : 0] nist_plaintext1;

    reg [127 : 0] nist_plaintext2;

    reg [127 : 0] nist_plaintext3;

    reg [127 : 0] nist_ecb_128_enc_expected0;

    reg [127 : 0] nist_ecb_128_enc_expected1;

    reg [127 : 0] nist_ecb_128_enc_expected2;

    reg [127 : 0] nist_ecb_128_enc_expected3;

    reg [127 : 0] nist_ecb_256_enc_expected0;

    reg [127 : 0] nist_ecb_256_enc_expected1;

    reg [127 : 0] nist_ecb_256_enc_expected2;

    reg [127 : 0] nist_ecb_256_enc_expected3;

    begin
      nist_aes128_key0           = 256'hc286696d887c9aa0611bbb3e2025a45a00000000000000000000000000000000;
      nist_IV0                   = 128'h562e17996d093d28ddb3ba695a2e6f58;
      nist_plaintext0            = 128'h000102030405060708090a0b0c0d0e0f;
      nist_ecb_128_enc_expected0 = 128'hd296cd94c2cccf8a3a863028b5e1dc0a;

      $display("CBC 128 bit key single block tests");
      $display("---------------------");
      cbc_mode_single_block_test(8'h01, AES_ENCIPHER, nist_aes128_key0, AES_128_BIT_KEY, nist_IV0,
                                 nist_plaintext0, nist_ecb_128_enc_expected0);
      $display("---------------------");
      cbc_mode_single_block_test(8'h01, AES_DECIPHER, nist_aes128_key0, AES_128_BIT_KEY, nist_IV0,
                                 nist_ecb_128_enc_expected0, nist_plaintext0);

      $display("---------------------");
      
      nist_aes128_key0           = 256'h56e47a38c5598974bc46903dba29034900000000000000000000000000000000;
      nist_IV0                   = 128'h8ce82eefbea0da3c44699ed7db51b7d9;
      nist_plaintext0            = 128'ha0a1a2a3a4a5a6a7a8a9aaabacadaeaf;
      nist_ecb_128_enc_expected0 = 128'hc30e32ffedc0774e6aff6af0869f71aa;

      cbc_mode_single_block_test(8'h02, AES_ENCIPHER, nist_aes128_key0, AES_128_BIT_KEY, nist_IV0,
                                 nist_plaintext0, nist_ecb_128_enc_expected0);
      $display("---------------------");
      cbc_mode_single_block_test(8'h03, AES_DECIPHER, nist_aes128_key0, AES_128_BIT_KEY, nist_IV0,
                                 nist_ecb_128_enc_expected0, nist_plaintext0);
      $display("---------------------");
      
      nist_aes128_key0           = 256'hc286696d887c9aa0611bbb3e2025a45a00000000000000000000000000000000;
      nist_IV0                   = 128'h562e17996d093d28ddb3ba695a2e6f58;
      nist_plaintext0            = 128'h000102030405060708090a0b0c0d0e0f;
      nist_plaintext1            = 128'h101112131415161718191a1b1c1d1e1f;
      nist_ecb_128_enc_expected0 = 128'hd296cd94c2cccf8a3a863028b5e1dc0a;
      nist_ecb_128_enc_expected1 = 128'h7586602d253cfff91b8266bea6d61ab1;
      $display("---------------------");
      cbc_mode_double_block_test(8'h04, AES_ENCIPHER, nist_aes128_key0, AES_128_BIT_KEY, nist_IV0,
                                 nist_plaintext0,
                                 nist_plaintext1,
                                 nist_ecb_128_enc_expected0,
                                 nist_ecb_128_enc_expected1);

      $display("---------------------");
      cbc_mode_double_block_test(8'h05, AES_DECIPHER, nist_aes128_key0, AES_128_BIT_KEY, nist_IV0,
                                 nist_ecb_128_enc_expected0,
                                 nist_ecb_128_enc_expected1,
                                 nist_plaintext0,
                                 nist_plaintext1);
      $display("---------------------");      
      nist_aes128_key0           = 256'h56e47a38c5598974bc46903dba29034900000000000000000000000000000000;
      nist_IV0                   = 128'h8ce82eefbea0da3c44699ed7db51b7d9;
      nist_plaintext0            = 128'ha0a1a2a3a4a5a6a7a8a9aaabacadaeaf;
      nist_plaintext1            = 128'hb0b1b2b3b4b5b6b7b8b9babbbcbdbebf;
      nist_plaintext2            = 128'hc0c1c2c3c4c5c6c7c8c9cacbcccdcecf;
      nist_plaintext3            = 128'hd0d1d2d3d4d5d6d7d8d9dadbdcdddedf;
      nist_ecb_128_enc_expected0 = 128'hc30e32ffedc0774e6aff6af0869f71aa;
      nist_ecb_128_enc_expected1 = 128'h0f3af07a9a31a9c684db207eb0ef8e4e;
      nist_ecb_128_enc_expected2 = 128'h35907aa632c3ffdf868bb7b29d3d46ad;
      nist_ecb_128_enc_expected3 = 128'h83ce9f9a102ee99d49a53e87f4c3da55;

      cbc_mode_quadratic_block_test(8'h06, AES_ENCIPHER, nist_aes128_key0, AES_128_BIT_KEY, nist_IV0,
                                 nist_plaintext0,
                                 nist_plaintext1,
                                 nist_plaintext2,
                                 nist_plaintext3,
                                 nist_ecb_128_enc_expected0,
                                 nist_ecb_128_enc_expected1,
                                 nist_ecb_128_enc_expected2,
                                 nist_ecb_128_enc_expected3);
      $display("---------------------");
      cbc_mode_quadratic_block_test(8'h07, AES_DECIPHER, nist_aes128_key0, AES_128_BIT_KEY, nist_IV0,
                                 nist_ecb_128_enc_expected0,
                                 nist_ecb_128_enc_expected1,
                                 nist_ecb_128_enc_expected2,
                                 nist_ecb_128_enc_expected3,
                                 nist_plaintext0,
                                 nist_plaintext1,
                                 nist_plaintext2,
                                 nist_plaintext3);

      $display("---------------------");
      cbc_mode_sequential_quadratic_block_test(8'h08, nist_aes128_key0, AES_128_BIT_KEY, nist_IV0,
                                 nist_ecb_128_enc_expected0,
                                 nist_ecb_128_enc_expected1,
                                 nist_ecb_128_enc_expected2,
                                 nist_ecb_128_enc_expected3);                         
      $display("---------------------");

      nist_aes128_key0           = 256'h603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4;
      nist_IV0                   = 128'h000102030405060708090A0B0C0D0E0F;
      nist_plaintext0            = 128'h6bc1bee22e409f96e93d7e117393172a;
      nist_ecb_128_enc_expected0 = 128'hf58c4c04d6e5f1ba779eabfb5f7bfbd6;

      $display("CBC 256 bit key single block tests");
      
      cbc_mode_single_block_test(8'h01, AES_ENCIPHER, nist_aes128_key0, AES_256_BIT_KEY, nist_IV0,
                                 nist_plaintext0, nist_ecb_128_enc_expected0);

      $display("---------------------");

      $display("CBC 256 bit key Known Answer Vector 128-block encipher tests");
      
      cbc_mode_kat_vector_test(8'h01, AES_ENCIPHER, AES_256_BIT_KEY, 128);

      $display("---------------------");

      $display("CBC 256 bit key Known Answer Vector 128-block decipher tests");
      
      cbc_mode_kat_vector_test(8'h01, AES_DECIPHER, AES_256_BIT_KEY, 128);

      $display("---------------------");

      $display("CBC 256 bit key Multiblock Message Vector encipher Test");
      
      cbc_mode_mmt_vector_test(8'h01, AES_ENCIPHER, AES_256_BIT_KEY);

      $display("---------------------");

    end
  endtask // aes_cbc_test

  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -= Testbench for AES CBC started =-");
      $display("    ==============================");
      $display("");

      init_sim();
      reset_dut();

      check_name_version();

      aes_cbc_test();

      display_test_results();
      
      $display("");
      $display("*** AES simulation done. ***");
      $finish;
    end // main

endmodule // aes_tb