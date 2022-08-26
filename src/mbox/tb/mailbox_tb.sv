//======================================================================
//
// aes_ctrl_tb.sv
// --------
// AES testbench for the AES AHb_lite interface controller.
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module mailbox_tb();

//----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG     = 0;

  parameter CLK_HALF_PERIOD = 1;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  // The DUT address map
  parameter DCCM_SADR             = 32'hf0040000;

  parameter MBOX_ADDR_BASE        = 32'h30020000;
  parameter MBOX_ADDR_LOCK        = MBOX_ADDR_BASE;
  parameter MBOX_ADDR_CMD         = MBOX_ADDR_BASE + 32'h00000008;
  parameter MBOX_ADDR_DLEN        = MBOX_ADDR_BASE + 32'h0000000C;
  parameter MBOX_ADDR_DATAIN      = MBOX_ADDR_BASE + 32'h00000010;
  parameter MBOX_ADDR_DATAOUT     = MBOX_ADDR_BASE + 32'h00000014;
  parameter MBOX_ADDR_EXECUTE     = MBOX_ADDR_BASE + 32'h00000018;
  
  parameter MBOX_DLEN_VAL         = 32'h0000001C;

  parameter AHB_ADDR_WIDTH = 32;
  parameter AHB_DATA_WIDTH = 32;
  parameter APB_ADDR_WIDTH = 32;
  parameter APB_DATA_WIDTH = 32;
  parameter APB_USER_WIDTH = 32;

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0]  cycle_ctr;
  reg [63 : 0]  error_ctr;
  reg [63 : 0]  tc_ctr;
  reg [63 : 0]  temp_ctr;

  reg           clk_tb;
  reg           cptra_pwrgood_tb;
  reg           cptra_rst_b_tb;

  reg [APB_ADDR_WIDTH-1:0]     paddr_i_tb;
  reg                          psel_i_tb;
  reg                          penable_i_tb;
  reg                          pwrite_i_tb;
  reg [APB_DATA_WIDTH-1:0]     pwdata_i_tb;
  reg [APB_USER_WIDTH-1:0]     pauser_i_tb;

  reg [AHB_ADDR_WIDTH-1:0]  haddr_i_tb;
  reg [AHB_DATA_WIDTH-1:0]  hwdata_i_tb;
  reg           hsel_i_tb;
  reg           hwrite_i_tb; 
  reg           hmastlock_i_tb;
  reg           hready_i_tb;
  reg [1:0]     htrans_i_tb;
  reg [3:0]     hprot_i_tb;
  reg [2:0]     hburst_i_tb;
  reg [2:0]     hsize_i_tb;

  wire                         pready_o_tb;
  wire [APB_DATA_WIDTH-1:0]    prdata_o_tb;
  wire                         pslverr_o_tb;

  wire          hresp_o_tb;
  wire          hreadyout_o_tb;
  wire [AHB_DATA_WIDTH-1:0] hrdata_o_tb;

  wire cptra_uc_rst_b_tb;

  reg [31 : 0]  read_data;
  reg [127 : 0] result_data;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  mbox_top #(
             .AHB_DATA_WIDTH(32),
             .AHB_ADDR_WIDTH(32),
             .APB_USER_WIDTH(32),
             .APB_ADDR_WIDTH(32),
             .APB_DATA_WIDTH(32)
            )
            dut (
             .clk(clk_tb),

             .cptra_pwrgood(cptra_pwrgood_tb),
             .cptra_rst_b(cptra_rst_b_tb),

             .paddr_i(paddr_i_tb),
             .psel_i(psel_i_tb),
             .penable_i(penable_i_tb),
             .pwrite_i(pwrite_i_tb),
             .pwdata_i(pwdata_i_tb),
             .pauser_i(pauser_i_tb),
             .pready_o(pready_o_tb),
             .prdata_o(prdata_o_tb),
             .pslverr_o(pslverr_o_tb),

             .haddr_i(haddr_i_tb),
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
             .hrdata_o(hrdata_o_tb),

             .cptra_uc_rst_b(cptra_uc_rst_b_tb)
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
      cptra_rst_b_tb = 0;

      #(2 * CLK_PERIOD);
      cptra_rst_b_tb = 1;
      $display("");
      #(10 * CLK_PERIOD);
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
      temp_ctr      = 0;
      result_data   = 0;

      clk_tb        = 0;
      cptra_pwrgood_tb = 1;
      cptra_rst_b_tb    = 0;

      haddr_i_tb      = 'Z;
      hwdata_i_tb     = 'Z;
      hsel_i_tb       = 0;
      hwrite_i_tb     = 0;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 3'b011;

      paddr_i_tb      = 'Z;
      psel_i_tb       = 0;
      penable_i_tb    = 0;
      pwrite_i_tb     = 0;
      pwdata_i_tb     = 0;
      pauser_i_tb     = 0;

    end
  endtask // init_sim

  //----------------------------------------------------------------
  // write_single_word_ahb()
  //
  // Write the given word to the DUT using the AHB-lite interface.
  //----------------------------------------------------------------
  task write_single_word_ahb(input [31 : 0]  address,
                  input [31 : 0] word);
    begin
      hsel_i_tb       = 1;
      haddr_i_tb      = address;
      hwrite_i_tb     = 1;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 3'b010;

      paddr_i_tb      = 'Z;
      psel_i_tb       = 0;
      penable_i_tb    = 0;
      pwrite_i_tb     = 0;
      pwdata_i_tb     = 0;
      pauser_i_tb     = 0;

      #(CLK_PERIOD);

      haddr_i_tb      = 'Z;
      hwdata_i_tb     = word;
      hwrite_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
    end
  endtask // write_single_word_ahb

  //----------------------------------------------------------------
  // write_single_word_apb()
  //
  // Write the given word to the DUT using the AHB-lite interface.
  //----------------------------------------------------------------
  task write_single_word_apb(input [31 : 0]  address,
                  input [31 : 0] word);
    begin
      hsel_i_tb       = 0;
      haddr_i_tb      = 'Z;
      hwrite_i_tb     = 0;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 0;

      paddr_i_tb      = address;
      psel_i_tb       = 1;
      penable_i_tb    = 0;
      pwrite_i_tb     = 1;
      pwdata_i_tb     = word;
      pauser_i_tb     = 0;

      #(CLK_PERIOD);
      penable_i_tb    = 1;

      #(CLK_PERIOD);
      penable_i_tb    = 0;
      psel_i_tb       = 0;
    end
  endtask // write_single_word_apb



  //----------------------------------------------------------------
  // write_block_ahb()
  //
  // Write the given block to the dut.
  //----------------------------------------------------------------
  task write_block_ahb(input [127 : 0] block);
    begin
      write_single_word_ahb(MBOX_ADDR_DATAIN, block[127  :  96]);
      write_single_word_ahb(MBOX_ADDR_DATAIN, block[95   :  64]);
      write_single_word_ahb(MBOX_ADDR_DATAIN, block[63   :  32]);
      write_single_word_ahb(MBOX_ADDR_DATAIN, block[31   :   0]);
    end
  endtask // write_block_ahb

  //----------------------------------------------------------------
  // write_block_apb()
  //
  // Write the given block to the dut.
  //----------------------------------------------------------------
  task write_block_apb(input [127 : 0] block);
    begin
      write_single_word_apb(MBOX_ADDR_DATAIN, block[127  :  96]);
      write_single_word_apb(MBOX_ADDR_DATAIN, block[95   :  64]);
      write_single_word_apb(MBOX_ADDR_DATAIN, block[63   :  32]);
      write_single_word_apb(MBOX_ADDR_DATAIN, block[31   :   0]);
    end
  endtask // write_block_apb


  //----------------------------------------------------------------
  // read_word()
  //
  // Read a data word from the given address in the DUT.
  // the word read will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_single_word_ahb(input [31 : 0]  address);
    begin
      hsel_i_tb       = 1;
      haddr_i_tb      = address;
      hwrite_i_tb     = 0;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 3'b010;

      paddr_i_tb      = 'Z;
      psel_i_tb       = 0;
      penable_i_tb    = 0;
      pwrite_i_tb     = 0;
      pwdata_i_tb     = 0;
      pauser_i_tb     = 0;

      #(CLK_PERIOD);
      
      hwdata_i_tb     = 0;
      haddr_i_tb     = 'Z;
      htrans_i_tb     = AHB_HTRANS_IDLE;

      // #(CLK_PERIOD);
      read_data = hrdata_o_tb;
    end
  endtask // read_single_word_ahb

  task read_single_word_apb(input [31 : 0]  address);
    begin
      hsel_i_tb       = 0;
      haddr_i_tb      = 'Z;
      hwrite_i_tb     = 0;
      hmastlock_i_tb  = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hprot_i_tb      = 0;
      hburst_i_tb     = 0;
      hsize_i_tb      = 0;

      paddr_i_tb      = address;
      psel_i_tb       = 1;
      penable_i_tb    = 0;
      pwrite_i_tb     = 0;
      pwdata_i_tb     = 0;
      pauser_i_tb     = 0;

      #(CLK_PERIOD);
      penable_i_tb    = 1;
      #(0.5 * CLK_PERIOD);
      read_data = prdata_o_tb;
      #(0.5 * CLK_PERIOD);

      #(2 * CLK_PERIOD);
      psel_i_tb       = 0;
      penable_i_tb    = 0;

    end
  endtask // read_single_word_ahb

  //----------------------------------------------------------------
  // read_result_ahb()
  //
  // Read the result block in the dut.
  //----------------------------------------------------------------
  task read_result_ahb;
    begin
      read_single_word_ahb(MBOX_ADDR_DATAOUT);
      result_data[127 : 96] = read_data;
      read_single_word_ahb(MBOX_ADDR_DATAOUT);
      result_data[95  : 64] = read_data;
      read_single_word_ahb(MBOX_ADDR_DATAOUT);
      result_data[63  : 32] = read_data;
      read_single_word_ahb(MBOX_ADDR_DATAOUT);
      result_data[31  :  0] = read_data;
    end
  endtask // read_result_ahb

  //----------------------------------------------------------------
  // read_result_apb()
  //
  // Read the result block in the dut.
  //----------------------------------------------------------------
  task read_result_apb;
    begin
      read_single_word_apb(MBOX_ADDR_DATAOUT);
      result_data[127 : 96] = read_data;
      read_single_word_apb(MBOX_ADDR_DATAOUT);
      result_data[95  : 64] = read_data;
      read_single_word_apb(MBOX_ADDR_DATAOUT);
      result_data[63  : 32] = read_data;
      read_single_word_apb(MBOX_ADDR_DATAOUT);
      result_data[31  :  0] = read_data;
    end
  endtask // read_result_apb

  //----------------------------------------------------------------
  // wait_unlock()
  //
  // wait for the mailbox to unlock before send in anything
  //----------------------------------------------------------------
  task wait_unlock;
    begin
      read_data = 32'h00000001;
      #(CLK_PERIOD);

      while (read_data != 0)
        begin
          read_single_word_ahb(MBOX_ADDR_LOCK);
          read_data = read_data & 32'h00000001;
        end
    end
  endtask // wait_unlock

  //----------------------------------------------------------------
  // mbox_ahb_test()
  //
  // mailbox ahb test for single block
  //----------------------------------------------------------------
  task mbox_ahb_test (input [7 : 0]   tc_number,
                      input [127 : 0] block
                      );
    reg [31  : 0] start_time;
    reg [31 : 0] end_time;
    
    begin
      $display("*** TC %0d mailbox test started.", tc_number);
      tc_ctr = tc_ctr + 1;
      start_time = cycle_ctr;

      // poll for lock register
      wait_unlock();

      //write to MBOX_ADDR_CMD
      write_single_word_ahb(MBOX_ADDR_CMD, 32'hDEADBEEF);

      // write to MBOX_ADDR_DLEN
      write_single_word_ahb(MBOX_ADDR_DLEN, 32'h00000010);

      // write a block in
      write_block_ahb(block);
      #(CLK_PERIOD);
      
      // execute
      write_single_word_ahb(MBOX_ADDR_EXECUTE, 32'h00000001);
      #(20 * CLK_PERIOD);

      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);
      read_result_ahb();

      // reset excecute
      write_single_word_apb(MBOX_ADDR_EXECUTE, 32'h00000000);

      if (result_data == block)
        begin
          $display("*** TC %0d successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d NOT successful.", tc_number);
          $display("Expected: 0x%032x", block);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // mbox_ahb_test

  //----------------------------------------------------------------
  // mbox_apb_test()
  //
  // mailbox apb test for single block
  //----------------------------------------------------------------
  task mbox_apb_test (input [7 : 0]   tc_number,
                      input [127 : 0] block
                      );
    reg [31  : 0] start_time;
    reg [31 : 0] end_time;
    
    begin
      $display("*** TC %0d mailbox test started.", tc_number);
      tc_ctr = tc_ctr + 1;
      start_time = cycle_ctr;

      // poll for lock register
      wait_unlock();

      //write to MBOX_ADDR_CMD
      write_single_word_apb(MBOX_ADDR_CMD, 32'hDEADBEEF);

      // write to MBOX_ADDR_DLEN
      write_single_word_apb(MBOX_ADDR_DLEN, 32'h00000010);

      // write a block in
      write_block_apb(block);
      #(CLK_PERIOD);
      
      // execute
      write_single_word_apb(MBOX_ADDR_EXECUTE, 32'h00000001);
      #(20 * CLK_PERIOD);

      // wait_ready();

      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);
      read_result_apb();

      // reset excecute
      write_single_word_apb(MBOX_ADDR_EXECUTE, 32'h00000000);

      if (result_data == block)
        begin
          $display("*** TC %0d successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d NOT successful.", tc_number);
          $display("Expected: 0x%032x", block);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // mbox_apb_test

  //----------------------------------------------------------------
  // mbox_test()
  //----------------------------------------------------------------
  task mbox_test;
    reg [127 : 0] ahb_message_1;
    reg [127 : 0] apb_message_1;

    begin
      ahb_message_1 = 128'h11111111222222223333333344444444;

      apb_message_1 = 128'h66666666777777778888888899999999;


      // $display("mailbox ahb test");
      // $display("---------------------");
      // mbox_ahb_test(8'h01, ahb_message_1);

      $display("mailbox apb test");
      $display("---------------------");
      mbox_apb_test(8'h01, apb_message_1);


    end
  endtask // mbox_test


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

      // check_name_version();

      mbox_test();

      display_test_results();
      
      $display("");
      $display("*** AES simulation done. ***");
      $finish;
    end // main

endmodule // aes_tb