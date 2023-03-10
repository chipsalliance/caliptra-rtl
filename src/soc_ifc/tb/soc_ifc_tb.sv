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
// soc_ifc_tb.sv
// --------
// soc_ifc testbench for the soc_ifc AHb_lite interface controller.
//
// This Testbench no longer works
// Probably should be deprecated and utilize UVMF environment only
//======================================================================

/*
`define PRINT_TESTNAME(_SOC_IFC_TESTNAME) \ 
    string tmpstr = `"_SOC_IFC_TESTNAME`";
    $display(`"Executing test: _SOC_IFC_TESTNAME`"); 
    $display({{tmpstr.len(){`"-`"}});
//----------------------------------------------------------------
*/


module soc_ifc_tb
  import soc_ifc_pkg::*;
  import soc_ifc_tb_pkg::*;
  ();

  // Strings for plusargs
  string soc_ifc_testname; 
  string socreg_method_name = ""; 
  string security_state_testname; 


  enum logic {DEBUG_UNLOCKED = 1'b0, DEBUG_LOCKED = 1'b1} debug_state_e;

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

  parameter MBOX_UDS_ADDR         = 32'h3003_0200;
  parameter MBOX_FE_ADDR          = 32'h3003_0230;
  parameter MBOX_FUSE_DONE_ADDR   = 32'h3003_00ac;

  parameter AHB_ADDR_WIDTH = 18;
  parameter AHB_DATA_WIDTH = 32;
  parameter APB_ADDR_WIDTH = 18;
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
  reg           hready_i_tb;
  reg [1:0]     htrans_i_tb;
  reg [2:0]     hsize_i_tb;

  wire                         pready_o_tb;
  wire [APB_DATA_WIDTH-1:0]    prdata_o_tb;
  wire                         pslverr_o_tb;

  wire          hresp_o_tb;
  wire          hreadyout_o_tb;
  wire [AHB_DATA_WIDTH-1:0] hrdata_o_tb;

  wire cptra_noncore_rst_b_tb;
  wire cptra_uc_rst_b_tb;

  reg [127 : 0] result_data;
  logic ready_for_fuses;

  //SRAM interface for mbox
  logic mbox_sram_cs;
  logic mbox_sram_we;
  logic [MBOX_ADDR_W-1:0] mbox_sram_addr;
  logic [MBOX_DATA_W-1:0] mbox_sram_wdata;
  logic [MBOX_DATA_W-1:0] mbox_sram_rdata;

  logic [0:11][31:0]          cptra_uds_tb;
  logic [0:31][31:0]          cptra_fe_tb;

  //mailbox sram gasket
  mbox_sram_req_t mbox_sram_req;
  mbox_sram_resp_t mbox_sram_resp;


  //MH. Initialize to default device lifecycle later rather than TIE OFF
  security_state_t security_state, tmp_ss;  // '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED};

  always_comb begin
    mbox_sram_cs = mbox_sram_req.cs;
    mbox_sram_we = mbox_sram_req.we;
    mbox_sram_addr = mbox_sram_req.addr;
    mbox_sram_wdata = mbox_sram_req.wdata;
    mbox_sram_resp.rdata = mbox_sram_rdata;
  end

  assign hready_i_tb = hreadyout_o_tb;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  soc_ifc_top #(
             .AHB_DATA_WIDTH(32),
             .AHB_ADDR_WIDTH(18),
             .APB_USER_WIDTH(32),
             .APB_ADDR_WIDTH(18),
             .APB_DATA_WIDTH(32)
            )
            dut (
             .clk(clk_tb),
             .clk_cg(clk_tb),
             .soc_ifc_clk_cg(clk_tb),

             .cptra_pwrgood(cptra_pwrgood_tb),
             .cptra_rst_b(cptra_rst_b_tb),

             .ready_for_fuses(ready_for_fuses),
             .ready_for_fw_push(ready_for_fw_push),
             .ready_for_runtime(),

             .mailbox_data_avail(),
             .mailbox_flow_done(),

             .security_state(security_state),

             .generic_input_wires('x),
             .BootFSM_BrkPoint(1'b0), // TODO
             .generic_output_wires(),

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
             .hready_i(hready_i_tb),
             .htrans_i(htrans_i_tb),
             .hsize_i(hsize_i_tb),

             .hresp_o(hresp_o_tb),
             .hreadyout_o(hreadyout_o_tb),
             .hrdata_o(hrdata_o_tb),

             .cptra_error_fatal(),
             .cptra_error_non_fatal(),
             .trng_req(),

             .soc_ifc_error_intr(),
             .soc_ifc_notif_intr(),
             .sha_error_intr(),
             .sha_notif_intr(),

             .mbox_sram_req(mbox_sram_req),
             .mbox_sram_resp(mbox_sram_resp),

             .clear_obf_secrets(),
             .scan_mode_f(1'b0),
             .cptra_obf_key('0),
             .cptra_obf_key_reg(),
             .obf_field_entropy(),
             .obf_uds_seed(),

             .nmi_vector(),

             .iccm_lock(),
             .iccm_axs_blocked(),

             .cptra_noncore_rst_b(cptra_noncore_rst_b_tb),
             .cptra_uc_rst_b(cptra_uc_rst_b_tb),
             .clk_gating_en(),

             .cptra_uncore_dmi_reg_en     ( 1'h0),
             .cptra_uncore_dmi_reg_wr_en  ( 1'h0),
             .cptra_uncore_dmi_reg_rdata  (     ),
             .cptra_uncore_dmi_reg_addr   ( 7'h0),
             .cptra_uncore_dmi_reg_wdata  (32'h0)

            );

  //SRAM for mbox
  caliptra_sram 
  #(
    .DATA_WIDTH(32),
    .DEPTH('h8000)
  )
  mbox_ram1
  (
    .clk_i(clk_tb),
    
    .cs_i(mbox_sram_cs),
    .we_i(mbox_sram_we),
    .addr_i(mbox_sram_addr),
    .wdata_i(mbox_sram_wdata),
    
    .rdata_o(mbox_sram_rdata)
  );


  RegScoreboard sb = new();  // scoreboard for checking register operations 

  SocRegisters socregs = new(); // allows for initialization of soc-registers 



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
      cptra_pwrgood_tb = '0;
      cptra_rst_b_tb = 0;

      repeat (5) @(posedge clk_tb);

      cptra_pwrgood_tb = 1;

      repeat (5) @(posedge clk_tb);
      
      cptra_rst_b_tb = 1;
      $display("");
    end
  endtask // reset_dut


  //----------------------------------------------------------------
  // warm_reset_dut()
  //
  // Warm reset DUT into a well known state.
  //----------------------------------------------------------------
  task warm_reset_dut;
    begin
      $display("*** Perform warm reset. ***");
      cptra_rst_b_tb = 0;

      repeat (5) @(posedge clk_tb);
      
      cptra_rst_b_tb = 1;
      $display("** Warm reset complete **");
    end
  endtask // reset_dut

  //----------------------------------------------------------------
  // load_fuses()
  //
  // Load Fuses (required to get other blocks out of reset)
  //----------------------------------------------------------------
  task load_fuses;
    begin
      for (int i = 0; i < 12; i++)begin
        write_single_word_apb(MBOX_UDS_ADDR + i*4, cptra_uds_tb[i]);
      end
      
      $display ("SoC: Writing obfuscated Field Entropy to fuse bank\n");
      for (int i = 0; i < 32; i++)begin
          write_single_word_apb(MBOX_FE_ADDR + i*4, cptra_fe_tb[i]);
      end
      
      $display ("SoC: Writing fuse done register\n");
      //set fuse done
      write_single_word_apb(MBOX_FUSE_DONE_ADDR, 32'h00000001); 
      
      /*
      wait (ready_for_fw_push == 1'b1);
        
      repeat (5) @(posedge clk_tb);
      // poll for lock register
      wait_unlock_apb();
      repeat (5) @(posedge clk_tb);
        */
    end
  endtask

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
      result_data   = 0;

      clk_tb        = 0;
      cptra_pwrgood_tb = 0;
      cptra_rst_b_tb    = 0;

      haddr_i_tb      = 'Z;
      hwdata_i_tb     = 'Z;
      hsel_i_tb       = 0;
      hwrite_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hsize_i_tb      = 3'b011;

      paddr_i_tb      = 'Z;
      psel_i_tb       = 0;
      penable_i_tb    = 0;
      pwrite_i_tb     = 0;
      pwdata_i_tb     = 0;
      pauser_i_tb     = 0;

      //Key for UDS 
      cptra_uds_tb = 384'he4046d05385ab789c6a72866e08350f93f583e2a005ca0faecc32b5cfc323d461c76c107307654db5566a5bd693e227c;

      //Key for FE
      cptra_fe_tb = {256'hb32e2b171b63827034ebb0d1909f7ef1d51c5f82c1bb9bc26bc4ac4dccdee835,
                     256'h7dca6154c2510ae1c87b1b422b02b621bb06cac280023894fcff3406af08ee9b,
                     256'he1dd72419beccddff77c722d992cdcc87e9c7486f56ab406ea608d8c6aeb060c,
                     256'h64cf2785ad1a159147567e39e303370da445247526d95942bf4d7e88057178b0};

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
      hsel_i_tb       <= 1;
      haddr_i_tb      <= address;
      hwrite_i_tb     <= 1;
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
  endtask // write_single_word_ahb

  //----------------------------------------------------------------
  // write_single_word_apb()
  //
  // Write the given word to the DUT using the AHB-lite interface.
  //----------------------------------------------------------------
  task write_single_word_apb(input [31 : 0] address,
                             input [31 : 0] word);
    begin
      paddr_i_tb      <= address;
      psel_i_tb       <= 1;
      penable_i_tb    <= 0;
      pwrite_i_tb     <= 1;
      pwdata_i_tb     <= word;
      pauser_i_tb     <= '1;
      wait(pready_o_tb == 1'b1);
      
      @(posedge clk_tb);
      penable_i_tb    <= 1;
      wait(pready_o_tb == 1'b1);

      @(posedge clk_tb);
      psel_i_tb       <= 0;
      penable_i_tb    <= 0;
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
      hsel_i_tb       <= 1;
      haddr_i_tb      <= address;
      hwrite_i_tb     <= 0;
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
  endtask // read_single_word_ahb

  task read_single_word_apb(input [31 : 0] address);
    begin
      paddr_i_tb      <= address;
      psel_i_tb       <= 1;
      penable_i_tb    <= 0;
      pwrite_i_tb     <= 0;
      pwdata_i_tb     <= 0;
      pauser_i_tb     <= '1;
      wait(pready_o_tb == 1'b1);

      @(posedge clk_tb);
      penable_i_tb    <= 1;
      wait(pready_o_tb == 1'b1);

      @(posedge clk_tb);
      psel_i_tb       <= 0;
      penable_i_tb    <= 0;
    end
  endtask // read_single_word_ahb

  //----------------------------------------------------------------
  // read_result_ahb()
  //
  // Read the result block in the dut.
  //----------------------------------------------------------------
  task read_result_ahb(output [127:0]  r_data);
    begin
      
      read_single_word_ahb(MBOX_ADDR_DATAOUT);
      r_data[127 : 96] = hrdata_o_tb;
      read_single_word_ahb(MBOX_ADDR_DATAOUT);
      r_data[95  : 64] = hrdata_o_tb;
      read_single_word_ahb(MBOX_ADDR_DATAOUT);
      r_data[63  : 32] = hrdata_o_tb;
      read_single_word_ahb(MBOX_ADDR_DATAOUT);
      r_data[31  :  0] = hrdata_o_tb;
    end
  endtask // read_result_ahb

  //----------------------------------------------------------------
  // read_result_apb()
  //
  // Read the result block in the dut.
  //----------------------------------------------------------------
  task read_result_apb(output [127:0]  r_data);
    begin

      read_single_word_apb(MBOX_ADDR_DATAOUT);
      r_data[127:96] = prdata_o_tb;
      read_single_word_apb(MBOX_ADDR_DATAOUT);
      r_data[ 95:64] = prdata_o_tb;
      read_single_word_apb(MBOX_ADDR_DATAOUT);
      r_data[ 63:32] = prdata_o_tb;
      read_single_word_apb(MBOX_ADDR_DATAOUT);
      r_data[ 31: 0] = prdata_o_tb;
  
    end
  endtask // read_result_apb

  //----------------------------------------------------------------
  // wait_unlock_ahb()
  //
  // wait for the mailbox to unlock before send in anything
  //----------------------------------------------------------------
  task wait_unlock_ahb;
    begin
      read_single_word_ahb(MBOX_ADDR_LOCK);
      while (hrdata_o_tb != 0)
        begin
          read_single_word_ahb(MBOX_ADDR_LOCK);
        end
    end
  endtask // wait_unlock_ahb

  //----------------------------------------------------------------
  // wait_unlock_apb()
  //
  // wait for the mailbox to unlock before send in anything
  //----------------------------------------------------------------
  task wait_unlock_apb;
    begin
      read_single_word_apb(MBOX_ADDR_LOCK);
      while (prdata_o_tb != 0)
        begin
          read_single_word_apb(MBOX_ADDR_LOCK);
        end
    end
  endtask // wait_unlock_apb


  //----------------------------------------------------------------
  // set_security_state()
  //
  // sets the security state explicily to any valid value 
  //----------------------------------------------------------------
  task set_security_state(input security_state_t ss);

      begin
          security_state = '{device_lifecycle: ss.device_lifecycle, debug_locked: ss.debug_locked};

          set_initval("CPTRA_SECURITY_STATE", ss & 32'h0000_0007);  
      end
  endtask


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
      wait_unlock_ahb();

      //write to MBOX_ADDR_CMD
      write_single_word_ahb(MBOX_ADDR_CMD, 32'hDEADBEEF);

      // write to MBOX_ADDR_DLEN
      write_single_word_ahb(MBOX_ADDR_DLEN, 32'h00000010);

      // write a block in
      write_block_ahb(block);
      @(posedge clk_tb);
      
      // execute
      write_single_word_ahb(MBOX_ADDR_EXECUTE, 32'h00000001);
      repeat (20) @(posedge clk_tb);

      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);
      read_result_apb(result_data);

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
      wait_unlock_apb();

      //write to MBOX_ADDR_CMD
      write_single_word_apb(MBOX_ADDR_CMD, 32'hDEADBEEF);

      // write to MBOX_ADDR_DLEN
      write_single_word_apb(MBOX_ADDR_DLEN, 32'h00000010);

      // write a block in
      write_block_apb(block);
      @(posedge clk_tb);
      
      // execute
      write_single_word_apb(MBOX_ADDR_EXECUTE, 32'h00000001);
      repeat (20) @(posedge clk_tb);

      // wait_ready();

      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);
      read_result_ahb(result_data);

      // reset excecute
      write_single_word_ahb(MBOX_ADDR_EXECUTE, 32'h00000000);

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


      $display("mailbox ahb test");
      $display("---------------------");
      mbox_ahb_test(8'h01, ahb_message_1);

      $display("mailbox apb test");
      $display("---------------------");
      mbox_apb_test(8'h01, apb_message_1);


    end
  endtask // mbox_test


  //----------------------------------------------------------------
  // sim_dut_init();
  // 
  // common sim and dut initialization routines for register tests 
  //----------------------------------------------------------------
  task sim_dut_init;

    int sscode = -1;

    begin
      sscode = int'(security_state);
      if (!((sscode >= 0)  || (sscode <= 7))) 
        $error("Have to explictily set security_state for soc_ifc_top for test to run!");

      else begin
        init_sim();
        reset_dut();

        wait (ready_for_fuses == 1'b1);
        update_exp_regval(socregs.get_addr("CPTRA_FLOW_STATUS"), 32'h4000_0000, SET_DIRECT); // , sscode);     

        repeat (5) @(posedge clk_tb);
      end
    end

  endtask // sim_dut_init

  
  //----------------------------------------------------------------
  // simulate_caliptra_boot();
  //
  // Set boot fuse write and boot status over APB 
  //----------------------------------------------------------------

  task simulate_caliptra_boot;
      // Enable release of Caliptra core from reset & simulate FW boot
      write_single_word_apb(socregs.get_addr("CPTRA_FUSE_WR_DONE"), 32'h1); 
      update_exp_regval(socregs.get_addr("CPTRA_FUSE_WR_DONE"), 32'h1, SET_APB);
      socregs.lock_fuses();

      repeat (3) @(posedge clk_tb); 
      write_single_word_apb(socregs.get_addr("CPTRA_BOOTFSM_GO"), 32'h1); 
      update_exp_regval(socregs.get_addr("CPTRA_BOOTFSM_GO"), 32'h1, SET_APB);

      repeat (20) @(posedge clk_tb); // simulate FW boot

  endtask // simulate_caliptra_boot


  //----------------------------------------------------------------
  // write_regs()
  //
  // Utility for tracking/writing to list of registers over APB/AHB
  //----------------------------------------------------------------
  task write_regs(input access_t modifier, strq_t reglist, int tid, int wait_cycles);
    string rname;
    word_addr_t addr;
    WordTransaction wrtrans;

    int tid_autoinc; 

    begin
      wrtrans = new();

      if (tid < 0) begin
        tid_autoinc = 1;
        tid = 0;
      end 

      $display("");

      foreach (reglist[i]) begin 
        rname = reglist[i];
        addr = socregs.get_addr(rname); 
        if (tid_autoinc) 
          tid += 1;
        wrtrans.update(addr, 0, tid); 
        wrtrans.randomize();
        if (modifier == SET_AHB) begin
          write_single_word_ahb(addr, wrtrans.data); 
          $display("Write over AHB: addr = %30s (0x%08x), data = 0x%08x", rname, addr, wrtrans.data);
        end else if (modifier == SET_APB) begin
          write_single_word_apb(addr, wrtrans.data); 
          $display("Write over APB: addr = %30s (0x%08x), data = 0x%08x", rname, addr, wrtrans.data);
        end else 
          $error("TB ERROR. Unsupported access modifier %s", modifier.name()); 

        sb.record_entry(wrtrans, modifier);
        if (wait_cycles == 0)
          @(posedge clk_tb);
        else
          repeat (wait_cycles) @(posedge clk_tb);
      end
    end
  endtask


  //----------------------------------------------------------------
  // read_regs()
  //
  // Utility for tracking/reading from list of registers over APB/AHB
  //----------------------------------------------------------------
  task read_regs(input access_t modifier, strq_t reglist, int tid, int wait_cycles);
    string rname;
    word_addr_t addr;
    WordTransaction rdtrans;

    int tid_autoinc; 

    begin
      rdtrans = new();

      if (tid < 0) begin
        tid_autoinc = 1;
        tid = 0;
      end 

      $display("");

      foreach (reglist[i]) begin 
        rname = reglist[i];
        addr = socregs.get_addr(rname); 
        if (tid_autoinc) 
          tid += 1;

        if (modifier == GET_AHB) begin
          read_single_word_ahb(addr);
          $display("Read over AHB:  addr = %30s (0x%08x), data = 0x%08x", rname, addr, hrdata_o_tb); 
          rdtrans.update(addr, hrdata_o_tb, tid); 
        end else if (modifier == GET_APB) begin
          read_single_word_apb(addr);
          $display("Read over APB:  addr = %30s (0x%08x), data = 0x%08x", rname, addr, prdata_o_tb); 
          rdtrans.update(addr, prdata_o_tb, tid); 
        end else 
          $error("TB ERROR. Unsupported access modifier %s", modifier.name()); 

        sb.check_entry(rdtrans);
        if (wait_cycles == 0)
          @(posedge clk_tb);
        else
          repeat (wait_cycles) @(posedge clk_tb);

      end
    end
  endtask


//----------------------------------------------------------------
// Following tests in include files should ideally be in packages 
// or as programs. For now, this is the only modularization for 
// directed tests planned.
//----------------------------------------------------------------
//
  `include "fuse_reg_lifecycle_test.svh"   
  `include "fuse_reg_perm_test.svh"     
  `include "fuse_reg_test.svh"     
  `include "single_soc_reg_test.svh"   
  `include "soc_reg_reset_test.svh"     
  `include "soc_reg_test.svh"     
//----------------------------------------------------------------



  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------        


 
  initial begin : main

    // common initialization steps for all tests 

    // set_security_state(DEVICE_PRODUCTION, DEBUG_LOCKED);
    // update_exp_regval(socregs.get_addr("CPTRA_SECURITY_STATE"), dword_t'(security_state), SET_DIRECT);


    if ($value$plusargs("SOC_IFC_TEST=%s", soc_ifc_testname)) 
      begin : alternate_test
        $display("    =================================================================");
        $display("    Running SOC_IFC_TEST = %s", soc_ifc_testname);
        $display("    =================================================================");

        // TODO. Push boiler-plate into task
        if (soc_ifc_testname == "soc_reg_pwron_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          soc_reg_pwron_test();

        end else if (soc_ifc_testname == "soc_reg_wrmrst_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          soc_reg_wrmrst_test();


        end else if (soc_ifc_testname == "fuse_reg_prod_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          fuse_reg_test();

        end else if (soc_ifc_testname == "fuse_reg_lifecycle_test") begin 
          // sim_dut_init() rolled into fuse_reg_lifecycle_test
          if ($value$plusargs("SECURITY_STATE=%s", security_state_testname)) 
            fuse_reg_lifecycle_test(security_state_testname);
          else
            fuse_reg_lifecycle_test("ALL");
 
        end else if (soc_ifc_testname == "soc_reg_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          soc_reg_test();

        end else if (soc_ifc_testname == "single_socreg_test") begin 
          if (!($value$plusargs("SOCREG_METHOD_NAME=%s", socreg_method_name))) 
            $display("ERROR with testing one soc_register; must provide method & name for +scoreg_method_name,eg. APB.CPTRA_TIMER_CONFIG");
          else begin
            set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
            sim_dut_init();
            single_socreg_test(socreg_method_name);
          end

        end else if (soc_ifc_testname == "fuse_reg_perm_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          fuse_reg_perm_test();

        end 
   
        @(posedge clk_tb);
        display_test_results();

        $display("\n*** '%s' test simulation done. ***", soc_ifc_testname);
        $finish;
      end  // alternate_test

    else 
      begin : default_test  // Keeping original default test structure 
        $display("    ==============================");
        $display("   -= Testbench for MBOX started =-");
        $display("    ==============================");
        $display("");

        set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});

        init_sim();
        reset_dut();

        wait (ready_for_fuses == 1'b1);
        //load_fuses();
        write_single_word_apb(MBOX_FUSE_DONE_ADDR, 32'h00000001);
        repeat (5) @(posedge clk_tb);
        
        mbox_test();

        display_test_results();
        
        $display("");
        $display("*** MBOX simulation done. ***");
        $finish;
      end // default_test 
  end // main
endmodule // soc_ifc_tb
