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
// csrng_tb.sv
// --------
// Integration test bench to ensure read/write through AHB is working
// with csrng ip.
//
//======================================================================

module csrng_tb
  import csrng_pkg::*;
  import csrng_reg_pkg::*;
  import entropy_src_pkg::*;
  import entropy_src_reg_pkg::*;
  import lc_ctrl_pkg::*;
  import prim_mubi_pkg::mubi8_t;
(
`ifdef VERILATOR
  input bit clk_tb
`endif
  );

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG = 0;

  parameter CLK_HALF_PERIOD = 2;

  // The address map.
  parameter ADDR_INTR_STATE      = 32'h0;
  parameter ADDR_INTR_ENABLE     = 32'h4;
  parameter ADDR_INTR_TEST       = 32'h8;
  parameter ADDR_ALERT_TEST      = 32'hc;
  parameter ADDR_REGWEN          = 32'h10;
  parameter ADDR_CTRL            = 32'h14;
  parameter ADDR_CMD_REQ         = 32'h18;
  parameter ADDR_SW_CMD_STS      = 32'h1c;
  parameter ADDR_GENBITS_VLD     = 32'h20;
  parameter ADDR_GENBITS         = 32'h24;
  parameter ADDR_INT_STATE_NUM   = 32'h28;
  parameter ADDR_INT_STATE_VAL   = 32'h2c;
  parameter ADDR_HW_EXC_STS      = 32'h30;
  parameter ADDR_RECOV_ALERT_STS = 32'h34;
  parameter ADDR_ERR_CODE        = 32'h38;
  parameter ADDR_ERR_CODE_TEST   = 32'h3c;
  parameter ADDR_MAIN_SM_STATE   = 32'h40;

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


`ifndef VERILATOR
  reg           clk_tb;
`endif
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
  logic  [AHB_DATA_WIDTH-1:0] hrdata_o_tb;

  reg [31 : 0]  read_data;
  reg [255 : 0] digest_data;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  entropy_src_hw_if_req_t entropy_src_hw_if_req;
  entropy_src_hw_if_rsp_t entropy_src_hw_if_rsp;
  cs_aes_halt_req_t       csrng_cs_aes_halt_req;
  cs_aes_halt_rsp_t       csrng_cs_aes_halt_rsp;
  entropy_src_rng_rsp_t   entropy_src_rng_rsp;

  csrng #(
    .RndCnstCsKeymgrDivNonProduction('0),
    .RndCnstCsKeymgrDivProduction('0),
    .AHBDataWidth(AHB_DATA_WIDTH),
    .AHBAddrWidth(AHB_ADDR_WIDTH)
  ) dut (
      // Clock and reset connections
      .clk_i       (clk_tb),
      .rst_ni      (reset_n_tb),
      // AMBA AHB Lite Interface
      .haddr_i     (haddr_i_tb),
      .hwdata_i    (hwdata_i_tb),
      .hsel_i      (hsel_i_tb),
      .hwrite_i    (hwrite_i_tb),
      .hready_i    (hready_i_tb),
      .htrans_i    (htrans_i_tb),
      .hsize_i     (hsize_i_tb),
      .hresp_o     (hresp_o_tb),
      .hreadyout_o (hreadyout_o_tb),
      .hrdata_o    (hrdata_o_tb),
       // OTP Interface
      .otp_en_csrng_sw_app_read_i(prim_mubi_pkg::MuBi8True),
      // Lifecycle broadcast inputs
      .lc_hw_debug_en_i(lc_ctrl_pkg::On),
      // Entropy Interface
      .entropy_src_hw_if_o(entropy_src_hw_if_req),
      .entropy_src_hw_if_i(entropy_src_hw_if_rsp),
      .cs_aes_halt_i      (csrng_cs_aes_halt_req),
      .cs_aes_halt_o      (csrng_cs_aes_halt_rsp),
      // Application Interfaces
      .csrng_cmd_i('0),
      .csrng_cmd_o(),
      // Alerts
      .alert_tx_o  (),
      .alert_rx_i  ('0),
      // Interrupt
      .intr_cs_cmd_req_done_o (),
      .intr_cs_entropy_req_o  (),
      .intr_cs_hw_inst_exc_o  (),
      .intr_cs_fatal_err_o    ()
  );

  //----------------------------------------------------------------
  // clk_gen
  //
  // Clock generator process.
  //----------------------------------------------------------------
`ifndef VERILATOR
  always
    begin : clk_gen
      #CLK_HALF_PERIOD
      clk_tb = !clk_tb;
    end // clk_gen
`endif

  //----------------------------------------------------------------
  // sys_monitor
  //
  // Generates a cycle counter and displays information about
  // the dut as needed.
  //----------------------------------------------------------------
  always @(posedge clk_tb) begin : sys_monitor
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

      repeat (2) @(posedge clk_tb);
      reset_n_tb = 1;

      repeat (2) @(posedge clk_tb);

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
`ifndef VERILATOR
      clk_tb        = 0;
`endif
      reset_n_tb    = 0;

      haddr_i_tb      = 0;
      hwdata_i_tb     = 0;
      hsel_i_tb       = 0;
      hwrite_i_tb     = 0;
      hready_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hsize_i_tb      = 3'b011;

      csrng_cs_aes_halt_req = '{default:'0};
      entropy_src_rng_rsp = '{default:'0};
      entropy_src_hw_if_rsp = '{default:'0};
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
  // write_single_word()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_single_word(input [31 : 0]  address,
                  input [31 : 0] word);
    begin
      $display("[%t] write_single_word(addr=0x%x, word=0x%x)", $time, address, word);
      hsel_i_tb       = 1;
      haddr_i_tb      = address;
      hwrite_i_tb     = 1;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hsize_i_tb      = 3'b010;

      @(posedge clk_tb);
      haddr_i_tb      = 'Z;
      hwdata_i_tb     = word;
      hwrite_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      wait(hreadyout_o_tb == 1'b1);

      @(posedge clk_tb);
      hsel_i_tb       = 0;
    end
  endtask // write_single_word

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

      @(posedge clk_tb);
      hwdata_i_tb     = 0;
      haddr_i_tb      = 'Z;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      read_data       = hrdata_o_tb;
      wait(hreadyout_o_tb == 1'b1);

      @(posedge clk_tb);
      hsel_i_tb       = 0;
      $display("[%t] read_single_word(addr=0x%x) = 0x%x", $time, address, read_data);

    end
  endtask // read_single_word

  //----------------------------------------------------------------
  // read_and_compare()
  //
  // Read a data word from the given address and compare against
  // an expected value.  Increment an error if there is a mismatch.
  //----------------------------------------------------------------
  task read_and_compare(
    input logic [31:0] addr,
    input logic [31:0] expected_data
  );
    read_single_word(addr);
    if (read_data != expected_data) begin
      error_ctr += 1;
      $display("Got: 0x%x Want: 0x%x", read_data, expected_data);
    end
  endtask : read_and_compare

  logic [31:0] test_vector_q[$];  // queue of random input

  //----------------------------------------------------------------
  // poll_register_value()
  //
  // Poll a register until a desired value has been hit.
  //----------------------------------------------------------------
  task poll_register_value(
      input logic [31:0] addr,
      input logic [31:0] value
  );

    do begin
      read_single_word(addr);
      repeat(10) @(posedge clk_tb);
    end while (read_data != value);
  endtask

  //----------------------------------------------------------------
  // enable_csrng()
  //
  // Configure the control register and enable csrng module
  //----------------------------------------------------------------
  task enable_csrng;

    // Configure Register
    // 3:0 ENABLE
    // 7:4 SW_APP_ENABLE
    // 11:8 READ_INT_STATE
    // 6 = True, 9 = False
    write_single_word(ADDR_CTRL, 32'h666);

  endtask

  //----------------------------------------------------------------
  // run_smoke_test()
  //
  // Configure and request a rng through the csrng_hw_if interface
  // Once a request is acked, validate against test vector provided
  //----------------------------------------------------------------
  task run_smoke_test;
    $display("Uninitiate Command");
    write_single_word(ADDR_CMD_REQ, 32'h0905);
    repeat (200) @(posedge clk_tb);
    poll_register_value(ADDR_SW_CMD_STS, 32'h1);

    $display("Initiate Command - Writing 48B of seed");
    write_single_word(ADDR_CMD_REQ, 32'h06C1);
    write_single_word(ADDR_CMD_REQ, 32'h73BEC010);
    write_single_word(ADDR_CMD_REQ, 32'h9262474c);
    write_single_word(ADDR_CMD_REQ, 32'h16a30f76);
    write_single_word(ADDR_CMD_REQ, 32'h531b51de);
    write_single_word(ADDR_CMD_REQ, 32'h2ee494e5);
    write_single_word(ADDR_CMD_REQ, 32'hdfec9db3);
    write_single_word(ADDR_CMD_REQ, 32'hcb7a879d);
    write_single_word(ADDR_CMD_REQ, 32'h5600419c);
    write_single_word(ADDR_CMD_REQ, 32'hca79b0b0);
    write_single_word(ADDR_CMD_REQ, 32'hdda33b5c);
    write_single_word(ADDR_CMD_REQ, 32'ha468649e);
    write_single_word(ADDR_CMD_REQ, 32'hdf5d73fa);

    poll_register_value(ADDR_SW_CMD_STS, 32'h1);

    $display("Generate Command - 512b");
    write_single_word(ADDR_CMD_REQ, 32'h4903);
    poll_register_value(ADDR_GENBITS_VLD, 32'h1);

    read_and_compare(ADDR_GENBITS, 32'h378FCA1E);
    read_and_compare(ADDR_GENBITS, 32'hcf763d08);
    read_and_compare(ADDR_GENBITS, 32'h17166e90);
    read_and_compare(ADDR_GENBITS, 32'h0b165308);

    poll_register_value(ADDR_GENBITS_VLD, 32'h1);
    read_and_compare(ADDR_GENBITS, 32'h359fbe3e);
    read_and_compare(ADDR_GENBITS, 32'ha69B1Bf1);
    read_and_compare(ADDR_GENBITS, 32'h14117211);
    read_and_compare(ADDR_GENBITS, 32'hc01a0839);


    poll_register_value(ADDR_GENBITS_VLD, 32'h1);
    read_and_compare(ADDR_GENBITS, 32'h58d7e45d);
    read_and_compare(ADDR_GENBITS, 32'hc5e00eb8);
    read_and_compare(ADDR_GENBITS, 32'hce7ab38f);
    read_and_compare(ADDR_GENBITS, 32'h6e48e546);

    poll_register_value(ADDR_GENBITS_VLD, 32'h1);
    read_and_compare(ADDR_GENBITS, 32'h49de93f9);
    read_and_compare(ADDR_GENBITS, 32'h88A65Ec7);
    read_and_compare(ADDR_GENBITS, 32'hc58a553e);
    read_and_compare(ADDR_GENBITS, 32'h5d6e1012);

    poll_register_value(ADDR_SW_CMD_STS, 32'h1);

    $display("Generate Command - 512b");
    write_single_word(ADDR_CMD_REQ, 32'h4903);
    poll_register_value(ADDR_GENBITS_VLD, 32'h1);

    read_and_compare(ADDR_GENBITS, 32'he48bb8cb);
    read_and_compare(ADDR_GENBITS, 32'h1012c84c);
    read_and_compare(ADDR_GENBITS, 32'h5af8a7f1);
    read_and_compare(ADDR_GENBITS, 32'hd1c07cd9);

    poll_register_value(ADDR_GENBITS_VLD, 32'h1);
    read_and_compare(ADDR_GENBITS, 32'hdf82ab22);
    read_and_compare(ADDR_GENBITS, 32'h771c619b);
    read_and_compare(ADDR_GENBITS, 32'hd40fccb1);
    read_and_compare(ADDR_GENBITS, 32'h87189e99);

    poll_register_value(ADDR_GENBITS_VLD, 32'h1);
    read_and_compare(ADDR_GENBITS, 32'h510494b3);
    read_and_compare(ADDR_GENBITS, 32'h64f7ac0c);
    read_and_compare(ADDR_GENBITS, 32'h2581f391);
    read_and_compare(ADDR_GENBITS, 32'h80b1dc2f);

    poll_register_value(ADDR_GENBITS_VLD, 32'h1);

    read_and_compare(ADDR_GENBITS, 32'h793e01c5);
    read_and_compare(ADDR_GENBITS, 32'h87b107ae);
    read_and_compare(ADDR_GENBITS, 32'hdb17514c);
    read_and_compare(ADDR_GENBITS, 32'ha43c41b7);

    poll_register_value(ADDR_SW_CMD_STS, 32'h1);

  endtask // run_smoke_test

  //----------------------------------------------------------------
  // run_entropy_source_seed_test()
  //
  // Instantiate a csrng and use entropy source seed
  //----------------------------------------------------------------
  task run_entropy_source_seed_test;

    $display("Instantiate Command - Use entropy Source Seed");
    write_single_word(ADDR_CMD_REQ, 32'h901);

    $display("Wait for Request");
    wait (entropy_src_hw_if_req.es_req == 1'b1);
    repeat (5000) @(posedge clk_tb);

    entropy_src_hw_if_rsp.es_ack = 1'b1;
    entropy_src_hw_if_rsp.es_bits = 384'h33F63B65F57AD68765693560E743CC5010518E4BF4ECBEBA71DC56AAA08B394311731D9DF763FC5D27E4ED3E4B7DE947;
    repeat (1) @(posedge clk_tb);
    entropy_src_hw_if_rsp.es_ack = 1'b0;

    repeat (30) @(posedge clk_tb);

    $display("Generate Request");
    write_single_word(ADDR_CMD_REQ, 32'h1003);

    poll_register_value(ADDR_GENBITS_VLD, 32'h1);
    read_and_compare(ADDR_GENBITS, 32'h15eb2a44);
    read_and_compare(ADDR_GENBITS, 32'h310851dd);
    read_and_compare(ADDR_GENBITS, 32'hba1365ab);
    read_and_compare(ADDR_GENBITS, 32'h4c7322f4);

    repeat (1000) @(posedge clk_tb);

  endtask // run_entropy_source_seed_test

  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -- Testbench for csrng started --");

      init_sim();
      reset_dut();


      repeat (1000) @(posedge clk_tb);
      enable_csrng();

      run_entropy_source_seed_test();
      run_smoke_test();

      display_test_result();

      $display("   -- Testbench for csrng done. --");
      $finish;
    end // main
endmodule // csrng_tb

//======================================================================
// EOF csrng_tb.sv
//======================================================================
