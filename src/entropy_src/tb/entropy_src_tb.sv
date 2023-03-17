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
// entropy_src_tb.sv
// --------
// Integration test bench to ensure read/write through AHB is working
// with entropy_src ip.
//
//======================================================================

module entropy_src_tb
  import entropy_src_pkg::*;
  import entropy_src_reg_pkg::*;
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
  parameter ADDR_INTR_STATE                = 32'h0;
  parameter ADDR_INTR_ENABLE               = 32'h4;
  parameter ADDR_INTR_TEST                 = 32'h8;
  parameter ADDR_ALERT_TEST                = 32'hc;
  parameter ADDR_ME_REGWEN                 = 32'h10;
  parameter ADDR_SW_REGUPD                 = 32'h14;
  parameter ADDR_REGWEN                    = 32'h18;
  parameter ADDR_REV                       = 32'h1c;
  parameter ADDR_MODULE_ENABLE             = 32'h20;
  parameter ADDR_CONF                      = 32'h24;
  parameter ADDR_ENTROPY_CONTROL           = 32'h28;
  parameter ADDR_ENTROPY_DATA              = 32'h2c;
  parameter ADDR_HEALTH_TEST_WINDOWS       = 32'h30;
  parameter ADDR_REPCNT_THRESHOLDS         = 32'h34;
  parameter ADDR_REPCNTS_THRESHOLDS        = 32'h38;
  parameter ADDR_ADAPTP_HI_THRESHOLDS      = 32'h3c;
  parameter ADDR_ADAPTP_LO_THRESHOLDS      = 32'h40;
  parameter ADDR_BUCKET_THRESHOLDS         = 32'h44;
  parameter ADDR_MARKOV_HI_THRESHOLDS      = 32'h48;
  parameter ADDR_MARKOV_LO_THRESHOLDS      = 32'h4c;
  parameter ADDR_EXTHT_HI_THRESHOLDS       = 32'h50;
  parameter ADDR_EXTHT_LO_THRESHOLDS       = 32'h54;
  parameter ADDR_REPCNT_HI_WATERMARKS      = 32'h58;
  parameter ADDR_REPCNTS_HI_WATERMARKS     = 32'h5c;
  parameter ADDR_ADAPTP_HI_WATERMARKS      = 32'h60;
  parameter ADDR_ADAPTP_LO_WATERMARKS      = 32'h64;
  parameter ADDR_EXTHT_HI_WATERMARKS       = 32'h68;
  parameter ADDR_EXTHT_LO_WATERMARKS       = 32'h6c;
  parameter ADDR_BUCKET_HI_WATERMARKS      = 32'h70;
  parameter ADDR_MARKOV_HI_WATERMARKS      = 32'h74;
  parameter ADDR_MARKOV_LO_WATERMARKS      = 32'h78;
  parameter ADDR_REPCNT_TOTAL_FAILS        = 32'h7c;
  parameter ADDR_REPCNTS_TOTAL_FAILS       = 32'h80;
  parameter ADDR_ADAPTP_HI_TOTAL_FAILS     = 32'h84;
  parameter ADDR_ADAPTP_LO_TOTAL_FAILS     = 32'h88;
  parameter ADDR_BUCKET_TOTAL_FAILS        = 32'h8c;
  parameter ADDR_MARKOV_HI_TOTAL_FAILS     = 32'h90;
  parameter ADDR_MARKOV_LO_TOTAL_FAILS     = 32'h94;
  parameter ADDR_EXTHT_HI_TOTAL_FAILS      = 32'h98;
  parameter ADDR_EXTHT_LO_TOTAL_FAILS      = 32'h9c;
  parameter ADDR_ALERT_THRESHOLD           = 32'ha0;
  parameter ADDR_ALERT_SUMMARY_FAIL_COUNTS = 32'ha4;
  parameter ADDR_ALERT_FAIL_COUNTS         = 32'ha8;
  parameter ADDR_EXTHT_FAIL_COUNTS         = 32'hac;
  parameter ADDR_FW_OV_CONTROL             = 32'hb0;
  parameter ADDR_FW_OV_SHA3_START          = 32'hb4;
  parameter ADDR_FW_OV_WR_FIFO_FULL        = 32'hb8;
  parameter ADDR_FW_OV_RD_FIFO_OVERFLOW    = 32'hbc;
  parameter ADDR_FW_OV_RD_DATA             = 32'hc0;
  parameter ADDR_FW_OV_WR_DATA             = 32'hc4;
  parameter ADDR_OBSERVE_FIFO_THRESH       = 32'hc8;
  parameter ADDR_OBSERVE_FIFO_DEPTH        = 32'hcc;
  parameter ADDR_DEBUG_STATUS              = 32'hd0;
  parameter ADDR_RECOV_ALERT_STS           = 32'hd4;
  parameter ADDR_ERR_CODE                  = 32'hd8;
  parameter ADDR_ERR_CODE_TEST             = 32'hdc;
  parameter ADDR_MAIN_SM_STATE             = 32'he0;

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
  logic        generate_rng;


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
  entropy_src_rng_req_t entropy_src_rng_req;
  entropy_src_rng_rsp_t entropy_src_rng_rsp;

  entropy_src #(
    .AHBDataWidth(AHB_DATA_WIDTH),
    .AHBAddrWidth(AHB_ADDR_WIDTH)
  ) dut (
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
    .otp_en_entropy_src_fw_read_i (prim_mubi_pkg::MuBi8True),
    .otp_en_entropy_src_fw_over_i (prim_mubi_pkg::MuBi8True),
    // RNG Interface
    .rng_fips_o          (),
    // Entropy Interface
    .entropy_src_hw_if_i (entropy_src_hw_if_req),
    .entropy_src_hw_if_o (entropy_src_hw_if_rsp),
    // RNG Interface
    .entropy_src_rng_o   (entropy_src_rng_req),
    .entropy_src_rng_i   (entropy_src_rng_rsp),
    // CSRNG Interface
    .cs_aes_halt_o       (),
    .cs_aes_halt_i       (cs_aes_halt_rsp_t'('0)),
    // External Health Test Interface
    .entropy_src_xht_o   (),
    .entropy_src_xht_i   (entropy_src_xht_rsp_t'('0)),
    // Alerts
    .alert_rx_i          ('0),
    .alert_tx_o          (),
    // Interrupts
    .intr_es_entropy_valid_o      (),
    .intr_es_health_test_failed_o (),
    .intr_es_observe_fifo_ready_o (),
    .intr_es_fatal_err_o          ()
    );

  physical_rng physical_rng (
    .clk    (clk_tb),
    .enable (entropy_src_rng_req.rng_enable),
    .data   (entropy_src_rng_rsp.rng_b),
    .valid  (entropy_src_rng_rsp.rng_valid)
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
      generate_rng = '0;
      cycle_ctr    = '0;
      error_ctr    = '0;
      tc_ctr       = '0;
`ifndef VERILATOR
      clk_tb       = 0;
`endif
      reset_n_tb   = 0;

      haddr_i_tb   = 0;
      hwdata_i_tb  = 0;
      hsel_i_tb    = 0;
      hwrite_i_tb  = 0;
      hready_i_tb  = 0;
      htrans_i_tb  = AHB_HTRANS_IDLE;
      hsize_i_tb   = 3'b011;
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
  // read_word()
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
  endtask // read_word

  logic [31:0] test_vector_q[$];  // queue of random input

  //----------------------------------------------------------------
  // run_hw_if_test()
  //
  // Configure and request a rng through the entropy_src_hw_if interface
  // Once a request is acked, validate against test vector provided
  //----------------------------------------------------------------
  task run_hw_if_test;
    entropy_src_hw_if_req = '{default:'0};
    repeat (1000) @(posedge clk_tb);

    // Configure Register
    // 3:0 FIPS_ENABLE
    // 7:4 ENTROPY_DATA_REG_ENABLE
    // 15:12 THRESHOLD_SCOPE
    // 23:20 RNG_BIT_ENABLE
    // 25:24 RNG_BIT_SEL
    // 6 = True, 9 = False
    write_single_word(ADDR_CONF, 32'h909099);

    // Enable
    write_single_word(ADDR_MODULE_ENABLE, 32'h6);
    generate_rng = 1'b1;
    repeat (10) @(posedge clk_tb);

    // Request and wait for response
    entropy_src_hw_if_req.es_req = 1;
    wait (entropy_src_hw_if_rsp.es_ack == 1'b1);

    // Check the value received against the expected test_vector
    for (int ii = 0; ii < $bits(entropy_src_hw_if_rsp.es_bits)/32; ii += 1) begin
      if (entropy_src_hw_if_rsp.es_bits[ii*32+:32] != test_vector_q[0]) begin
        $display("[%d] Got: %x Want: %x", ii,
                                          entropy_src_hw_if_rsp.es_bits[ii*32+:32],
                                          test_vector_q[0]);
        error_ctr += 1;
      end
      test_vector_q.pop_front();
    end
    repeat (1) @(posedge clk_tb);
    entropy_src_hw_if_req.es_req = 0;
    repeat (1000) @(posedge clk_tb);

  endtask // run_hw_if_test

  //----------------------------------------------------------------
  // Scoreboard RNG Data
  //----------------------------------------------------------------
  int index;
  logic [AHB_DATA_WIDTH-1:0] test_vector;

  localparam int NUM_RNG_BITS = $bits(entropy_src_rng_rsp.rng_b);
  initial begin
    index = 0;
    test_vector_q = {};

    forever begin
      @(posedge clk_tb)
      // The Physical RNG outputs 4 bits of data.  We collect this in a shift
      // register until we receive 32 bits.  Then append to test_vector_q for
      // easier comparison downstream.
      if (entropy_src_rng_rsp.rng_valid) begin
        test_vector >>= NUM_RNG_BITS;
        // Append to MSB
        test_vector[$bits(test_vector) - NUM_RNG_BITS +: NUM_RNG_BITS] = entropy_src_rng_rsp.rng_b;

        index += 1;
        if (index == $bits(test_vector) / NUM_RNG_BITS) begin
          test_vector_q.push_back(test_vector);
          test_vector = '0;
          index = 0;
        end
      end
    end
  end

  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -- Testbench for entropy_src started --");

      init_sim();
      reset_dut();

      run_hw_if_test();

      display_test_result();

      $display("   -- Testbench for entropy_src done. --");
      $finish;
    end // main
endmodule // entropy_src_tb

//======================================================================
// EOF entropy_src_tb.sv
//======================================================================
