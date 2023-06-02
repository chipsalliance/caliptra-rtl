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
// uart_tb.sv
// --------
// Integration test bench to ensure read/write through AHB is working
// with uart ip.
//
//======================================================================

module uart_tb
  import uart_reg_pkg::*;
  import caliptra_prim_mubi_pkg::mubi8_t;
(
`ifdef VERILATOR
  input bit clk_tb
`endif
  );

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG = 0;
  parameter NUM_TX = 100;
  parameter USE_RANDOM_DATA = 1;

  parameter CLK_HALF_PERIOD = 2;

  // The address map.
  parameter ADDR_INTR_STATE   = 32'h0;
  parameter ADDR_INTR_ENABLE  = 32'h4;
  parameter ADDR_INTR_TEST    = 32'h8;
  parameter ADDR_ALERT_TEST   = 32'hc;
  parameter ADDR_CTRL         = 32'h10;
  parameter ADDR_STATUS       = 32'h14;
  parameter ADDR_RDATA        = 32'h18;
  parameter ADDR_WDATA        = 32'h1c;
  parameter ADDR_FIFO_CTRL    = 32'h20;
  parameter ADDR_FIFO_STATUS  = 32'h24;
  parameter ADDR_OVRD         = 32'h28;
  parameter ADDR_VAL          = 32'h2c;
  parameter ADDR_TIMEOUT_CTRL = 32'h30;

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

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  /* verilator lint_off UNOPTFLAT */
  wire loopback;

  uart #(
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
    // Alerts
    .alert_rx_i  (),
    .alert_tx_o  (),
    // Generic IO
    .cio_rx_i(loopback),
    .cio_tx_o(loopback),
    .cio_tx_en_o(),
    // Interrupts
    .intr_tx_watermark_o(),
    .intr_rx_watermark_o(),
    .intr_tx_empty_o(),
    .intr_rx_overflow_o(),
    .intr_rx_frame_err_o(),
    .intr_rx_break_err_o(),
    .intr_rx_timeout_o(),
    .intr_rx_parity_err_o()
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

  task  uart_tx(input logic [7:0] char);
      if (DEBUG) begin
        $display("uart_tx >> Sending 0x%x", char);
      end
      // Check the TX fifo is not full
      read_single_word(ADDR_STATUS);
      while (read_data[0] == 1) begin
        repeat (1000) @(posedge clk_tb);
        read_single_word(ADDR_STATUS);
      end

      write_single_word(ADDR_WDATA, {24'h0, char});  // Enable RX/TX

  endtask : uart_tx

  task  uart_rx();
      // Check if the RX fifo is empty
      read_single_word(ADDR_STATUS);
      while (read_data[5]) begin
        repeat (1000) @(posedge clk_tb);
        read_single_word(ADDR_STATUS);
      end

      // read the data
      read_single_word(ADDR_RDATA);
      if (DEBUG) begin
        $display("uart_rx << Receiving 0x%x", read_data[7:0]);
      end
  endtask : uart_rx

  //----------------------------------------------------------------
  // run_test()
  //
  // Configure and request a rng through the uart_hw_if interface
  // Once a request is acked, validate against test vector provided
  //----------------------------------------------------------------
  localparam logic [63:0] baud_rate = 115_200;
  logic [7:0] exp_data_q[$];  // queue of random input

  task automatic run_test;
    logic [31:0] random_data;
    logic [7:0]  exp_data, act_data;
    logic [31:0] ctrl;
    logic [63:0] nco;

    repeat (1000) @(posedge clk_tb);

    // 31:16 NCO
    // 9:8   rxblvl
    // 7     parity_odd
    // 6     parity_even
    // 5     line loopback enable
    // 4     system loopback enable
    // 2     RX Noise Filter
    // 1     Rx Enable
    // 0     Tx Enable
    // NCO Equation: 2^20 * Fbaud
    //              --------------
    //                   Fclk
    // Fbaud = baud rate in bits per second
    // Fclk  = fixed frequency of the IP
    nco = baud_rate << 20;
    nco = nco / 64'd100_000_000;

    $display("nco = %d", nco);
    ctrl = '0;
    ctrl[31:16] = nco[15:0];
    ctrl[1:0] = 2'b11;
    write_single_word(ADDR_CTRL, ctrl);  // Enable RX/TX

    // fork off two threads that send and receive the uart data
    fork
      // Generate random data for tx
      begin
        for (int ii = 1; ii < NUM_TX; ii += 1) begin
          if (USE_RANDOM_DATA) begin
            random_data = $urandom;
            exp_data = random_data[7:0];
          end else begin
            exp_data = ii[7:0];
          end
          exp_data_q.push_back(exp_data);
          uart_tx(exp_data);
        end
      end
      // Process received data for rx
      begin
        // Wait a few cycles until transmission starts
        repeat (1000)  @(posedge clk_tb);
        while (exp_data_q.size() > 0) begin
          uart_rx();

          act_data = read_data[7:0];
          if (act_data != exp_data_q[0]) begin
            error_ctr += 1;
            $display("Got: %x Want: %x", act_data, exp_data_q[0]);
          end

          exp_data_q.pop_front();
        end
      end
    join

  endtask // run_test

  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -- Testbench for uart started --");

      init_sim();
      reset_dut();

      run_test();

      display_test_result();

      $display("   -- Testbench for uart done. --");
      $finish;
    end // main
endmodule // uart_tb

//======================================================================
// EOF uart_tb.sv
//======================================================================
