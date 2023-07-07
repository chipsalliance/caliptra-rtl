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
// spi_host_tb.sv
// --------
// Integration test bench to ensure read/write through AHB is working
// with spi_host ip.
//
//======================================================================

module spi_host_tb
  import spi_host_reg_pkg::*;
  import spi_device_pkg::*;
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
  parameter NUM_HOSTS = 2;

  parameter CLK_HALF_PERIOD = 2;

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  parameter AHB_ADDR_WIDTH = 32;
  parameter AHB_DATA_WIDTH = 32;

  typedef struct packed {
    logic       ready;     // spi host ready to receive command
    logic       active;    // processing previously issued command
    logic       txfull;    // tx fifo is full
    logic       txempty;   // tx fifo is empty
    logic       txstall;   // transaction has stalled due to lack of data in the tx fifo
    logic       txwm;      // tx watermark
    logic       rxfull;    // rx fifo is full
    logic       rxempty;   // rx fifo is empty
    logic       rxstall;   // ongoing transaction stalled due to lack of space in rx fifo
    logic       byteorder; // value of ByteOrder parameter
    logic       reserved;
    logic       rxwm;      // rx watermark
    logic [3:0] cmdqd;     // command queue depth
    logic [7:0] rxqd;      // receive queue depth
    logic [7:0] txqd;      // transmit queue depth
  } spi_host_status_t;

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
  wire  [3:0] spi_flash_sd;
  logic       spi_flash_sck;
  logic [1:0] spi_flash_csb;

  logic             cio_sck_o;
  logic             cio_sck_en_o;
  logic [NumCS-1:0] cio_csb_o;
  logic [NumCS-1:0] cio_csb_en_o;
  logic [3:0]       cio_sd_o;
  logic [3:0]       cio_sd_en_o;
  logic [3:0]       cio_sd_i;

  assign spi_flash_sck = cio_sck_en_o ? cio_sck_o : 1'b0;

  for (genvar ii = 0; ii < NumCS; ii += 1) begin : gen_qspi_csb
    assign spi_flash_csb[ii] = cio_csb_en_o[ii] ? cio_csb_o[ii] : 1'b1;  // leave all high
  end

  for (genvar ii = 0; ii < 4; ii += 1 ) begin : gen_qspi_sd
    assign spi_flash_sd[ii] = cio_sd_en_o[ii] ? cio_sd_o[ii] : 1'bz;
    assign cio_sd_i[ii] = cio_sd_en_o[ii] ? 1'bz : spi_flash_sd[ii];
  end

  spi_host #(
    .AHBDataWidth(32),
    .AHBAddrWidth(32)
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
    .alert_rx_i(caliptra_prim_alert_pkg::ALERT_RX_DEFAULT),
    .alert_tx_o(),

    // SPI Interface
    .cio_sck_o    (cio_sck_o),
    .cio_sck_en_o (cio_sck_en_o),
    .cio_csb_o    (cio_csb_o),
    .cio_csb_en_o (cio_csb_en_o),
    .cio_sd_o     (cio_sd_o),
    .cio_sd_en_o  (cio_sd_en_o),
    .cio_sd_i     (cio_sd_i),

    .intr_error_o(),
    .intr_spi_event_o()
  );

  localparam logic [15:0] DeviceId0 = 16'hBA5E;
  localparam logic [15:0] DeviceId1 = 16'h5AFE;

  spiflash #(
    .DeviceId(DeviceId0)
  ) spiflash0 (
    .sck (spi_flash_sck),
    .csb (spi_flash_csb[0]),
    .sd  (spi_flash_sd)
  );

  spiflash #(
    .DeviceId(DeviceId1)
  ) spiflash1 (
    .sck (spi_flash_sck),
    .csb (spi_flash_csb[1]),
    .sd  (spi_flash_sd)
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
  always_ff @(posedge clk_tb) begin : sys_monitor
      cycle_ctr = (~reset_n_tb) ? 0 : cycle_ctr + 1;
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
  task write_single_word(
    input [spi_host_reg_pkg::BlockAw-1: 0]  addr,
    input [31 : 0] word
  );

    logic [31:0] address;
    address = {{32-spi_host_reg_pkg::BlockAw{1'b0}}, addr};

    $display("[%t] write_single_word(addr=0x%x, word=0x%x)", $time, address, word);
    hsel_i_tb       = 1;
    haddr_i_tb      = address;
    hwdata_i_tb     = word;
    hwrite_i_tb     = 1;
    hready_i_tb     = 1;
    htrans_i_tb     = AHB_HTRANS_NONSEQ;
    hsize_i_tb      = 3'b010;

    @(posedge clk_tb);
    hwdata_i_tb     = word;
    hwrite_i_tb     = 0;
    htrans_i_tb     = AHB_HTRANS_IDLE;
    wait(hreadyout_o_tb == 1'b1);

    @(posedge clk_tb);
    hsel_i_tb       = 0;
  endtask // write_single_word

  //----------------------------------------------------------------
  // read_word()
  //
  // Read a data word from the given address in the DUT.
  // the word read will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_single_word(input [spi_host_reg_pkg::BlockAw-1 : 0]  addr);
    logic [31:0] address;
    spi_host_status_t status;
    address = {{32-spi_host_reg_pkg::BlockAw{1'b0}}, addr};

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

    if (addr == spi_host_reg_pkg::SPI_HOST_STATUS_OFFSET) begin
      status = read_data;
`ifdef VERILATOR
      $display("[%t] read_single_word(addr=0x%x) = %x {ready=%d active=%d rxqd=%d txqd=%d}",
        $time, address, status, status.ready, status.active, status.rxqd, status.txqd);
`else
      $display("[%t] read_single_word(addr=0x%x) = %p", $time, address, status);
`endif
    end else begin
      $display("[%t] read_single_word(addr=0x%x) = 0x%x", $time, address, read_data);
    end

  endtask // read_word

  task set_spi_csid(input int id);
    write_single_word(spi_host_reg_pkg::SPI_HOST_CSID_OFFSET, {31'h0, id[0]});
  endtask : set_spi_csid

  task spi_command (
    input int len,
    input logic csaat, // chip select active after transaction
    input spi_host_cmd_pkg::speed_t speed,
    input spi_host_cmd_pkg::reg_direction_t direction
  );

    logic [8:0] length;
    spi_host_status_t status;
    length = len[8:0];

    // Wait for Status.ready
    do begin
      read_single_word(spi_host_reg_pkg::SPI_HOST_STATUS_OFFSET);
      status = read_data;
      if (!status.ready) begin
        repeat(10) @(posedge clk_tb);
      end
    end while (!status.ready);

    write_single_word(spi_host_reg_pkg::SPI_HOST_COMMAND_OFFSET, {18'h0,  // reserved
                                     direction,
                                     speed,
                                     csaat,
                                     length});
  endtask : spi_command

  task spi_command_wait();
    spi_host_status_t status;
    // Wait for Status.active
    do begin
      read_single_word(spi_host_reg_pkg::SPI_HOST_STATUS_OFFSET);
      status = read_data;
      if (status.active) begin
        repeat(10) @(posedge clk_tb);
      end
    end while (status.active);

  endtask : spi_command_wait

  task write_tx_fifo (input logic [31:0] data);
    write_single_word(spi_host_reg_pkg::SPI_HOST_TXDATA_OFFSET, data);
  endtask : write_tx_fifo


  task read_rx_fifo (output logic [31:0] data);
    read_single_word(spi_host_reg_pkg::SPI_HOST_RXDATA_OFFSET);
    data = read_data;
  endtask : read_rx_fifo

  // configure_spi_host enables the IP and sets the protocol behavior
  task configure_spi_host(input int host);
    logic [spi_host_reg_pkg::BlockAw-1:0] offset;
    write_single_word(spi_host_reg_pkg::SPI_HOST_CONTROL_OFFSET, {1'b1,    // spi enable
                                    1'b0,    // sw rst
                                    1'b1,    // output enable
                                    13'h0,   // reserved
                                    8'h0,    // tx watermark
                                    8'h7f}); // rx watermark
    if (host == 0) begin
      offset = spi_host_reg_pkg::SPI_HOST_CONFIGOPTS_0_OFFSET;
    end else begin
      offset = spi_host_reg_pkg::SPI_HOST_CONFIGOPTS_1_OFFSET;
    end

    write_single_word(offset, {1'b0, // Polarity
                               1'b0, // Phase
                               1'b0, // full cycle
                               1'b0, // reserved
                               4'h0, // cs_n lead time
                               4'h0, // cs_n trail time
                               4'h0, // minimum time between commands
                               16'h0}); // core clock divider
  endtask : configure_spi_host

  //----------------------------------------------------------------
  // run_jedec_id_test()
  //
  // Configures the spi_host to request the jedec id
  // The spiflash device will return 7 bytes of continuous code ('h7f)
  // followed by the JedecId ('h1f) and the DeviceId ('h1234)
  //----------------------------------------------------------------
  task run_jedec_id_test(input int host);
    logic [31:0] rx_data;
    logic [31:0] exp_data[3];
    spi_host_status_t status;

    exp_data[0] = 32'h7f7f7f7f;
    exp_data[1] = 32'h1f7f7f7f;
    if (host == 0) begin
      exp_data[2] = {16'h0, DeviceId0};
    end else begin
      exp_data[2] = {16'h0, DeviceId1};
    end

    // Load the TX FIFO with instructions and data to be transmitted
    write_tx_fifo({24'h0, CmdJedecId});

    // Specify which device should receive the next command
    set_spi_csid(host);

    // Issue speed, direction and length details for the next command
    // segment.  If a command consists of multiple segments, set csaat to one
    // for all segments except the last one.
    //
    // Issue Command Instruction
    spi_command(.len(0),
                .csaat(1),
                .speed(spi_host_cmd_pkg::Standard),
                .direction(spi_host_cmd_pkg::WrOnly));

    // spi flash will return 10 bytes for the jedec command
    spi_command(.len(9), // Read Len+1 Bytes
                .csaat(0),
                .speed(spi_host_cmd_pkg::Standard),
                .direction(spi_host_cmd_pkg::RdOnly));

    // Wait for spi commands to finish before reading responses
    spi_command_wait();

    read_single_word(spi_host_reg_pkg::SPI_HOST_STATUS_OFFSET);
    status = read_data;
    // TODO: Replace with assertions when open source tooling is better
    // supported.
    if ({24'h0, status.rxqd} != $size(exp_data)) begin
      error_ctr += 1;
      $display("run_jedec_id_test: status.rxqd: Got: %d Want:%d", status.rxqd, $size(exp_data));
    end

    for (int ii = 0; ii < $size(exp_data); ii += 1) begin
      read_rx_fifo(rx_data);
      if (rx_data != exp_data[ii]) begin
        error_ctr += 1;
        $display("run_jedec_id_test: rx_data: Got: %d Want:%d", rx_data, exp_data[ii]);
      end
    end
  endtask : run_jedec_id_test


  //----------------------------------------------------------------
  // run_read_test()
  //
  // Configures the spi_host to request data from the spi flash
  // The spiflash device will return data at the requested addresses
  //----------------------------------------------------------------
  task automatic run_read_test(input int host);
    logic [31:0] rx_data;
    automatic logic [7:0]  rx_bytes[$] = {};
    spi_host_status_t status;
    logic [7:0]  spi_data;
    logic [19:0] spi_offset;

    localparam int NumBytes = 256;
    localparam logic [23:0] SpiFlashAddr = 24'h00ABCD;

    // Load the TX FIFO with instructions and data to be transmitted
    write_tx_fifo({24'h0, CmdReadQuad});
    // Upper Bytes are transmitted first, 8'h12 is ignored
    write_tx_fifo({8'h12, SpiFlashAddr[7:0],
                          SpiFlashAddr[15:8],
                          SpiFlashAddr[23:16]});

    // Specify which device should receive the next command
    set_spi_csid(host);

    // Issue speed, direction and length details for the next command
    // segment.  If a command consists of multiple segments, set csaat to one
    // for all segments except the last one.
    //
    // Issue Command Instruction
    spi_command(.len(0),
                .csaat(1),
                .speed(spi_host_cmd_pkg::Standard),
                .direction(spi_host_cmd_pkg::WrOnly));
    // Issue 3 Byte Address - (Send the CmdEn4B if 4B is needed)
    spi_command(.len(2),
                .csaat(1),
                .speed(spi_host_cmd_pkg::Standard),
                .direction(spi_host_cmd_pkg::WrOnly));

    // Issue 2 Dummy Cycles - This is derived from spiflash.DummyQuad-1
    spi_command(.len(1),
                .csaat(1),
                .speed(spi_host_cmd_pkg::Quad),
                .direction(spi_host_cmd_pkg::Dummy));

    // Request 13 bytes of data
    spi_command(.len(NumBytes-1), // Read Len+1 Bytes
                .csaat(0),
                .speed(spi_host_cmd_pkg::Quad),
                .direction(spi_host_cmd_pkg::RdOnly));

    // Wait for spi commands to finish before reading responses
    spi_command_wait();

    read_single_word(spi_host_reg_pkg::SPI_HOST_STATUS_OFFSET);
    status = read_data;

    // Store the bytes for comparison
    for (int ii = 0; ii < status.rxqd; ii += 1) begin
      read_rx_fifo(rx_data);
      rx_bytes.push_back(rx_data[0+:8]);
      rx_bytes.push_back(rx_data[8+:8]);
      rx_bytes.push_back(rx_data[16+:8]);
      rx_bytes.push_back(rx_data[24+:8]);
    end

    for (int ii = 0; ii < rx_bytes.size(); ii += 1) begin
      if (ii >= NumBytes) begin
        if (rx_bytes[ii] != 8'h0) begin
          error_ctr += 1;
          $display("Received Extra Non-Zero Bytes from SpiFlash.  Got: %d Want: %d Size:%d",
            rx_bytes[ii], 0, rx_bytes.size());
        end
        continue;
      end
      spi_offset = SpiFlashAddr[0+:$bits(spi_offset)] +
                             ii[0+:$bits(spi_offset)];
      if (host == 0) begin
        spi_data = spiflash0.storage[spi_offset];
      end else begin
        spi_data = spiflash1.storage[spi_offset];
      end
      if (rx_bytes[ii] != spi_data) begin
        error_ctr += 1;
        $display("[%d]spiflash.storage[%x] Got: %x Want: %x",
          ii,
          spi_offset,
          rx_bytes[ii],
          spi_data);
      end
    end
  endtask : run_read_test

  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -- Testbench for spi_host started --");

      init_sim();
      reset_dut();

      for (int host = 0; host < NUM_HOSTS; host +=1) begin
        configure_spi_host(host);
        // Run Tests
        run_jedec_id_test(host);
        run_read_test(host);
        run_read_test(host);
        run_read_test(host);
      end

      display_test_result();

      $finish;
    end // main
endmodule // spi_host_tb

//======================================================================
// EOF spi_host_tb.sv
//======================================================================
