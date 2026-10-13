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

  parameter CLK_HALF_PERIOD = 2;

  // The address map.
  parameter ADDR_INTR_STATE                = ENTROPY_SRC_INTR_STATE_OFFSET;
  parameter ADDR_INTR_ENABLE               = ENTROPY_SRC_INTR_ENABLE_OFFSET;
  parameter ADDR_INTR_TEST                 = ENTROPY_SRC_INTR_TEST_OFFSET;
  parameter ADDR_ALERT_TEST                = ENTROPY_SRC_ALERT_TEST_OFFSET;
  parameter ADDR_ME_REGWEN                 = ENTROPY_SRC_ME_REGWEN_OFFSET;
  parameter ADDR_SW_REGUPD                 = ENTROPY_SRC_SW_REGUPD_OFFSET;
  parameter ADDR_REGWEN                    = ENTROPY_SRC_REGWEN_OFFSET;
  parameter ADDR_REV                       = ENTROPY_SRC_REV_OFFSET;
  parameter ADDR_MODULE_ENABLE             = ENTROPY_SRC_MODULE_ENABLE_OFFSET;
  parameter ADDR_CONF                      = ENTROPY_SRC_CONF_OFFSET;
  parameter ADDR_ENTROPY_CONTROL           = ENTROPY_SRC_ENTROPY_CONTROL_OFFSET;
  parameter ADDR_ENTROPY_DATA              = ENTROPY_SRC_ENTROPY_DATA_OFFSET;
  parameter ADDR_HEALTH_TEST_WINDOWS       = ENTROPY_SRC_HEALTH_TEST_WINDOWS_OFFSET;
  parameter ADDR_THRESHOLD_ONEWAY          = ENTROPY_SRC_THRESHOLD_ONEWAY_OFFSET;
  parameter ADDR_REPCNT_THRESHOLD          = ENTROPY_SRC_REPCNT_THRESHOLD_OFFSET;
  parameter ADDR_REPCNTS_THRESHOLD         = ENTROPY_SRC_REPCNTS_THRESHOLD_OFFSET;
  parameter ADDR_ADAPTP_HI_THRESHOLD       = ENTROPY_SRC_ADAPTP_HI_THRESHOLD_OFFSET;
  parameter ADDR_ADAPTP_LO_THRESHOLD       = ENTROPY_SRC_ADAPTP_LO_THRESHOLD_OFFSET;
  parameter ADDR_ADAPTPS_THRESHOLD         = ENTROPY_SRC_ADAPTPS_THRESHOLD_OFFSET;
  parameter ADDR_BUCKET_THRESHOLD          = ENTROPY_SRC_BUCKET_THRESHOLD_OFFSET;
  parameter ADDR_MARKOV_HI_THRESHOLD       = ENTROPY_SRC_MARKOV_HI_THRESHOLD_OFFSET;
  parameter ADDR_MARKOV_LO_THRESHOLD       = ENTROPY_SRC_MARKOV_LO_THRESHOLD_OFFSET;
  parameter ADDR_EXTHT_HI_THRESHOLD        = ENTROPY_SRC_EXTHT_HI_THRESHOLD_OFFSET;
  parameter ADDR_EXTHT_LO_THRESHOLD        = ENTROPY_SRC_EXTHT_LO_THRESHOLD_OFFSET;
  parameter ADDR_HT_WATERMARK_NUM          = ENTROPY_SRC_HT_WATERMARK_NUM_OFFSET;
  parameter ADDR_HT_WATERMARK              = ENTROPY_SRC_HT_WATERMARK_OFFSET;
  parameter ADDR_REPCNT_TOTAL_FAILS        = ENTROPY_SRC_REPCNT_TOTAL_FAILS_OFFSET;
  parameter ADDR_REPCNTS_TOTAL_FAILS       = ENTROPY_SRC_REPCNTS_TOTAL_FAILS_OFFSET;
  parameter ADDR_ADAPTP_HI_TOTAL_FAILS     = ENTROPY_SRC_ADAPTP_HI_TOTAL_FAILS_OFFSET;
  parameter ADDR_ADAPTP_LO_TOTAL_FAILS     = ENTROPY_SRC_ADAPTP_LO_TOTAL_FAILS_OFFSET;
  parameter ADDR_ADAPTPS_TOTAL_FAILS       = ENTROPY_SRC_ADAPTPS_TOTAL_FAILS_OFFSET;
  parameter ADDR_BUCKET_TOTAL_FAILS        = ENTROPY_SRC_BUCKET_TOTAL_FAILS_OFFSET;
  parameter ADDR_MARKOV_HI_TOTAL_FAILS     = ENTROPY_SRC_MARKOV_HI_TOTAL_FAILS_OFFSET;
  parameter ADDR_MARKOV_LO_TOTAL_FAILS     = ENTROPY_SRC_MARKOV_LO_TOTAL_FAILS_OFFSET;
  parameter ADDR_EXTHT_HI_TOTAL_FAILS      = ENTROPY_SRC_EXTHT_HI_TOTAL_FAILS_OFFSET;
  parameter ADDR_EXTHT_LO_TOTAL_FAILS      = ENTROPY_SRC_EXTHT_LO_TOTAL_FAILS_OFFSET;
  parameter ADDR_ALERT_THRESHOLD           = ENTROPY_SRC_ALERT_THRESHOLD_OFFSET;
  parameter ADDR_ALERT_SUMMARY_FAIL_COUNTS = ENTROPY_SRC_ALERT_SUMMARY_FAIL_COUNTS_OFFSET;
  parameter ADDR_ALERT_FAIL_COUNTS         = ENTROPY_SRC_ALERT_FAIL_COUNTS_OFFSET;
  parameter ADDR_EXTHT_FAIL_COUNTS         = ENTROPY_SRC_EXTHT_FAIL_COUNTS_OFFSET;
  parameter ADDR_FW_OV_CONTROL             = ENTROPY_SRC_FW_OV_CONTROL_OFFSET;
  parameter ADDR_FW_OV_SHA3_START          = ENTROPY_SRC_FW_OV_SHA3_START_OFFSET;
  parameter ADDR_FW_OV_WR_FIFO_FULL        = ENTROPY_SRC_FW_OV_WR_FIFO_FULL_OFFSET;
  parameter ADDR_FW_OV_RD_FIFO_OVERFLOW    = ENTROPY_SRC_FW_OV_RD_FIFO_OVERFLOW_OFFSET;
  parameter ADDR_FW_OV_RD_DATA             = ENTROPY_SRC_FW_OV_RD_DATA_OFFSET;
  parameter ADDR_FW_OV_WR_DATA             = ENTROPY_SRC_FW_OV_WR_DATA_OFFSET;
  parameter ADDR_OBSERVE_FIFO_THRESH       = ENTROPY_SRC_OBSERVE_FIFO_THRESH_OFFSET;
  parameter ADDR_OBSERVE_FIFO_DEPTH        = ENTROPY_SRC_OBSERVE_FIFO_DEPTH_OFFSET;
  parameter ADDR_DEBUG_STATUS              = ENTROPY_SRC_DEBUG_STATUS_OFFSET;
  parameter ADDR_RECOV_ALERT_STS           = ENTROPY_SRC_RECOV_ALERT_STS_OFFSET;
  parameter ADDR_ERR_CODE                  = ENTROPY_SRC_ERR_CODE_OFFSET;
  parameter ADDR_ERR_CODE_TEST             = ENTROPY_SRC_ERR_CODE_TEST_OFFSET;
  parameter ADDR_MAIN_SM_STATE             = ENTROPY_SRC_MAIN_SM_STATE_OFFSET;
  parameter ADDR_ENTROPY_SRC_CTRL          = ENTROPY_SRC_ENTROPY_SRC_CTRL_OFFSET;

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
  logic        zeroize_tb;        // drives debugUnlock_or_scan_mode_switch


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
  logic                 entropy_src_rng_enable;
  logic                 entropy_src_rng_valid;
  logic [3:0]           entropy_src_rng_bits;

  entropy_src #(
    .AHBDataWidth(AHB_DATA_WIDTH),
    .AHBAddrWidth(AHB_ADDR_WIDTH)
  ) dut (
    .clk_i                                (clk_tb),
    .rst_ni                               (reset_n_tb),
    .debugUnlock_or_scan_mode_switch      (zeroize_tb),
    // AMBA AHB Lite Interface
    .haddr_i                              (haddr_i_tb),
    .hwdata_i                             (hwdata_i_tb),
    .hsel_i                               (hsel_i_tb),
    .hwrite_i                             (hwrite_i_tb),
    .hready_i                             (hready_i_tb),
    .htrans_i                             (htrans_i_tb),
    .hsize_i                              (hsize_i_tb),
    .hresp_o                              (hresp_o_tb),
    .hreadyout_o                          (hreadyout_o_tb),
    .hrdata_o                             (hrdata_o_tb),
    // RNG Interface
    .rng_fips_o                           (),
    // Entropy Interface
    .entropy_src_hw_if_i                  (entropy_src_hw_if_req),
    .entropy_src_hw_if_o                  (entropy_src_hw_if_rsp),
    // RNG Interface
    .entropy_src_rng_enable_o             (entropy_src_rng_enable),
    .entropy_src_rng_valid_i              (entropy_src_rng_valid),
    .entropy_src_rng_bits_i               (entropy_src_rng_bits),
    // External Health Test Interface
    .entropy_src_xht_valid_o              (),
    .entropy_src_xht_bits_o               (),
    .entropy_src_xht_bit_sel_o            (),
    .entropy_src_xht_health_test_window_o (),
    .entropy_src_xht_meta_o               (),
    .entropy_src_xht_meta_i               (entropy_src_xht_meta_rsp_t'('0)),
    // Alerts
    .alert_rx_i                           ('0),
    .alert_tx_o                           (),
    // Interrupts
    .intr_es_entropy_valid_o              (),
    .intr_es_health_test_failed_o         (),
    .intr_es_observe_fifo_ready_o         (),
    .intr_es_fatal_err_o                  ()
    );

  physical_rng physical_rng (
    .clk    (clk_tb),
    .enable (entropy_src_rng_enable),
    .data   (entropy_src_rng_bits),
    .valid  (entropy_src_rng_valid)
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
      cycle_ctr = (!reset_n_tb) ? 32'h0 : cycle_ctr + 1;
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
      zeroize_tb   = '0;
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
      @(negedge clk_tb);
      hsel_i_tb       = 1;
      haddr_i_tb      = address;
      hwdata_i_tb     = word;
      hwrite_i_tb     = 1;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hsize_i_tb      = 3'b010;

      // Address phase. Drive and end it on a negedge, so that the DUT samples
      // it on exactly one posedge (changing it in the same time step as the
      // posedge races the DUT).
      @(posedge clk_tb);
      @(negedge clk_tb);
      haddr_i_tb      = 'Z;
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
      @(negedge clk_tb);
      hsel_i_tb       = 1;
      haddr_i_tb      = address;
      hwrite_i_tb     = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hsize_i_tb      = 3'b010;

      // Address phase. Drive and end it on a negedge, so that the DUT samples
      // it on exactly one posedge (changing it in the same time step as the
      // posedge races the DUT).
      @(posedge clk_tb);
      @(negedge clk_tb);
      hwdata_i_tb     = 0;
      haddr_i_tb      = 'Z;
      htrans_i_tb     = AHB_HTRANS_IDLE;

      // Data phase: the read data is valid at the clock edge where hreadyout is high
      do begin
        @(posedge clk_tb);
      end while (hreadyout_o_tb != 1'b1);
      read_data       = hrdata_o_tb;
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
    // 7:4 FIPS_FLAG
    // 11:8 RNG_FIPS
    // 15:12 RNG_BIT_ENABLE
    // 19:16 THRESHOLD_SCOPE
    // 23:20 ENTROPY_DATA_REG_ENABLE
    // 31:24 RNG_BIT_SEL
    // 6 = True, 9 = False
    write_single_word(ADDR_CONF, 32'h00999999);

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
  // Seed checker
  //
  // Count the delivered seeds and check that no seed is all-zero and
  // that each seed differs from the previous one.
  // The zeroize behavior inside entropy_src (no ack in the zeroize
  // cycle, FIFOs and FSMs cleared, noise source undisturbed) is
  // checked by the Zeroize*_A assertions in entropy_src_core.
  //----------------------------------------------------------------
  int                                                    seed_cnt;
  logic [$bits(entropy_src_hw_if_rsp.es_bits)-1:0]       last_seed;

  initial begin
    seed_cnt  = 0;
    last_seed = '0;
    forever begin
      @(posedge clk_tb);
      if (entropy_src_hw_if_rsp.es_ack) begin
        if (entropy_src_hw_if_rsp.es_bits == '0) begin
          $display("[%t] ERROR: all-zero seed delivered", $time);
          error_ctr += 1;
        end
        if (entropy_src_hw_if_rsp.es_bits == last_seed) begin
          $display("[%t] ERROR: seed equal to the previous seed", $time);
          error_ctr += 1;
        end
        last_seed = entropy_src_hw_if_rsp.es_bits;
        seed_cnt += 1;
      end
    end
  end

  //----------------------------------------------------------------
  // zeroize_pulse()
  //
  // Assert debugUnlock_or_scan_mode_switch for the given number of
  // cycles, starting in the current cycle.
  //----------------------------------------------------------------
  task zeroize_pulse(input int cycles);
    zeroize_tb = 1'b1;
    repeat (cycles) @(negedge clk_tb);
    zeroize_tb = 1'b0;
  endtask // zeroize_pulse

  //----------------------------------------------------------------
  // wait_new_seed()
  //
  // Wait until a new seed has been delivered on the hw interface.
  //----------------------------------------------------------------
  task wait_new_seed(input string ctx);
    int start_cnt;
    int ii;
    start_cnt = seed_cnt;
    for (ii = 0; ii < 2_000_000; ii++) begin
      @(posedge clk_tb);
      if (seed_cnt != start_cnt) break;
    end
    if (seed_cnt == start_cnt) begin
      $display("[%t] ERROR: %s: no seed delivered (main SM state = %s)", $time, ctx,
               dut.u_entropy_src_core.u_entropy_src_main_sm.state_q.name());
      error_ctr += 1;
    end
  endtask // wait_new_seed

  //----------------------------------------------------------------
  // check_no_error()
  //
  // Check that the main SM is not in the Error state and that no
  // error has been recorded.
  //----------------------------------------------------------------
  task check_no_error(input string ctx);
    if (dut.u_entropy_src_core.u_entropy_src_main_sm.state_q == entropy_src_main_sm_pkg::Error) begin
      $display("[%t] ERROR: %s: main SM in Error state", $time, ctx);
      error_ctr += 1;
    end
    read_single_word(ADDR_ERR_CODE);
    if (read_data != '0) begin
      $display("[%t] ERROR: %s: ERR_CODE = 0x%x", $time, ctx, read_data);
      error_ctr += 1;
    end
  endtask // check_no_error

  //----------------------------------------------------------------
  // run_bypass_zeroize_test()
  //
  // entropy_src is in boot (bypass) mode and has delivered its seed.
  // Zeroize via ENTROPY_SRC_CTRL or debugUnlock_or_scan_mode_switch.
  // entropy_src restarts and delivers a new boot seed, which must
  // consist of the RNG bits received after the zeroize.
  //----------------------------------------------------------------
  task run_bypass_zeroize_test(input bit use_reg);
    $display("*** Bypass mode zeroize via %s", use_reg ? "ENTROPY_SRC_CTRL" : "pin");
    tc_ctr += 1;

    if (use_reg) begin
      write_single_word(ADDR_ENTROPY_SRC_CTRL, 32'h1);
    end else begin
      @(negedge clk_tb);
      zeroize_pulse(1);
    end

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

    check_no_error("bypass mode zeroize");
  endtask // run_bypass_zeroize_test

  //----------------------------------------------------------------
  // run_fips_zeroize_test()
  //
  // entropy_src runs in FIPS mode and the hw interface keeps
  // requesting seeds. Zeroize via debugUnlock_or_scan_mode_switch in
  // each state of the main SM. After each zeroize, entropy_src must
  // restart on its own and deliver a new seed (no hang). Then zeroize
  // via ENTROPY_SRC_CTRL and with a multi-cycle zeroize.
  //
  // The startup states are only visited right after a (re)start, so
  // they directly follow a zeroize without waiting for a seed in
  // between (wait_seed = 0).
  //----------------------------------------------------------------
  localparam int NumTargets = 9;
  entropy_src_main_sm_pkg::state_e targets [NumTargets] = '{
    entropy_src_main_sm_pkg::Sha3Process,
    entropy_src_main_sm_pkg::Sha3Valid,
    entropy_src_main_sm_pkg::Sha3Done,
    entropy_src_main_sm_pkg::Sha3MsgDone,
    entropy_src_main_sm_pkg::ContHTStart,
    entropy_src_main_sm_pkg::ContHTRunning,
    entropy_src_main_sm_pkg::StartupHTStart,
    entropy_src_main_sm_pkg::StartupPhase1,
    entropy_src_main_sm_pkg::StartupPass1
  };
  bit wait_seed [NumTargets] = '{1, 1, 1, 1, 1, 0, 0, 0, 1};

  task run_fips_zeroize_test;
    int ii;
    int jj;
    $display("*** FIPS mode zeroize");

    // Disable and reconfigure for FIPS mode
    write_single_word(ADDR_MODULE_ENABLE, 32'h9);
    repeat (100) @(posedge clk_tb);
    write_single_word(ADDR_CONF, 32'h00999996);
    // FIPS_WINDOW = 128 samples to keep the sim short, BYPASS_WINDOW = 384 bits
    write_single_word(ADDR_HEALTH_TEST_WINDOWS, 32'h01800080);
    write_single_word(ADDR_MODULE_ENABLE, 32'h6);
    repeat (10) @(posedge clk_tb);

    entropy_src_hw_if_req.es_req = 1;
    wait_new_seed("first FIPS seed");

    // Zeroize in each state of the main SM
    for (ii = 0; ii < NumTargets; ii++) begin
      tc_ctr += 1;
      for (jj = 0; jj < 2_000_000; jj++) begin
        @(negedge clk_tb);
        if (dut.u_entropy_src_core.u_entropy_src_main_sm.state_q == targets[ii]) break;
      end
      if (dut.u_entropy_src_core.u_entropy_src_main_sm.state_q != targets[ii]) begin
        $display("[%t] ERROR: main SM never reached %s", $time, targets[ii].name());
        error_ctr += 1;
      end else begin
        $display("[%t] Zeroize in state %s", $time, targets[ii].name());
        zeroize_pulse(1);
      end
      if (wait_seed[ii]) wait_new_seed(targets[ii].name());
    end

    // Zeroize via ENTROPY_SRC_CTRL while the conditioner is absorbing
    tc_ctr += 1;
    wait (dut.u_entropy_src_core.u_entropy_src_main_sm.state_q ==
          entropy_src_main_sm_pkg::ContHTRunning);
    $display("[%t] Zeroize via ENTROPY_SRC_CTRL", $time);
    write_single_word(ADDR_ENTROPY_SRC_CTRL, 32'h1);
    wait_new_seed("ENTROPY_SRC_CTRL zeroize");

    // Multi-cycle zeroize (e.g. the switch signal stays asserted)
    tc_ctr += 1;
    wait (dut.u_entropy_src_core.u_entropy_src_main_sm.state_q ==
          entropy_src_main_sm_pkg::ContHTRunning);
    $display("[%t] Multi-cycle zeroize", $time);
    @(negedge clk_tb);
    zeroize_pulse(1000);
    wait_new_seed("multi-cycle zeroize");

    @(posedge clk_tb);
    entropy_src_hw_if_req.es_req = 0;
    repeat (1000) @(posedge clk_tb);

    check_no_error("FIPS mode zeroize");
  endtask // run_fips_zeroize_test

  //----------------------------------------------------------------
  // run_ht_fail_fw_ov_zeroize_test()
  //
  // Zeroize in the main SM states that are only reached when the health
  // tests fail (StartupFail1, AlertState, AlertHang) or in firmware
  // override insert mode (FWInsertStart, FWInsertMsg). The default
  // configuration is restored afterwards.
  //----------------------------------------------------------------
  task zeroize_in_state(input entropy_src_main_sm_pkg::state_e state);
    int ii;
    tc_ctr += 1;
    for (ii = 0; ii < 2_000_000; ii++) begin
      @(negedge clk_tb);
      if (dut.u_entropy_src_core.u_entropy_src_main_sm.state_q == state) break;
    end
    if (dut.u_entropy_src_core.u_entropy_src_main_sm.state_q != state) begin
      $display("[%t] ERROR: main SM never reached %s", $time, state.name());
      error_ctr += 1;
    end else begin
      $display("[%t] Zeroize in state %s", $time, state.name());
      zeroize_pulse(1);
    end
  endtask // zeroize_in_state

  task run_ht_fail_fw_ov_zeroize_test;
    $display("*** Zeroize with failing health tests and in firmware override mode");
    entropy_src_hw_if_req.es_req = 0;

    // FIPS mode with an ADAPTP high threshold that every window exceeds. After
    // each zeroize, the startup health tests run and fail again.
    write_single_word(ADDR_MODULE_ENABLE, 32'h9);
    repeat (100) @(posedge clk_tb);
    write_single_word(ADDR_CONF, 32'h00999996);
    write_single_word(ADDR_HEALTH_TEST_WINDOWS, 32'h01800080);
    write_single_word(ADDR_ADAPTP_HI_THRESHOLD, 32'h1);
    write_single_word(ADDR_MODULE_ENABLE, 32'h6);
    zeroize_in_state(entropy_src_main_sm_pkg::StartupFail1);
    zeroize_in_state(entropy_src_main_sm_pkg::AlertState);
    zeroize_in_state(entropy_src_main_sm_pkg::AlertHang);

    // Firmware override insert mode: the main SM waits in FWInsertStart until
    // FW_OV_SHA3_START is set, then moves to FWInsertMsg.
    write_single_word(ADDR_MODULE_ENABLE, 32'h9);
    repeat (100) @(posedge clk_tb);
    write_single_word(ADDR_ADAPTP_HI_THRESHOLD, 32'hFFFF);
    write_single_word(ADDR_FW_OV_CONTROL, 32'h66);  // FW_OV_MODE, FW_OV_ENTROPY_INSERT
    write_single_word(ADDR_MODULE_ENABLE, 32'h6);
    zeroize_in_state(entropy_src_main_sm_pkg::FWInsertStart);
    write_single_word(ADDR_FW_OV_SHA3_START, 32'h6);
    zeroize_in_state(entropy_src_main_sm_pkg::FWInsertMsg);

    // Restore the default configuration
    write_single_word(ADDR_FW_OV_SHA3_START, 32'h9);
    write_single_word(ADDR_MODULE_ENABLE, 32'h9);
    repeat (100) @(posedge clk_tb);
    write_single_word(ADDR_FW_OV_CONTROL, 32'h99);
    check_no_error("health test failure / firmware override zeroize");
  endtask // run_ht_fail_fw_ov_zeroize_test

  //----------------------------------------------------------------
  // Random zeroize
  //
  // In boot-time / bypass mode, entropy_src only delivers one seed per start, so
  // every seed of the random bypass zeroize test is the first seed after a
  // zeroize. It must consist of the first RNG bits received by entropy_src after
  // that zeroize.
  bit bypass_seed_check_en;

  initial begin
    bypass_seed_check_en = 1'b0;
    forever begin
      @(posedge clk_tb);
      if (bypass_seed_check_en && entropy_src_hw_if_rsp.es_ack) begin
        for (int ii = 0; ii < $bits(entropy_src_hw_if_rsp.es_bits)/32; ii += 1) begin
          if (ii >= test_vector_q.size() ||
              entropy_src_hw_if_rsp.es_bits[ii*32+:32] != test_vector_q[ii]) begin
            $display("[%t] ERROR: bypass seed word %0d does not match the RNG bits after the zeroize",
                     $time, ii);
            error_ctr += 1;
          end
        end
      end
    end
  end

  //----------------------------------------------------------------
  // run_random_zeroize_test()
  //
  // Zeroize at random points in FIPS or bypass mode: on entering a randomly
  // chosen main SM state or a random delay later, through the pin (1 or more
  // cycles) or ENTROPY_SRC_CTRL. entropy_src must keep delivering seeds and
  // record no error.
  // Iterations: +ES_RAND_ZEROIZE_ITER=<n> (default 20).
  //----------------------------------------------------------------
  localparam int NumBypassTargets = 3;
  entropy_src_main_sm_pkg::state_e bypass_targets [NumBypassTargets] = '{
    entropy_src_main_sm_pkg::BootHTRunning,
    entropy_src_main_sm_pkg::BootPostHTChk,
    entropy_src_main_sm_pkg::BootPhaseDone
  };

  task run_random_zeroize_test(input bit fips);
    int num_iter;
    int max_delay;
    int delay;
    int src;
    int jj;
    bit seed_pending;
    string ctx;
    entropy_src_main_sm_pkg::state_e target;

    if (!$value$plusargs("ES_RAND_ZEROIZE_ITER=%d", num_iter)) num_iter = 20;
    ctx = fips ? "FIPS mode random zeroize" : "bypass mode random zeroize";
    $display("*** %s (%0d iterations)", ctx, num_iter);

    // Disable and reconfigure. FIPS_WINDOW = 128 samples to keep the sim
    // short, BYPASS_WINDOW = 384 bits.
    entropy_src_hw_if_req.es_req = 0;
    write_single_word(ADDR_MODULE_ENABLE, 32'h9);
    repeat (100) @(posedge clk_tb);
    write_single_word(ADDR_CONF, fips ? 32'h00999996 : 32'h00999999);
    write_single_word(ADDR_HEALTH_TEST_WINDOWS, 32'h01800080);
    write_single_word(ADDR_MODULE_ENABLE, 32'h6);

    // The delays cover a full startup (2 windows in FIPS mode, 1 window in
    // bypass mode) plus some margin.
    max_delay = fips ? 3 * 128 * physical_rng.DutyCycle : 2 * 96 * physical_rng.DutyCycle;

    // In bypass mode, the scoreboard only holds the RNG bits since the last
    // zeroize. Zeroize once before checking any seed against it.
    if (!fips) begin
      @(negedge clk_tb);
      zeroize_pulse(1);
      bypass_seed_check_en = 1'b1;
    end
    entropy_src_hw_if_req.es_req = 1;

    for (int ii = 0; ii < num_iter; ii++) begin
      tc_ctr += 1;
      // Wait for a randomly chosen main SM state, most of which only last a
      // single cycle, and zeroize when entering it (1 of 2 cases), 1-3 cycles
      // later (1 of 4) or at a random point in time later (1 of 4), e.g. in
      // the middle of a long state.
      target = fips ? targets[$urandom_range(NumTargets-1)] :
                      bypass_targets[$urandom_range(NumBypassTargets-1)];
      case ($urandom_range(3))
        0:       delay = $urandom_range(1, 3);
        1:       delay = $urandom_range(max_delay);
        default: delay = 0;
      endcase
      // The startup / boot states are only visited after a restart. If the
      // main SM is already past them, restart it with a zeroize first.
      if (target inside {entropy_src_main_sm_pkg::StartupHTStart,
                         entropy_src_main_sm_pkg::StartupPhase1,
                         entropy_src_main_sm_pkg::StartupPass1,
                         entropy_src_main_sm_pkg::BootHTRunning,
                         entropy_src_main_sm_pkg::BootPostHTChk} &&
          !(dut.u_entropy_src_core.u_entropy_src_main_sm.state_q inside
            {entropy_src_main_sm_pkg::Idle,
             entropy_src_main_sm_pkg::BootHTRunning,
             entropy_src_main_sm_pkg::BootPostHTChk,
             entropy_src_main_sm_pkg::StartupHTStart,
             entropy_src_main_sm_pkg::StartupPhase1,
             entropy_src_main_sm_pkg::StartupPass1,
             entropy_src_main_sm_pkg::StartupFail1})) begin
        @(negedge clk_tb);
        zeroize_pulse(1);
      end
      for (jj = 0; jj < max_delay; jj++) begin
        @(negedge clk_tb);
        if (dut.u_entropy_src_core.u_entropy_src_main_sm.state_q == target) break;
      end
      repeat (delay) @(negedge clk_tb);

      // 0-1: 1-cycle pulse on the pin, 2: multi-cycle pulse, 3: ENTROPY_SRC_CTRL
      // (takes effect a few cycles later, when the write completes)
      src = $urandom_range(3);
      $display("[%t] Random zeroize %0d, %0d cycles after %s%s via %s", $time, ii, delay,
               target.name(), jj < max_delay ? "" : " (not reached)",
               src == 3 ? "ENTROPY_SRC_CTRL" : src == 2 ? "pin (multi-cycle)" : "pin");
      if (src == 3) begin
        write_single_word(ADDR_ENTROPY_SRC_CTRL, 32'h1);
      end else begin
        zeroize_pulse(src == 2 ? $urandom_range(2, 64) : 1);
      end

      seed_pending = 1'b1;
      if ($urandom_range(1) != 0) begin
        wait_new_seed(ctx);
        seed_pending = 1'b0;
      end
    end

    // After the last zeroize, a seed must still be delivered
    if (seed_pending) wait_new_seed(ctx);
    @(posedge clk_tb);
    entropy_src_hw_if_req.es_req = 0;
    bypass_seed_check_en = 1'b0;
    repeat (1000) @(posedge clk_tb);

    check_no_error(ctx);
  endtask // run_random_zeroize_test

  //----------------------------------------------------------------
  // Scoreboard RNG Data
  //----------------------------------------------------------------
  int index;
  logic [AHB_DATA_WIDTH-1:0] test_vector;

  localparam int NUM_RNG_BITS = $bits(entropy_src_rng_bits);
  initial begin
    index = 0;
    test_vector_q = {};

    forever begin
      @(posedge clk_tb)
      // Zeroize drops all the RNG bits held inside entropy_src, including the sample of the
      // zeroize cycle. Restart the scoreboard.
      if (dut.u_entropy_src_core.zeroize) begin
        test_vector_q = {};
        test_vector   = '0;
        index         = 0;
      end else
      // The Physical RNG outputs 4 bits of data.  We collect this in a shift
      // register until we receive 32 bits.  Then append to test_vector_q for
      // easier comparison downstream.
      if (entropy_src_rng_valid) begin
        test_vector >>= NUM_RNG_BITS;
        // Append to MSB
        test_vector[$bits(test_vector) - NUM_RNG_BITS +: NUM_RNG_BITS] = entropy_src_rng_bits;

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
      run_bypass_zeroize_test(.use_reg(1'b1));
      run_bypass_zeroize_test(.use_reg(1'b0));
      run_fips_zeroize_test();
      run_ht_fail_fw_ov_zeroize_test();
      run_random_zeroize_test(.fips(1'b1));
      run_random_zeroize_test(.fips(1'b0));

      display_test_result();

      $display("   -- Testbench for entropy_src done. --");
      $finish;
    end // main
endmodule // entropy_src_tb

//======================================================================
// EOF entropy_src_tb.sv
//======================================================================
