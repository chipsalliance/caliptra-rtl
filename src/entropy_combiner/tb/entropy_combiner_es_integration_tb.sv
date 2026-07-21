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
// entropy_combiner_es_integration_tb.sv
// -------------------------------------
// Integration testbench: two REAL entropy_src IPs feeding the entropy
// combiner, with the raw noise driven through each entropy_src's itrng
// (rng_b / rng_valid) interface via the physical_rng simulation model.
//
// Topology:
//     physical_rng(IS0) --itrng--> entropy_src ES0 --es_hw_if--> combiner es0
//     physical_rng(IS1) --itrng--> entropy_src ES1 --es_hw_if--> combiner es1
//     TB (CSRNG role) --csrng_hw_if--> combiner --> 384b SHA3-384 digest
//
// Both entropy_src instances are AHB-configured for RAW/BYPASS output
// (CONF=0x2649999: FIPS/conditioner disabled, RNG_BIT_ENABLE=false), exactly
// like src/entropy_src/tb/entropy_src_tb.sv. In this mode entropy_src streams
// the raw 4-bit itrng nibbles straight into es_bits, and the nibble packing is
// an identity map, so es_bits == physical_rng InitialSeed for the first 384-bit
// seed. That makes the whole datapath deterministic:
//
//     ES0 seed = IS0,  ES1 seed = IS1,  digest = SHA3-384(IS0 || IS1)
//
// The expected digest is precomputed offline (tb/gen_test_vectors.py model).
// The TB also snoops the seeds each entropy_src actually delivers to the
// combiner and checks them against IS0/IS1, so a packing/config mismatch is
// diagnosed directly rather than only showing up as a digest miss.
//
// Only one deterministic combine is checked: physical_rng emits InitialSeed
// for the first 384 bits and $urandom thereafter, so a second seed would not
// be predictable.
//
//======================================================================

module entropy_combiner_es_integration_tb
  import entropy_src_pkg::*;
  ();

  //----------------------------------------------------------------
  // Parameters
  //----------------------------------------------------------------
  localparam int CLK_HALF_PERIOD = 2;
  localparam int SEED_W          = entropy_src_pkg::CSRNG_BUS_WIDTH; // 384
  localparam int ES_AHB_ADDR_W   = 32;
  localparam int ES_AHB_DATA_W   = 32;
  // Fast itrng pacing for simulation (physical_rng default 500 models a slow
  // hw source; the combine result is independent of the rate).
  localparam int RNG_DUTY_CYCLE  = 4;

  // itrng InitialSeeds. In the bypass config es_bits == InitialSeed.
  // IS0 is physical_rng's default (proven health-test-friendly in
  // entropy_src_tb); IS1 is a distinct well-mixed value.
  localparam logic [SEED_W-1:0] IS0 =
    384'h33f63b65f57ad68765693560e743cc5010518e4bf4ecbeba71dc56aaa08b394311731d9df763fc5d27e4ed3e4b7de947;
  localparam logic [SEED_W-1:0] IS1 =
    384'h9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e9587f9e1a34b2d0c7658493a1fbe6d2c0a;
  // Precomputed: SHA3-384(IS0 || IS1) in the combiner's little-endian byte order.
  localparam logic [SEED_W-1:0] EXP_DIGEST =
    384'hd5137041d197084214e3d6e04ed17ca7264825e7f707961a45184d1b0be62b48bdfce4d0ae18be5c42c8e0169c387d16;

  // entropy_src register offsets and values (see entropy_src_tb.sv).
  localparam logic [31:0] ADDR_MODULE_ENABLE = 32'h20;
  localparam logic [31:0] ADDR_CONF          = 32'h24;
  localparam logic [31:0] CONF_RAW_BYPASS    = 32'h2649999; // FIPS off, 4-bit mode
  localparam logic [31:0] MODULE_ENABLE_ON   = 32'h6;

  localparam logic [1:0] AHB_HTRANS_IDLE   = 2'h0;
  localparam logic [1:0] AHB_HTRANS_NONSEQ = 2'h2;

  //----------------------------------------------------------------
  // Clock / reset
  //----------------------------------------------------------------
  logic clk_tb;
  logic reset_n_tb;
  logic cptra_pwrgood_tb;

  //----------------------------------------------------------------
  // Shared entropy_src AHB config bus (both ES configured identically)
  //----------------------------------------------------------------
  logic [ES_AHB_ADDR_W-1:0] es_haddr;
  logic [ES_AHB_DATA_W-1:0] es_hwdata;
  logic                     es_hsel;
  logic                     es_hwrite;
  logic                     es_hready;
  logic [1:0]               es_htrans;
  logic [2:0]               es_hsize;

  logic                     es0_hresp, es0_hreadyout;
  logic [ES_AHB_DATA_W-1:0] es0_hrdata;
  logic                     es1_hresp, es1_hreadyout;
  logic [ES_AHB_DATA_W-1:0] es1_hrdata;

  //----------------------------------------------------------------
  // entropy_src_hw_if between combiner and the two entropy_src IPs
  //----------------------------------------------------------------
  entropy_src_hw_if_req_t es0_hw_req;   // combiner -> ES0
  entropy_src_hw_if_rsp_t es0_hw_rsp;   // ES0      -> combiner
  entropy_src_hw_if_req_t es1_hw_req;   // combiner -> ES1
  entropy_src_hw_if_rsp_t es1_hw_rsp;   // ES1      -> combiner

  //----------------------------------------------------------------
  // itrng interface between entropy_src and physical_rng
  //----------------------------------------------------------------
  entropy_src_rng_req_t es0_rng_req;    // ES0 -> rng (rng_enable)
  entropy_src_rng_rsp_t es0_rng_rsp;    // rng -> ES0 (rng_b/rng_valid)
  entropy_src_rng_req_t es1_rng_req;
  entropy_src_rng_rsp_t es1_rng_rsp;

  //----------------------------------------------------------------
  // Combiner CSRNG-facing side (TB plays CSRNG) + tie-offs
  //----------------------------------------------------------------
  entropy_src_hw_if_req_t csrng_req;
  entropy_src_hw_if_rsp_t csrng_rsp;
  logic                   combine_en_tb;

  logic          comb_hresp, comb_hreadyout;
  logic [31:0]   comb_hrdata;
  logic          comb_error_intr, comb_notif_intr, comb_ahb_lock;

  //----------------------------------------------------------------
  // Bookkeeping / snoop / timing control
  //----------------------------------------------------------------
  integer            error_ctr, tc_ctr;
  logic [SEED_W-1:0] got_digest;
  logic              got_fips;
  logic [SEED_W-1:0] es0_seed_seen, es1_seed_seen;
  logic              es0_seen, es1_seen;

  // TB-controlled itrng start gates: hold a source idle to delay when its
  // entropy_src produces a seed, stressing ES0-vs-ES1 arrival misalignment.
  logic rng0_go, rng1_go;

  // Ack-cycle timestamps (reset per case) to prove the combiner waits for both.
  integer cycle_ctr;
  integer es0_ack_cyc, es1_ack_cyc, csrng_ack_cyc;

  //----------------------------------------------------------------
  // DUT: entropy combiner (combine mode)
  //----------------------------------------------------------------
  entropy_combiner #(
    .AHB_DATA_WIDTH(32),
    .AHB_ADDR_WIDTH(32)
  ) u_combiner (
    .clk              (clk_tb),
    .reset_n          (reset_n_tb),
    .cptra_pwrgood_i  (cptra_pwrgood_tb),

    .csrng_hw_if_req_i(csrng_req),
    .csrng_hw_if_rsp_o(csrng_rsp),

    .es0_hw_if_req_o  (es0_hw_req),
    .es0_hw_if_rsp_i  (es0_hw_rsp),
    .es1_hw_if_req_o  (es1_hw_req),
    .es1_hw_if_rsp_i  (es1_hw_rsp),

    .combine_en_i     (combine_en_tb),

    // Combiner AHB (KAT) port unused here.
    .haddr_i          (32'h0),
    .hwdata_i         (32'h0),
    .hsel_i           (1'b0),
    .hwrite_i         (1'b0),
    .hready_i         (1'b1),
    .htrans_i         (2'b00),
    .hsize_i          (3'b000),
    .hresp_o          (comb_hresp),
    .hreadyout_o      (comb_hreadyout),
    .hrdata_o         (comb_hrdata),

    .error_intr_o     (comb_error_intr),
    .notif_intr_o     (comb_notif_intr),
    .ahb_lock_o       (comb_ahb_lock)
  );

  //----------------------------------------------------------------
  // Real entropy_src IP #0 (primary), via the RTL wrapper that ties off the
  // MuBi enable straps and other unused interfaces inside the design partition.
  //----------------------------------------------------------------
  entropy_src_raw_wrap #(
    .AHBDataWidth(ES_AHB_DATA_W),
    .AHBAddrWidth(ES_AHB_ADDR_W)
  ) u_es0 (
    .clk_i               (clk_tb),
    .rst_ni              (reset_n_tb),
    .haddr_i             (es_haddr),
    .hwdata_i            (es_hwdata),
    .hsel_i              (es_hsel),
    .hwrite_i            (es_hwrite),
    .hready_i            (es_hready),
    .htrans_i            (es_htrans),
    .hsize_i             (es_hsize),
    .hresp_o             (es0_hresp),
    .hreadyout_o         (es0_hreadyout),
    .hrdata_o            (es0_hrdata),
    .entropy_src_hw_if_i (es0_hw_req),
    .entropy_src_hw_if_o (es0_hw_rsp),
    .entropy_src_rng_o   (es0_rng_req),
    .entropy_src_rng_i   (es0_rng_rsp)
  );

  //----------------------------------------------------------------
  // Real entropy_src IP #1 (secondary), via the same RTL wrapper.
  //----------------------------------------------------------------
  entropy_src_raw_wrap #(
    .AHBDataWidth(ES_AHB_DATA_W),
    .AHBAddrWidth(ES_AHB_ADDR_W)
  ) u_es1 (
    .clk_i               (clk_tb),
    .rst_ni              (reset_n_tb),
    .haddr_i             (es_haddr),
    .hwdata_i            (es_hwdata),
    .hsel_i              (es_hsel),
    .hwrite_i            (es_hwrite),
    .hready_i            (es_hready),
    .htrans_i            (es_htrans),
    .hsize_i             (es_hsize),
    .hresp_o             (es1_hresp),
    .hreadyout_o         (es1_hreadyout),
    .hrdata_o            (es1_hrdata),
    .entropy_src_hw_if_i (es1_hw_req),
    .entropy_src_hw_if_o (es1_hw_rsp),
    .entropy_src_rng_o   (es1_rng_req),
    .entropy_src_rng_i   (es1_rng_rsp)
  );

  //----------------------------------------------------------------
  // itrng sources: deterministic InitialSeed for the first 384 bits.
  //----------------------------------------------------------------
  physical_rng #(
    .UseInitialSeed(1'b1),
    .InitialSeed   (IS0),
    .DutyCycle     (RNG_DUTY_CYCLE)
  ) u_rng0 (
    .clk    (clk_tb),
    .enable (es0_rng_req.rng_enable & rng0_go),
    .data   (es0_rng_rsp.rng_b),
    .valid  (es0_rng_rsp.rng_valid)
  );

  physical_rng #(
    .UseInitialSeed(1'b1),
    .InitialSeed   (IS1),
    .DutyCycle     (RNG_DUTY_CYCLE)
  ) u_rng1 (
    .clk    (clk_tb),
    .enable (es1_rng_req.rng_enable & rng1_go),
    .data   (es1_rng_rsp.rng_b),
    .valid  (es1_rng_rsp.rng_valid)
  );

  //----------------------------------------------------------------
  // Clock
  //----------------------------------------------------------------
  always #CLK_HALF_PERIOD clk_tb = ~clk_tb;

  //----------------------------------------------------------------
  // Snoop the seed each entropy_src delivers, and timestamp the ES/CSRNG
  // acks (relative to the per-case reset) to check arrival ordering.
  //
  // entropy_src es_ack and the combiner csrng ack are one-cycle COMBINATIONAL
  // pulses, so they are sampled on the negedge (mid-cycle, stable) to avoid a
  // posedge race. cycle_ctr is a posedge counter, stable when read at negedge.
  //----------------------------------------------------------------
  always @(posedge clk_tb or negedge reset_n_tb) begin
    if (!reset_n_tb) cycle_ctr <= 0;
    else             cycle_ctr <= cycle_ctr + 1;
  end

  always @(negedge clk_tb or negedge reset_n_tb) begin
    if (!reset_n_tb) begin
      es0_seen      <= 1'b0;
      es1_seen      <= 1'b0;
      es0_seed_seen <= '0;
      es1_seed_seen <= '0;
      es0_ack_cyc   <= -1;
      es1_ack_cyc   <= -1;
    end else begin
      if (es0_hw_rsp.es_ack && !es0_seen) begin
        es0_seed_seen <= es0_hw_rsp.es_bits;
        es0_seen      <= 1'b1;
        es0_ack_cyc   <= cycle_ctr;
      end
      if (es1_hw_rsp.es_ack && !es1_seen) begin
        es1_seed_seen <= es1_hw_rsp.es_bits;
        es1_seen      <= 1'b1;
        es1_ack_cyc   <= cycle_ctr;
      end
    end
  end

  //----------------------------------------------------------------
  // init_sim()
  //----------------------------------------------------------------
  task init_sim;
    begin
      clk_tb           = 1'b0;
      reset_n_tb       = 1'b0;
      cptra_pwrgood_tb = 1'b0;

      es_haddr         = '0;
      es_hwdata        = '0;
      es_hsel          = 1'b0;
      es_hwrite        = 1'b0;
      es_hready        = 1'b1;
      es_htrans        = AHB_HTRANS_IDLE;
      es_hsize         = 3'b010;

      csrng_req        = '0;
      combine_en_tb    = 1'b0;

      rng0_go          = 1'b0;
      rng1_go          = 1'b0;

      error_ctr        = 0;
      tc_ctr           = 0;
      got_digest       = '0;
      got_fips         = 1'b0;
      csrng_ack_cyc    = -1;
    end
  endtask

  //----------------------------------------------------------------
  // reset_dut()
  //----------------------------------------------------------------
  task reset_dut;
    begin
      $display("*** Toggle reset.");
      reset_n_tb       = 1'b0;
      cptra_pwrgood_tb = 1'b0;
      repeat (5) @(posedge clk_tb);
      reset_n_tb       = 1'b1;
      cptra_pwrgood_tb = 1'b1;
      repeat (2) @(posedge clk_tb);
    end
  endtask

  //----------------------------------------------------------------
  // write_es() - AHB write to BOTH entropy_src (shared config bus).
  //----------------------------------------------------------------
  task write_es(input logic [31:0] address, input logic [31:0] word);
    begin
      $display("[%0t] write_es(addr=0x%08x, data=0x%08x)", $time, address, word);
      es_hsel   = 1'b1;
      es_haddr  = address;
      es_hwdata = word;
      es_hwrite = 1'b1;
      es_hready = 1'b1;
      es_htrans = AHB_HTRANS_NONSEQ;
      es_hsize  = 3'b010;

      @(posedge clk_tb);
      es_haddr  = 'z;
      es_hwrite = 1'b0;
      es_htrans = AHB_HTRANS_IDLE;
      wait (es0_hreadyout == 1'b1 && es1_hreadyout == 1'b1);

      @(posedge clk_tb);
      es_hsel   = 1'b0;
    end
  endtask

  //----------------------------------------------------------------
  // configure_es() - raw/bypass mode + enable, for both entropy_src.
  //----------------------------------------------------------------
  task configure_es;
    begin
      write_es(ADDR_CONF, CONF_RAW_BYPASS);
      write_es(ADDR_MODULE_ENABLE, MODULE_ENABLE_ON);
    end
  endtask

  //----------------------------------------------------------------
  // wait_combiner_ack() - entropy production is slow, so allow a big budget.
  //----------------------------------------------------------------
  task wait_combiner_ack;
    integer timeout;
    begin
      timeout    = 0;
      got_digest = '0;
      got_fips   = 1'b0;
      forever begin
        @(negedge clk_tb);
        if (csrng_rsp.es_ack) begin
          got_digest    = csrng_rsp.es_bits;
          got_fips      = csrng_rsp.es_fips;
          csrng_ack_cyc = cycle_ctr;   // capture cleanly (comb ack, race-free at negedge)
          disable wait_combiner_ack;
        end
        timeout = timeout + 1;
        if (timeout > 2_000_000) begin
          $display("*** ERROR: timeout waiting for combiner CSRNG ack");
          error_ctr = error_ctr + 1;
          disable wait_combiner_ack;
        end
      end
    end
  endtask

  //----------------------------------------------------------------
  // display_test_result()
  //----------------------------------------------------------------
  task display_test_result;
    begin
      if (error_ctr == 0) begin
        $display("*** All %0d checks completed successfully.", tc_ctr);
        $display("* TESTCASE PASSED");
      end else begin
        $display("*** %0d checks completed.", tc_ctr);
        $display("*** %0d errors detected during testing.", error_ctr);
        $display("* TESTCASE FAILED");
      end
    end
  endtask

  //----------------------------------------------------------------
  // run_case() - one deterministic combine with a controlled ES0/ES1
  // arrival skew. es{0,1}_delay = cycles each itrng source is held idle
  // (after the CSRNG request) before it starts streaming its InitialSeed.
  // A full reset precedes each case so both seeds are the deterministic
  // InitialSeed again (physical_rng re-arms while its enable is low).
  //----------------------------------------------------------------
  task run_case(input integer es0_delay,
                input integer es1_delay,
                input string  tag);
    integer err_at_entry;
    begin
      err_at_entry = error_ctr;

      // Hold both itrng sources idle, reset, then bring both ES up. With the
      // sources gated, neither entropy_src collects until released below.
      rng0_go = 1'b0;
      rng1_go = 1'b0;
      reset_dut();
      repeat (50) @(posedge clk_tb);
      configure_es();
      repeat (20) @(posedge clk_tb);

      // Start the combine, then release the sources with the requested skew
      // (one delay is always 0, so this stays sequential).
      @(negedge clk_tb);
      csrng_req.es_req = 1'b1;
      if (es0_delay <= es1_delay) begin
        rng0_go = 1'b1;
        repeat (es1_delay - es0_delay) @(posedge clk_tb);
        rng1_go = 1'b1;
      end else begin
        rng1_go = 1'b1;
        repeat (es0_delay - es1_delay) @(posedge clk_tb);
        rng0_go = 1'b1;
      end

      wait_combiner_ack();

      // Seeds are deterministic regardless of arrival timing.
      if (!es0_seen || (es0_seed_seen !== IS0)) begin
        error_ctr = error_ctr + 1;
        $display("*** [%s] ES0 seed MISMATCH seen=%0b got=%096h", tag, es0_seen, es0_seed_seen);
      end
      if (!es1_seen || (es1_seed_seen !== IS1)) begin
        error_ctr = error_ctr + 1;
        $display("*** [%s] ES1 seed MISMATCH seen=%0b got=%096h", tag, es1_seen, es1_seed_seen);
      end
      // Digest is order-independent: SHA3-384(IS0 || IS1).
      if (got_digest !== EXP_DIGEST) begin
        error_ctr = error_ctr + 1;
        $display("*** [%s] DIGEST MISMATCH", tag);
        $display("      exp = %096h", EXP_DIGEST);
        $display("      got = %096h", got_digest);
      end
      if (got_fips !== 1'b0) begin
        error_ctr = error_ctr + 1;
        $display("*** [%s] es_fips expected 0 (raw mode) got %0b", tag, got_fips);
      end
      // The combiner must ack only after BOTH ES seeds arrived.
      if (!((csrng_ack_cyc > es0_ack_cyc) && (csrng_ack_cyc > es1_ack_cyc))) begin
        error_ctr = error_ctr + 1;
        $display("*** [%s] ORDER VIOLATION es0@%0d es1@%0d csrng@%0d",
                 tag, es0_ack_cyc, es1_ack_cyc, csrng_ack_cyc);
      end

      if (error_ctr == err_at_entry)
        $display("    [TC %0d] %-16s PASS  es0@%0d es1@%0d csrng@%0d  digest OK",
                 tc_ctr, tag, es0_ack_cyc, es1_ack_cyc, csrng_ack_cyc);
      tc_ctr = tc_ctr + 1;

      @(negedge clk_tb);
      csrng_req.es_req = 1'b0;
      repeat (10) @(posedge clk_tb);
    end
  endtask

  //----------------------------------------------------------------
  // Main - re-run the same deterministic combine under several ES0/ES1
  // arrival-timing skews.
  //----------------------------------------------------------------
  initial begin
    init_sim();

    // combine_en_i strap = 1; re-sampled by each per-case reset in run_case.
    combine_en_tb = 1'b1;

    $display("*** [integration] Dual entropy_src -> combiner, itrng-driven, timing sweep");
    run_case(0,   0,   "simultaneous");
    run_case(0,   120, "ES0-first-small");
    run_case(120, 0,   "ES1-first-small");
    run_case(0,   600, "ES0-first-large");
    run_case(600, 0,   "ES1-first-large");

    display_test_result();
    $finish;
  end

  //----------------------------------------------------------------
  // Global watchdog
  //----------------------------------------------------------------
  initial begin
    #80_000_000;
    $display("*** ERROR: global simulation timeout.");
    $display("* TESTCASE FAILED");
    $finish;
  end

endmodule
