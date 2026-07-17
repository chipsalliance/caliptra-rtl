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
// entropy_combiner_tb.sv
// -----------------------
// Direct (non-UVM) testbench for the SHA3-384 entropy combiner datapath.
//
// Scope: exercises the CSRNG <-> ES0/ES1 entropy_src_hw_if datapath only.
// The AHB/KAT register port is tied off (not exercised) per the task: the
// single goal is to prove that the combiner concatenates the two 384-bit
// entropy_src seeds and returns one 384-bit SHA3-384 digest to CSRNG, i.e.
//
//     csrng_es_bits = SHA3-384( ES0 || ES1 )
//
// Expected digests come from tb/gen_test_vectors.py (hashlib SHA3-384),
// loaded from tb/entropy_combiner_test_vectors.hex.
//
// A bypass sanity case (combine_en_i=0) confirms ES0 is forwarded verbatim.
//
//======================================================================

module entropy_combiner_tb
  import entropy_src_pkg::*;
  ();

  //----------------------------------------------------------------
  // Parameters
  //----------------------------------------------------------------
  localparam int CLK_HALF_PERIOD = 1;
  localparam int SEED_W          = entropy_src_pkg::CSRNG_BUS_WIDTH; // 384

  // Default ES0/ES1 response latencies (cycles from es_req to es_ack). These
  // are runtime-adjustable via es0_latency_tb/es1_latency_tb so the directed
  // handshake tests can skew ES0 vs ES1 arrival order.
  localparam int ES0_LATENCY_DEFAULT = 2;
  localparam int ES1_LATENCY_DEFAULT = 6;

  localparam string DEFAULT_VEC_FILE = "entropy_combiner_test_vectors.hex";

  localparam int MAX_VECTORS = 256;

  //----------------------------------------------------------------
  // Clock / reset
  //----------------------------------------------------------------
  logic clk_tb;
  logic reset_n_tb;
  logic cptra_pwrgood_tb;

  //----------------------------------------------------------------
  // DUT interface signals
  //----------------------------------------------------------------
  entropy_src_hw_if_req_t csrng_req_tb;   // TB  -> DUT
  entropy_src_hw_if_rsp_t csrng_rsp_tb;   // DUT -> TB
  entropy_src_hw_if_req_t es0_req_tb;     // DUT -> ES0 model
  entropy_src_hw_if_rsp_t es0_rsp_tb;     // ES0 model -> DUT
  entropy_src_hw_if_req_t es1_req_tb;     // DUT -> ES1 model
  entropy_src_hw_if_rsp_t es1_rsp_tb;     // ES1 model -> DUT

  logic combine_en_tb;

  // AHB tied off (KAT path intentionally not exercised).
  logic          hresp_tb;
  logic          hreadyout_tb;
  logic [31:0]   hrdata_tb;

  logic error_intr_tb;
  logic notif_intr_tb;
  logic ahb_lock_tb;

  //----------------------------------------------------------------
  // ES model seed data and bookkeeping
  //----------------------------------------------------------------
  logic [SEED_W-1:0] es0_data_tb;
  logic [SEED_W-1:0] es1_data_tb;

  // Runtime-adjustable ES response latencies (see directed handshake tests).
  integer es0_latency_tb;
  integer es1_latency_tb;

  logic [SEED_W-1:0] got_digest;
  logic              got_fips;

  integer error_ctr;
  integer tc_ctr;

  //----------------------------------------------------------------
  // Device Under Test
  //----------------------------------------------------------------
  entropy_combiner #(
    .AHB_DATA_WIDTH(32),
    .AHB_ADDR_WIDTH(32)
  ) dut (
    .clk              (clk_tb),
    .reset_n          (reset_n_tb),
    .cptra_pwrgood_i  (cptra_pwrgood_tb),

    .csrng_hw_if_req_i(csrng_req_tb),
    .csrng_hw_if_rsp_o(csrng_rsp_tb),

    .es0_hw_if_req_o  (es0_req_tb),
    .es0_hw_if_rsp_i  (es0_rsp_tb),
    .es1_hw_if_req_o  (es1_req_tb),
    .es1_hw_if_rsp_i  (es1_rsp_tb),

    .combine_en_i     (combine_en_tb),

    // AHB port unused: quiescent slave inputs.
    .haddr_i          (32'h0),
    .hwdata_i         (32'h0),
    .hsel_i           (1'b0),
    .hwrite_i         (1'b0),
    .hready_i         (1'b1),
    .htrans_i         (2'b00),
    .hsize_i          (3'b000),

    .hresp_o          (hresp_tb),
    .hreadyout_o      (hreadyout_tb),
    .hrdata_o         (hrdata_tb),

    .error_intr_o     (error_intr_tb),
    .notif_intr_o     (notif_intr_tb),
    .ahb_lock_o       (ahb_lock_tb)
  );

  //----------------------------------------------------------------
  // Clock generator
  //----------------------------------------------------------------
  always #CLK_HALF_PERIOD clk_tb = ~clk_tb;

  //----------------------------------------------------------------
  // ES0 responder model
  //
  // Mimics entropy_src_ack_sm: while es_req is asserted, after a fixed
  // latency it pulses es_ack for one cycle with es_bits/es_fips valid.
  // The `acked` flag prevents a second ack for the same held request; it
  // clears once the DUT drops es_req.
  //----------------------------------------------------------------
  integer es0_cnt;
  logic   es0_busy;
  logic   es0_acked;
  always @(posedge clk_tb or negedge reset_n_tb) begin
    if (!reset_n_tb) begin
      es0_rsp_tb.es_ack  <= 1'b0;
      es0_rsp_tb.es_bits <= '0;
      es0_rsp_tb.es_fips <= '0;
      es0_cnt            <= 0;
      es0_busy           <= 1'b0;
      es0_acked          <= 1'b0;
    end else begin
      es0_rsp_tb.es_ack <= 1'b0;
      if (!es0_req_tb.es_req) begin
        es0_busy  <= 1'b0;
        es0_acked <= 1'b0;
        es0_cnt   <= 0;
      end else if (!es0_acked) begin
        if (!es0_busy) begin
          es0_busy <= 1'b1;
          es0_cnt  <= es0_latency_tb;
        end else if (es0_cnt == 0) begin
          es0_rsp_tb.es_ack  <= 1'b1;
          es0_rsp_tb.es_bits <= es0_data_tb;
          es0_rsp_tb.es_fips <= 1'b1;
          es0_acked          <= 1'b1;
          es0_busy           <= 1'b0;
        end else begin
          es0_cnt <= es0_cnt - 1;
        end
      end
    end
  end

  //----------------------------------------------------------------
  // ES1 responder model (same protocol, longer latency)
  //----------------------------------------------------------------
  integer es1_cnt;
  logic   es1_busy;
  logic   es1_acked;
  always @(posedge clk_tb or negedge reset_n_tb) begin
    if (!reset_n_tb) begin
      es1_rsp_tb.es_ack  <= 1'b0;
      es1_rsp_tb.es_bits <= '0;
      es1_rsp_tb.es_fips <= '0;
      es1_cnt            <= 0;
      es1_busy           <= 1'b0;
      es1_acked          <= 1'b0;
    end else begin
      es1_rsp_tb.es_ack <= 1'b0;
      if (!es1_req_tb.es_req) begin
        es1_busy  <= 1'b0;
        es1_acked <= 1'b0;
        es1_cnt   <= 0;
      end else if (!es1_acked) begin
        if (!es1_busy) begin
          es1_busy <= 1'b1;
          es1_cnt  <= es1_latency_tb;
        end else if (es1_cnt == 0) begin
          es1_rsp_tb.es_ack  <= 1'b1;
          es1_rsp_tb.es_bits <= es1_data_tb;
          es1_rsp_tb.es_fips <= 1'b1;
          es1_acked          <= 1'b1;
          es1_busy           <= 1'b0;
        end else begin
          es1_cnt <= es1_cnt - 1;
        end
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

      csrng_req_tb     = '0;
      combine_en_tb    = 1'b0;

      es0_data_tb      = '0;
      es1_data_tb      = '0;

      es0_latency_tb   = ES0_LATENCY_DEFAULT;
      es1_latency_tb   = ES1_LATENCY_DEFAULT;

      got_digest       = '0;
      got_fips         = 1'b0;

      error_ctr        = 0;
      tc_ctr           = 0;
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
      repeat (4) @(negedge clk_tb);
      reset_n_tb       = 1'b1;
      cptra_pwrgood_tb = 1'b1;
      repeat (2) @(negedge clk_tb);
    end
  endtask

  //----------------------------------------------------------------
  // wait_csrng_ack()
  //
  // Waits (sampling on negedge, race-free) for the DUT to present its
  // one-cycle CSRNG ack, capturing the returned es_bits/es_fips.
  //----------------------------------------------------------------
  task wait_csrng_ack;
    integer timeout;
    begin
      timeout    = 0;
      got_digest = '0;
      got_fips   = 1'b0;
      forever begin
        @(negedge clk_tb);
        if (csrng_rsp_tb.es_ack) begin
          got_digest = csrng_rsp_tb.es_bits;
          got_fips   = csrng_rsp_tb.es_fips;
          disable wait_csrng_ack;
        end
        timeout = timeout + 1;
        if (timeout > 2000) begin
          $display("*** ERROR: timeout waiting for CSRNG ack (tc %0d)", tc_ctr);
          error_ctr = error_ctr + 1;
          disable wait_csrng_ack;
        end
      end
    end
  endtask

  //----------------------------------------------------------------
  // run_combine()
  //
  // Combine mode (combine_en strap sampled = 1 at reset): one CSRNG request
  // -> ES0+ES1 seeds -> SHA3-384 digest. The caller is responsible for having
  // strapped combine_en_i=1 before the preceding reset.
  //----------------------------------------------------------------
  task run_combine(input logic [SEED_W-1:0] d0,
                   input logic [SEED_W-1:0] d1,
                   input logic [SEED_W-1:0] exp);
    begin
      @(negedge clk_tb);
      es0_data_tb     = d0;
      es1_data_tb     = d1;
      csrng_req_tb.es_req = 1'b1;

      wait_csrng_ack();

      if (got_digest !== exp) begin
        error_ctr = error_ctr + 1;
        $display("*** [TC %0d] COMBINE MISMATCH", tc_ctr);
        $display("      ES0 = %096h", d0);
        $display("      ES1 = %096h", d1);
        $display("      exp = %096h", exp);
        $display("      got = %096h", got_digest);
      end else if (got_fips !== 1'b1) begin
        error_ctr = error_ctr + 1;
        $display("*** [TC %0d] COMBINE es_fips MISMATCH exp=1 got=%0b (digest ok)",
                 tc_ctr, got_fips);
      end else begin
        $display("    [TC %0d] COMBINE PASS  digest=%096h fips=%0b",
                 tc_ctr, got_digest, got_fips);
      end
      tc_ctr = tc_ctr + 1;

      @(negedge clk_tb);
      csrng_req_tb.es_req = 1'b0;
      // Allow the FSM (comb_ack -> wait_req_low -> idle) to settle.
      repeat (8) @(negedge clk_tb);
    end
  endtask

  //----------------------------------------------------------------
  // run_combine_hold_req()   [directed handshake test 1]
  //
  // Runs one combine, then keeps csrng es_req asserted for `hold_cycles`
  // extra cycles after the ack. Since busy_o is no longer exposed, correct
  // behaviour is proven purely through the entropy_src_hw_if:
  //   (a) exactly ONE ack is produced (the combiner does not re-ack while
  //       req stays high, unlike a bare entropy_src_ack_sm), and
  //   (b) after req finally deasserts, the combiner leaves wait_req_low,
  //       returns to idle, and correctly services a fresh request
  //       (d0b/d1b/expb). A stuck FSM would hang and trip the ack timeout.
  //----------------------------------------------------------------
  task run_combine_hold_req(input logic [SEED_W-1:0] d0,
                            input logic [SEED_W-1:0] d1,
                            input logic [SEED_W-1:0] exp,
                            input integer            hold_cycles,
                            input logic [SEED_W-1:0] d0b,
                            input logic [SEED_W-1:0] d1b,
                            input logic [SEED_W-1:0] expb);
    integer err_at_entry;
    integer extra_acks;
    integer i;
    begin
      err_at_entry = error_ctr;

      @(negedge clk_tb);
      es0_data_tb     = d0;
      es1_data_tb     = d1;
      csrng_req_tb.es_req = 1'b1;

      wait_csrng_ack();
      if (got_digest !== exp) begin
        error_ctr = error_ctr + 1;
        $display("*** [TC %0d] HOLD-REQ digest MISMATCH exp=%096h got=%096h",
                 tc_ctr, exp, got_digest);
      end

      // Keep req asserted; no further ack may appear while it is held high.
      extra_acks = 0;
      for (i = 0; i < hold_cycles; i = i + 1) begin
        @(negedge clk_tb);
        if (csrng_rsp_tb.es_ack) extra_acks = extra_acks + 1;
      end
      if (extra_acks != 0) begin
        error_ctr = error_ctr + 1;
        $display("*** [TC %0d] HOLD-REQ double-ack detected (%0d extra acks)",
                 tc_ctr, extra_acks);
      end

      // Drop req and issue a fresh request; it must complete, proving the
      // combiner left wait_req_low and returned to idle.
      @(negedge clk_tb);
      csrng_req_tb.es_req = 1'b0;
      repeat (2) @(negedge clk_tb);

      es0_data_tb     = d0b;
      es1_data_tb     = d1b;
      @(negedge clk_tb);
      csrng_req_tb.es_req = 1'b1;
      wait_csrng_ack();
      if (got_digest !== expb) begin
        error_ctr = error_ctr + 1;
        $display("*** [TC %0d] HOLD-REQ recovery digest MISMATCH exp=%096h got=%096h",
                 tc_ctr, expb, got_digest);
      end

      @(negedge clk_tb);
      csrng_req_tb.es_req = 1'b0;
      repeat (4) @(negedge clk_tb);

      if (error_ctr == err_at_entry)
        $display("    [TC %0d] HOLD-REQ PASS  single ack under %0d-cyc hold, then recovered",
                 tc_ctr, hold_cycles);
      tc_ctr = tc_ctr + 1;
    end
  endtask

  //----------------------------------------------------------------
  // run_combine_back_to_back()   [directed handshake test 2]
  //
  // Issues two combine requests separated by only a single-cycle req gap.
  // Confirms the combiner finishes request A, observes req low for one cycle
  // (wait_req_low -> idle), then accepts request B without dropping or
  // merging them - each seed pair produces its own correct digest.
  //----------------------------------------------------------------
  task run_combine_back_to_back(input logic [SEED_W-1:0] d0a,
                                input logic [SEED_W-1:0] d1a,
                                input logic [SEED_W-1:0] expa,
                                input logic [SEED_W-1:0] d0b,
                                input logic [SEED_W-1:0] d1b,
                                input logic [SEED_W-1:0] expb);
    integer err_at_entry;
    begin
      err_at_entry = error_ctr;

      // ---- Request A ----
      @(negedge clk_tb);
      es0_data_tb     = d0a;
      es1_data_tb     = d1a;
      csrng_req_tb.es_req = 1'b1;
      wait_csrng_ack();
      if (got_digest !== expa) begin
        error_ctr = error_ctr + 1;
        $display("*** [TC %0d] B2B request A MISMATCH exp=%096h got=%096h",
                 tc_ctr, expa, got_digest);
      end

      // Single-cycle req gap, then request B with new seeds.
      @(negedge clk_tb);
      csrng_req_tb.es_req = 1'b0;
      es0_data_tb     = d0b;
      es1_data_tb     = d1b;
      @(negedge clk_tb);
      csrng_req_tb.es_req = 1'b1;
      wait_csrng_ack();
      if (got_digest !== expb) begin
        error_ctr = error_ctr + 1;
        $display("*** [TC %0d] B2B request B MISMATCH exp=%096h got=%096h",
                 tc_ctr, expb, got_digest);
      end

      @(negedge clk_tb);
      csrng_req_tb.es_req = 1'b0;
      repeat (6) @(negedge clk_tb);

      if (error_ctr == err_at_entry)
        $display("    [TC %0d] B2B PASS  two seeds across a 1-cycle req gap",
                 tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask

  //----------------------------------------------------------------
  // run_bypass()
  //
  // Bypass mode (combine_en strap sampled = 0 at reset): CSRNG request/
  // response is forwarded to/from ES0 only, so the digest returned must equal
  // the ES0 seed verbatim. A non-zero ES1 seed is driven in parallel to prove
  // it has no effect. The caller must have strapped combine_en_i=0 before the
  // preceding reset.
  //----------------------------------------------------------------
  task run_bypass(input logic [SEED_W-1:0] d0,
                  input logic [SEED_W-1:0] d1);
    begin
      @(negedge clk_tb);
      es0_data_tb     = d0;
      es1_data_tb     = d1;   // must not influence the forwarded ES0 response
      csrng_req_tb.es_req = 1'b1;

      wait_csrng_ack();

      if (got_digest !== d0) begin
        error_ctr = error_ctr + 1;
        $display("*** [TC %0d] BYPASS MISMATCH exp=%096h got=%096h (es1=%096h)",
                 tc_ctr, d0, got_digest, d1);
      end else begin
        $display("    [TC %0d] BYPASS  PASS  es0=%096h (es1=%096h ignored)",
                 tc_ctr, got_digest, d1);
      end
      tc_ctr = tc_ctr + 1;

      @(negedge clk_tb);
      csrng_req_tb.es_req = 1'b0;
      repeat (4) @(negedge clk_tb);
    end
  endtask

  //----------------------------------------------------------------
  // display_test_result()
  //----------------------------------------------------------------
  task display_test_result;
    begin
      if (error_ctr == 0) begin
        $display("*** All %0d test cases completed successfully.", tc_ctr);
        $display("* TESTCASE PASSED");
      end else begin
        $display("*** %0d test cases completed.", tc_ctr);
        $display("*** %0d errors detected during testing.", error_ctr);
        $display("* TESTCASE FAILED");
      end
    end
  endtask

  //----------------------------------------------------------------
  // rand384()
  //
  // Builds a 384-bit random value from twelve 32-bit $urandom draws.
  //----------------------------------------------------------------
  function automatic logic [SEED_W-1:0] rand384();
    logic [SEED_W-1:0] r;
    for (int i = 0; i < SEED_W/32; i++)
      r[i*32 +: 32] = $urandom;
    return r;
  endfunction

  //----------------------------------------------------------------
  // Main stimulus
  //----------------------------------------------------------------
  string             vec_file;
  integer            fd;
  integer            scan_ret;
  logic [SEED_W-1:0] v_es0;
  logic [SEED_W-1:0] v_es1;
  logic [SEED_W-1:0] v_exp;

  // Captured reference vectors, reused by the directed handshake tests.
  logic [SEED_W-1:0] es0_arr [MAX_VECTORS];
  logic [SEED_W-1:0] es1_arr [MAX_VECTORS];
  logic [SEED_W-1:0] exp_arr [MAX_VECTORS];
  integer            nvec;
  integer            k;

  initial begin
    init_sim();

    if (!$value$plusargs("VEC_FILE=%s", vec_file))
      vec_file = DEFAULT_VEC_FILE;

    //--------------------------------------------------------------
    // Phase 1 - COMBINE mode.
    // combine_en_i is a static strap sampled once at reset (reset_n
    // deassertion) into COMBINER_STATUS via the one-shot combine_en_strap_we.
    // Drive the strap value BEFORE reset and keep it stable for the phase.
    //--------------------------------------------------------------
    combine_en_tb = 1'b1;
    reset_dut();

    fd = $fopen(vec_file, "r");
    if (fd == 0) begin
      $display("*** ERROR: cannot open vector file '%s'", vec_file);
      $display("* TESTCASE FAILED");
      $finish;
    end
    $display("*** [combine strap=1] Loading combine vectors from '%s'", vec_file);

    // Load reference vectors into arrays, running a basic combine on each.
    nvec = 0;
    while (!$feof(fd) && (nvec < MAX_VECTORS)) begin
      scan_ret = $fscanf(fd, "%h %h %h\n", v_es0, v_es1, v_exp);
      if (scan_ret == 3) begin
        es0_arr[nvec] = v_es0;
        es1_arr[nvec] = v_es1;
        exp_arr[nvec] = v_exp;
        nvec = nvec + 1;
        run_combine(v_es0, v_es1, v_exp);
      end
    end
    $fclose(fd);

    if (nvec < 4) begin
      $display("*** ERROR: need >=4 vectors for directed handshake tests (got %0d)",
               nvec);
      error_ctr = error_ctr + 1;
    end else begin
      //------------------------------------------------------------
      // Directed handshake test 1 - held csrng es_req after ack.
      // CSRNG normally drops req 1 cycle after ack; here we hold it high
      // for many cycles to prove no double-ack and no early idle return.
      //------------------------------------------------------------
      $display("*** [handshake] Test 1: held es_req (no double-ack, then recovers)");
      run_combine_hold_req(es0_arr[0], es1_arr[0], exp_arr[0], 12,
                           es0_arr[3], es1_arr[3], exp_arr[3]);

      //------------------------------------------------------------
      // Directed handshake test 2 - back-to-back requests, 1-cycle gap.
      //------------------------------------------------------------
      $display("*** [handshake] Test 2: back-to-back combine requests");
      run_combine_back_to_back(es0_arr[1], es1_arr[1], exp_arr[1],
                               es0_arr[2], es1_arr[2], exp_arr[2]);

      //------------------------------------------------------------
      // Directed handshake test 3 - ES0/ES1 arrival-order skew.
      // Same-cycle acks, then ES1-late, then ES0-late; the combiner must
      // wait for BOTH seeds regardless of order and still produce the
      // correct digest.
      //------------------------------------------------------------
      $display("*** [handshake] Test 3: ES0/ES1 latency skew (simultaneous, ES1-late, ES0-late)");
      es0_latency_tb = 3;  es1_latency_tb = 3;   // simultaneous acks
      run_combine(es0_arr[0], es1_arr[0], exp_arr[0]);
      es0_latency_tb = 1;  es1_latency_tb = 15;  // ES1 arrives much later
      run_combine(es0_arr[1], es1_arr[1], exp_arr[1]);
      es0_latency_tb = 15; es1_latency_tb = 1;   // ES0 arrives much later
      run_combine(es0_arr[2], es1_arr[2], exp_arr[2]);
      es0_latency_tb = ES0_LATENCY_DEFAULT;
      es1_latency_tb = ES1_LATENCY_DEFAULT;
    end

    //--------------------------------------------------------------
    // Phase 2 - BYPASS mode.
    // Re-strap combine_en_i=0 across a fresh reset so the new value is
    // sampled. ES0 must be forwarded verbatim regardless of ES1; drive
    // random ES0/ES1 directly (expected result is simply ES0), plus an
    // explicit ES0=0 / ES1!=0 case to prove ES1 never leaks through.
    //--------------------------------------------------------------
    combine_en_tb = 1'b0;
    reset_dut();
    $display("*** [bypass strap=0] Running bypass forwarding checks");

    run_bypass('0, rand384());
    for (k = 0; k < 8; k = k + 1)
      run_bypass(rand384(), rand384());

    display_test_result();
    $finish;
  end

  //----------------------------------------------------------------
  // Global watchdog
  //----------------------------------------------------------------
  initial begin
    #2_000_000;
    $display("*** ERROR: global simulation timeout.");
    $display("* TESTCASE FAILED");
    $finish;
  end

endmodule
