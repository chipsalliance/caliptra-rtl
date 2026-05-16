// SPDX-License-Identifier: Apache-2.0
//
// ecc_fau_dualcurve_smoke_tb.sv
// -----------------------------
// Standalone smoke test for `ecc_fau` driven by the same prime/mu mux
// expression as `ecc_arith_unit` (lines 142-145), sweeping all four
// (curve_sel_i, mod_p_q) corners. This closes the verification gap
// for the per-curve FAU constants:
//
//   - PRIME_P256 / PRIME_P384       on adder_prime selector
//   - GROUP_ORDER_P256 / _P384      on adder_prime selector
//   - PRIME_mu_P256 / _P384         on mult_mu selector
//   - GROUP_ORDER_mu_P256 / _P384   on mult_mu selector
//
// Coverage:
//   1) Directed identity checks per (curve, mod) corner using the Mont
//      constants from ecc_params_pkg.
//   2) Random Montgomery multiplications, comparing against an SV
//      software FIOS reference.
//   3) Modular add/sub edge cases: 0+1, (m-1)+1==0, 0-1==m-1, plus
//      random opa+opb mod m / opa-opb mod m for all four corners.
//
// Hierarchical refs are used into the FAU subblocks to observe the
// internal `ready_o` strobes (the FAU itself does not export them).
//
// Pass criterion: zero errors out of all directed + random checks.

`default_nettype none

module ecc_fau_dualcurve_smoke_tb;
  import ecc_params_pkg::*;

  localparam int REG = 384;
  localparam int RAD = MULT_RADIX;   // 48
  localparam int N_RAND_PER_CORNER = 10;

  logic                clk;
  logic                reset_n;

  logic                add_en;
  logic                sub_sel;
  logic                mult_en;
  logic [REG-1:0]      prime;
  logic [RAD-1:0]      mu;
  logic [REG-1:0]      opa;
  logic [REG-1:0]      opb;
  logic [REG-1:0]      add_res;
  logic [REG-1:0]      mult_res;

  initial clk = 1'b0;
  always #5 clk = ~clk;

  // -----------------------------------------------------------------
  // DUT
  // -----------------------------------------------------------------
  ecc_fau #(
    .REG_SIZE(REG),
    .RADIX  (RAD)
  ) dut (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(1'b0),
    .add_en_i (add_en),
    .sub_i    (sub_sel),
    .mult_en_i(mult_en),
    .prime_i  (prime),
    .mult_mu_i(mu),
    .opa_i    (opa),
    .opb_i    (opb),
    .add_res_o (add_res),
    .mult_res_o(mult_res)
  );

  // Hierarchical refs to the internal ready strobes (FAU hides them).
  wire mult_ready = dut.i_MULTIPLIER.ready_o;
  wire add_ready  = dut.i_ADDER_SUBTRACTOR.ready_o;

  int errors;
  int trials;

  // -----------------------------------------------------------------
  // PRIME / MU MUX — must mirror ecc_arith_unit.sv lines 142-145.
  // If that file is changed, change here too (and vice versa).
  // -----------------------------------------------------------------
  function automatic [REG-1:0] sel_prime(input bit curve_sel, input bit mod_p_q);
    if (mod_p_q)
      sel_prime = curve_sel ? GROUP_ORDER_P256 : GROUP_ORDER_P384;
    else
      sel_prime = curve_sel ? PRIME_P256       : PRIME_P384;
  endfunction

  function automatic [RAD-1:0] sel_mu(input bit curve_sel, input bit mod_p_q);
    if (mod_p_q)
      sel_mu = curve_sel ? GROUP_ORDER_mu_P256 : GROUP_ORDER_mu_P384;
    else
      sel_mu = curve_sel ? PRIME_mu_P256       : PRIME_mu_P384;
  endfunction

  // -----------------------------------------------------------------
  // SW Montgomery reference, R = 2^(9*48) = 2^432 (see montmul header)
  // -----------------------------------------------------------------
  function automatic [REG-1:0] ref_montmul(
      input [REG-1:0] a,
      input [REG-1:0] b,
      input [REG-1:0] n,
      input [RAD-1:0] n_prime
  );
    logic [2*REG+RAD-1:0] t;
    logic [RAD-1:0]       m_chunk;
    logic [REG+RAD-1:0]   add_term;
    int i;
    begin
      t = a * b;
      for (i = 0; i < 9; i++) begin
        m_chunk  = t[RAD-1:0] * n_prime;
        add_term = m_chunk * n;
        t        = (t + add_term) >> RAD;
      end
      if (t >= n) t = t - n;
      ref_montmul = t[REG-1:0];
    end
  endfunction

  // -----------------------------------------------------------------
  // DUT drivers
  // -----------------------------------------------------------------
  task automatic do_mult(
      input  [REG-1:0] a,
      input  [REG-1:0] b,
      input  [REG-1:0] n,
      input  [RAD-1:0] n_prime,
      output [REG-1:0] r
  );
    int wait_count;
    begin
      @(posedge clk);
      opa     <= a;
      opb     <= b;
      prime   <= n;
      mu      <= n_prime;
      mult_en <= 1'b1;
      @(posedge clk);
      mult_en <= 1'b0;
      // Wait for ready_o pulse with a generous timeout.
      wait_count = 0;
      @(posedge clk);
      while (mult_ready == 1'b0 && wait_count < 200) begin
        @(posedge clk);
        wait_count++;
      end
      r = mult_res;
    end
  endtask

  // 'do_sub_in' selects add (0) or sub (1).
  task automatic do_addsub(
      input  bit       do_sub,
      input  [REG-1:0] a,
      input  [REG-1:0] b,
      input  [REG-1:0] n,
      output [REG-1:0] r
  );
    int wait_count;
    begin
      @(posedge clk);
      opa     <= a;
      opb     <= b;
      prime   <= n;
      sub_sel <= do_sub;
      add_en  <= 1'b1;
      @(posedge clk);
      add_en  <= 1'b0;
      wait_count = 0;
      @(posedge clk);
      while (add_ready == 1'b0 && wait_count < 50) begin
        @(posedge clk);
        wait_count++;
      end
      r = add_res;
    end
  endtask

  // -----------------------------------------------------------------
  // Generic check helpers
  // -----------------------------------------------------------------
  task automatic check_mult(
      input string    label,
      input bit       curve_sel,
      input bit       mod_p_q,
      input [REG-1:0] a,
      input [REG-1:0] b,
      input [REG-1:0] expected
  );
    logic [REG-1:0] hw;
    logic [REG-1:0] n;
    logic [RAD-1:0] n_prime;
    begin
      n       = sel_prime(curve_sel, mod_p_q);
      n_prime = sel_mu   (curve_sel, mod_p_q);
      trials++;
      do_mult(a, b, n, n_prime, hw);
      if (hw !== expected) begin
        errors++;
        $display("[FAIL] MUL %s  (curve=%0d mod_p_q=%0d)", label, curve_sel, mod_p_q);
        $display("       a   = %0h", a);
        $display("       b   = %0h", b);
        $display("       n   = %0h", n);
        $display("       mu  = %0h", n_prime);
        $display("       hw  = %0h", hw);
        $display("       exp = %0h", expected);
      end else begin
        $display("[PASS] MUL %s  (curve=%0d mod_p_q=%0d)", label, curve_sel, mod_p_q);
      end
    end
  endtask

  task automatic check_addsub(
      input string    label,
      input bit       do_sub,
      input bit       curve_sel,
      input bit       mod_p_q,
      input [REG-1:0] a,
      input [REG-1:0] b,
      input [REG-1:0] expected
  );
    logic [REG-1:0] hw;
    logic [REG-1:0] n;
    begin
      n = sel_prime(curve_sel, mod_p_q);
      trials++;
      do_addsub(do_sub, a, b, n, hw);
      if (hw !== expected) begin
        errors++;
        $display("[FAIL] %s %s  (curve=%0d mod_p_q=%0d)",
                 do_sub ? "SUB" : "ADD", label, curve_sel, mod_p_q);
        $display("       a   = %0h", a);
        $display("       b   = %0h", b);
        $display("       n   = %0h", n);
        $display("       hw  = %0h", hw);
        $display("       exp = %0h", expected);
      end else begin
        $display("[PASS] %s %s  (curve=%0d mod_p_q=%0d)",
                 do_sub ? "SUB" : "ADD", label, curve_sel, mod_p_q);
      end
    end
  endtask

  // -----------------------------------------------------------------
  // Per-corner directed + random workout
  // -----------------------------------------------------------------
  function automatic [REG-1:0] rand_lt(input [REG-1:0] n);
    logic [REG-1:0] v;
    begin
      v = {$urandom, $urandom, $urandom, $urandom,
           $urandom, $urandom, $urandom, $urandom,
           $urandom, $urandom, $urandom, $urandom};
      while (v >= n) v = v >> 1;
      rand_lt = v;
    end
  endfunction

  task automatic corner_block(
      input string label,
      input bit    curve_sel,
      input bit    mod_p_q,
      input [REG-1:0] one_mont,      // ONE_*_MONT for this corner
      input [REG-1:0] r2_mont,       // R2_*_MONT  for this corner
      input [REG-1:0] one_p_mont_p,  // ONE_p_MONT (only used for mod_p MUL identity probe)
      input [REG-1:0] tag_mont       // a known Mont constant for the corner (e.g. E_a_MONT for mod_p, R2_q_MONT for mod_q)
  );
    logic [REG-1:0] n;
    logic [REG-1:0] a, b, expected, hw;
    logic [REG:0]   wide;          // REG+1 bits to absorb add/sub carry/borrow
    string lab;
    int    i;
    begin
      n = sel_prime(curve_sel, mod_p_q);

      $display("------------------------------------------------------------");
      $display(" Corner: %s  curve_sel=%0d mod_p_q=%0d  prime=%0h",
               label, curve_sel, mod_p_q, n);
      $display("------------------------------------------------------------");

      // ---------- MUL: directed identity ----------
      // R2 * 1 == ONE
      check_mult({label, " R2*1==ONE"}, curve_sel, mod_p_q,
                 r2_mont, 384'd1, one_mont);
      // ONE * ONE == ONE
      check_mult({label, " ONE*ONE==ONE"}, curve_sel, mod_p_q,
                 one_mont, one_mont, one_mont);
      // tag * 1 == tag  (sanity that the corner's chosen Mont constant survives a *1 mont multiply)
      check_mult({label, " TAG*1==TAG"}, curve_sel, mod_p_q,
                 tag_mont, 384'd1,
                 ref_montmul(tag_mont, 384'd1, n, sel_mu(curve_sel, mod_p_q)));

      // ---------- MUL: random Montgomery ops ----------
      for (i = 0; i < N_RAND_PER_CORNER; i++) begin
        a        = rand_lt(n);
        b        = rand_lt(n);
        expected = ref_montmul(a, b, n, sel_mu(curve_sel, mod_p_q));
        $sformat(lab, "%s rand[%0d]", label, i);
        check_mult(lab, curve_sel, mod_p_q, a, b, expected);
      end

      // ---------- ADD edge cases ----------
      // 0 + 0 == 0
      check_addsub({label, " 0+0==0"}, 1'b0, curve_sel, mod_p_q,
                   '0, '0, '0);
      // (m-1) + 1 == 0
      check_addsub({label, " (m-1)+1==0"}, 1'b0, curve_sel, mod_p_q,
                   n - 1, 384'd1, '0);
      // (m-1) + (m-1) == m-2
      check_addsub({label, " (m-1)+(m-1)==m-2"}, 1'b0, curve_sel, mod_p_q,
                   n - 1, n - 1, n - 2);

      // ---------- SUB edge cases ----------
      // 0 - 1 == m-1
      check_addsub({label, " 0-1==m-1"}, 1'b1, curve_sel, mod_p_q,
                   '0, 384'd1, n - 1);
      // m-1 - (m-1) == 0
      check_addsub({label, " (m-1)-(m-1)==0"}, 1'b1, curve_sel, mod_p_q,
                   n - 1, n - 1, '0);

      // ---------- ADD/SUB random ----------
      for (i = 0; i < N_RAND_PER_CORNER; i++) begin
        a        = rand_lt(n);
        b        = rand_lt(n);
        // (a+b) mod n with a 385-bit intermediate to keep the carry bit.
        wide     = {1'b0, a} + {1'b0, b};
        expected = (wide >= {1'b0, n}) ? (wide - {1'b0, n}) : wide[REG-1:0];
        $sformat(lab, "%s rand_add[%0d]", label, i);
        check_addsub(lab, 1'b0, curve_sel, mod_p_q, a, b, expected);

        a = rand_lt(n);
        b = rand_lt(n);
        // (a-b) mod n; both a,b are in [0,n), so result is exactly one of these.
        expected = (a >= b) ? (a - b) : ((a + n) - b);
        $sformat(lab, "%s rand_sub[%0d]", label, i);
        check_addsub(lab, 1'b1, curve_sel, mod_p_q, a, b, expected);
      end
    end
  endtask

  // -----------------------------------------------------------------
  // Main test sequence
  // -----------------------------------------------------------------
  initial begin
    errors  = 0;
    trials  = 0;
    reset_n = 1'b0;
    add_en  = 1'b0;
    sub_sel = 1'b0;
    mult_en = 1'b0;
    prime   = '0;
    mu      = '0;
    opa     = '0;
    opb     = '0;

    repeat (5) @(posedge clk);
    reset_n = 1'b1;
    repeat (5) @(posedge clk);

    // ----------- P-384 mod p -----------
    corner_block("P384/p", 1'b0, 1'b0,
                 ONE_p_MONT_P384, R2_p_MONT_P384,
                 ONE_p_MONT_P384, E_a_MONT_P384);

    // ----------- P-384 mod q -----------
    corner_block("P384/q", 1'b0, 1'b1,
                 ONE_q_MONT_P384, R2_q_MONT_P384,
                 ONE_p_MONT_P384, R2_q_MONT_P384);

    // ----------- P-256 mod p -----------
    corner_block("P256/p", 1'b1, 1'b0,
                 ONE_p_MONT_P256, R2_p_MONT_P256,
                 ONE_p_MONT_P256, E_a_MONT_P256);

    // ----------- P-256 mod q -----------
    corner_block("P256/q", 1'b1, 1'b1,
                 ONE_q_MONT_P256, R2_q_MONT_P256,
                 ONE_p_MONT_P256, R2_q_MONT_P256);

    $display("============================================================");
    if (errors == 0) begin
      $display(" *** All %0d FAU dual-curve checks passed", trials);
      $display(" * TESTCASE PASSED");
    end else begin
      $display(" *** %0d of %0d FAU dual-curve checks FAILED", errors, trials);
      $display(" * TESTCASE FAILED");
    end
    $display("============================================================");
    $finish;
  end

  // Watchdog
  initial begin
    #10_000_000;
    $display(" * TESTCASE FAILED (timeout)");
    $finish;
  end

endmodule
