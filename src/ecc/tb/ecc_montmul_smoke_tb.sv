// SPDX-License-Identifier: Apache-2.0
//
// ecc_montmul_smoke_tb.sv
//
// Standalone smoke test for ecc_montgomerymultiplier at REG_SIZE=384,
// RADIX=48. Validates the multiplier against directed identity checks
// and random Mont-domain checks for both NIST P-384 and P-256 (using
// constants from ecc_params_pkg).
//
// The multiplier requires a 1-cycle start pulse (the engine uses a
// rising-edge detector around start_i). This TB models that.
//
// Pass criterion: zero errors out of all directed + random checks.

`default_nettype none

module ecc_montmul_smoke_tb;
  import ecc_params_pkg::*;

  localparam int REG = 384;
  localparam int RAD = MULT_RADIX;       // 48
  localparam int N_RAND_PER_MOD = 20;

  logic                clk;
  logic                reset_n;

  logic                start_i;
  logic [REG-1:0]      opa_i;
  logic [REG-1:0]      opb_i;
  logic [REG-1:0]      n_i;
  logic [RAD-1:0]      n_prime_i;
  logic [REG-1:0]      p_o;
  logic                ready_o;

  initial clk = 1'b0;
  always #5 clk = ~clk;

  ecc_montgomerymultiplier #(
    .REG_SIZE(REG),
    .RADIX  (RAD)
  ) dut (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(1'b0),
    .start_i(start_i),
    .opa_i(opa_i),
    .opb_i(opb_i),
    .n_i(n_i),
    .n_prime_i(n_prime_i),
    .p_o(p_o),
    .ready_o(ready_o)
  );

  int errors;
  int trials;

  // -------------- SW Montgomery reference --------------
  // result = a*b*R^-1 mod n, where R = 2^432 (= 2^(RAD * 9)) --
  // see header of ecc_montgomerymultiplier.sv.
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

  // -------------- DUT driver: 1-cycle start pulse, clean handshake --------------
  task automatic do_mul(
      input  [REG-1:0] a,
      input  [REG-1:0] b,
      input  [REG-1:0] n,
      input  [RAD-1:0] n_prime,
      output [REG-1:0] r
  );
    begin
      @(posedge clk);
      opa_i     <= a;
      opb_i     <= b;
      n_i       <= n;
      n_prime_i <= n_prime;
      start_i   <= 1'b1;
      @(posedge clk);
      start_i   <= 1'b0;
      // Wait at least one cycle for ready_o to drop, then for it to pulse high.
      @(posedge clk);
      while (ready_o == 1'b0) @(posedge clk);
      r = p_o;
    end
  endtask

  task automatic check(
      input string    label,
      input [REG-1:0] a,
      input [REG-1:0] b,
      input [REG-1:0] n,
      input [RAD-1:0] n_prime,
      input [REG-1:0] expected
  );
    logic [REG-1:0] hw;
    begin
      trials++;
      do_mul(a, b, n, n_prime, hw);
      if (hw !== expected) begin
        errors++;
        $display("[FAIL] %s", label);
        $display("       a   = %0h", a);
        $display("       b   = %0h", b);
        $display("       n   = %0h", n);
        $display("       hw  = %0h", hw);
        $display("       exp = %0h", expected);
      end else begin
        $display("[PASS] %s", label);
      end
    end
  endtask

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

  task automatic random_block(
      input string    curve_lbl,
      input [REG-1:0] n,
      input [RAD-1:0] n_prime,
      input int       count
  );
    logic [REG-1:0] a, b, expected;
    string lab;
    int    i;
    begin
      for (i = 0; i < count; i++) begin
        a        = rand_lt(n);
        b        = rand_lt(n);
        expected = ref_montmul(a, b, n, n_prime);
        $sformat(lab, "%s rand[%0d]", curve_lbl, i);
        check(lab, a, b, n, n_prime, expected);
      end
    end
  endtask

  // Reference (a*b) mod n in the normal (non-Mont) field via the
  // same internal scheme used by the multiplier reference. We just
  // call ref_montmul(a*b_lifted, 1, ...) -- but that re-multiplies
  // by R^-1, which we don't want. Easiest: do schoolbook mod-n.
  function automatic [REG-1:0] ref_mulmod(
      input [REG-1:0] a,
      input [REG-1:0] b,
      input [REG-1:0] n
  );
    logic [2*REG-1:0] prod;
    logic [2*REG-1:0] nn;
    int               i;
    begin
      prod = a * b;
      nn   = {{REG{1'b0}}, n} << (REG-1);
      for (i = 0; i < REG; i++) begin
        if (prod >= nn) prod = prod - nn;
        nn = nn >> 1;
      end
      ref_mulmod = prod[REG-1:0];
    end
  endfunction

  // End-to-end round-trip: raw a, raw b
  //   a_m = MontMul(a, R2)        // raw a -> Mont(a) = a*R mod n
  //   b_m = MontMul(b, R2)        // raw b -> Mont(b)
  //   c_m = MontMul(a_m, b_m)     // = a*b*R mod n = Mont(a*b)
  //   c   = MontMul(c_m, 1)       // = a*b mod n
  // Check c == (a*b) mod n.
  task automatic roundtrip_block(
      input string    curve_lbl,
      input [REG-1:0] n,
      input [RAD-1:0] n_prime,
      input [REG-1:0] r2_mont,
      input int       count
  );
    logic [REG-1:0] a, b, a_m, b_m, c_m, c_raw, expected;
    string lab;
    int    i;
    begin
      for (i = 0; i < count; i++) begin
        a = rand_lt(n);
        b = rand_lt(n);
        do_mul(a,   r2_mont, n, n_prime, a_m);
        do_mul(b,   r2_mont, n, n_prime, b_m);
        do_mul(a_m, b_m,     n, n_prime, c_m);
        do_mul(c_m, 384'd1,  n, n_prime, c_raw);
        expected = ref_mulmod(a, b, n);
        trials++;
        if (c_raw !== expected) begin
          errors++;
          $sformat(lab, "%s roundtrip[%0d]", curve_lbl, i);
          $display("[FAIL] %s", lab);
          $display("       a    = %0h", a);
          $display("       b    = %0h", b);
          $display("       c_hw = %0h", c_raw);
          $display("       exp  = %0h", expected);
        end else begin
          $display("[PASS] %s roundtrip[%0d]", curve_lbl, i);
        end
      end
    end
  endtask

  initial begin
    errors    = 0;
    trials    = 0;
    reset_n   = 1'b0;
    start_i   = 1'b0;
    opa_i     = '0;
    opb_i     = '0;
    n_i       = '0;
    n_prime_i = '0;

    repeat (5) @(posedge clk);
    reset_n = 1'b1;
    repeat (5) @(posedge clk);

    // ---------------- P-384 ----------------
    $display("============================================================");
    $display(" P-384 directed identity checks");
    $display("============================================================");
    check("P384/p ONE_p * ONE_p == ONE_p",
          ONE_p_MONT_P384, ONE_p_MONT_P384, PRIME_P384, PRIME_mu_P384,
          ONE_p_MONT_P384);
    check("P384/p R2_p   * 1     == ONE_p",
          R2_p_MONT_P384, 384'd1, PRIME_P384, PRIME_mu_P384,
          ONE_p_MONT_P384);
    check("P384/p E_a    * ONE_p == E_a",
          E_a_MONT_P384, ONE_p_MONT_P384, PRIME_P384, PRIME_mu_P384,
          E_a_MONT_P384);
    check("P384/q ONE_q * ONE_q == ONE_q",
          ONE_q_MONT_P384, ONE_q_MONT_P384, GROUP_ORDER_P384, GROUP_ORDER_mu_P384,
          ONE_q_MONT_P384);
    check("P384/q R2_q   * 1     == ONE_q",
          R2_q_MONT_P384, 384'd1, GROUP_ORDER_P384, GROUP_ORDER_mu_P384,
          ONE_q_MONT_P384);

    $display(" P-384 random Mont-domain checks (mod p) x %0d", N_RAND_PER_MOD);
    random_block("P384/p", PRIME_P384,       PRIME_mu_P384,       N_RAND_PER_MOD);
    $display(" P-384 random Mont-domain checks (mod q) x %0d", N_RAND_PER_MOD);
    random_block("P384/q", GROUP_ORDER_P384, GROUP_ORDER_mu_P384, N_RAND_PER_MOD);

    $display(" P-384 end-to-end round-trip (raw->Mont->raw) x %0d/mod", N_RAND_PER_MOD);
    roundtrip_block("P384/p", PRIME_P384,       PRIME_mu_P384,       R2_p_MONT_P384, N_RAND_PER_MOD);
    roundtrip_block("P384/q", GROUP_ORDER_P384, GROUP_ORDER_mu_P384, R2_q_MONT_P384, N_RAND_PER_MOD);

    // ---------------- P-256 ----------------
    $display("============================================================");
    $display(" P-256 directed identity checks  (R = 2^384 internally)");
    $display("============================================================");
    check("P256/p ONE_p * ONE_p == ONE_p",
          ONE_p_MONT_P256, ONE_p_MONT_P256, PRIME_P256, PRIME_mu_P256,
          ONE_p_MONT_P256);
    check("P256/p R2_p   * 1     == ONE_p",
          R2_p_MONT_P256, 384'd1, PRIME_P256, PRIME_mu_P256,
          ONE_p_MONT_P256);
    check("P256/p E_a    * ONE_p == E_a",
          E_a_MONT_P256, ONE_p_MONT_P256, PRIME_P256, PRIME_mu_P256,
          E_a_MONT_P256);
    check("P256/p E_b    * ONE_p == E_b",
          E_b_MONT_P256, ONE_p_MONT_P256, PRIME_P256, PRIME_mu_P256,
          E_b_MONT_P256);
    check("P256/p G_X    * ONE_p == G_X",
          G_X_MONT_P256, ONE_p_MONT_P256, PRIME_P256, PRIME_mu_P256,
          G_X_MONT_P256);
    check("P256/p G_Y    * ONE_p == G_Y",
          G_Y_MONT_P256, ONE_p_MONT_P256, PRIME_P256, PRIME_mu_P256,
          G_Y_MONT_P256);
    check("P256/q ONE_q * ONE_q == ONE_q",
          ONE_q_MONT_P256, ONE_q_MONT_P256, GROUP_ORDER_P256, GROUP_ORDER_mu_P256,
          ONE_q_MONT_P256);
    check("P256/q R2_q   * 1     == ONE_q",
          R2_q_MONT_P256, 384'd1, GROUP_ORDER_P256, GROUP_ORDER_mu_P256,
          ONE_q_MONT_P256);

    $display(" P-256 random Mont-domain checks (mod p) x %0d", N_RAND_PER_MOD);
    random_block("P256/p", PRIME_P256,       PRIME_mu_P256,       N_RAND_PER_MOD);
    $display(" P-256 random Mont-domain checks (mod q) x %0d", N_RAND_PER_MOD);
    random_block("P256/q", GROUP_ORDER_P256, GROUP_ORDER_mu_P256, N_RAND_PER_MOD);

    $display(" P-256 end-to-end round-trip (raw->Mont->raw) x %0d/mod", N_RAND_PER_MOD);
    roundtrip_block("P256/p", PRIME_P256,       PRIME_mu_P256,       R2_p_MONT_P256, N_RAND_PER_MOD);
    roundtrip_block("P256/q", GROUP_ORDER_P256, GROUP_ORDER_mu_P256, R2_q_MONT_P256, N_RAND_PER_MOD);

    $display("============================================================");
    if (errors == 0) begin
      $display(" *** All %0d test cases completed successfully", trials);
      $display(" * TESTCASE PASSED");
    end else begin
      $display(" *** %0d of %0d test cases FAILED", errors, trials);
      $display(" * TESTCASE FAILED");
    end
    $display("============================================================");
    $finish;
  end

  initial begin
    #5000000;
    $display(" * TESTCASE FAILED (timeout)");
    $finish;
  end

endmodule
