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
// ecc_scalar_blinding_dualcurve_smoke_tb.sv
// -----------------------------------------
// Standalone smoke test for `ecc_scalar_blinding` against both P-384
// (curve_sel_i = 0) and P-256 (curve_sel_i = 1). Closes the DV gap for
// the curve-muxed GROUP_ORDER input (line 143 of the RTL).
//
// Coverage:
//   1) Algebraic KAT: data_o must equal (scalar + rnd * GROUP_ORDER_*)
//      truncated to REG_SIZE+RND_SIZE bits, for both curves.
//   2) Cryptographic invariant: data_o mod GROUP_ORDER_* == scalar,
//      verifying that scalar reduction modulo the curve order is
//      preserved by blinding (the property that makes the blinding
//      transparent to the scalar multiplication that follows).
//   3) Latency parity (constant-time check): the cycle count from
//      en_i pulse to !busy_o must be identical between P-384 and
//      P-256. Any data-dependent branch in the FSM would break this.
//   4) P-256 output upper-bit zero check: for a 256-bit scalar (high
//      128 input bits are zero) and 192-bit rnd, the mathematical
//      result has at most 256+192 = 448 bits, so the top 128 bits of
//      the 576-bit data_o port must be zero.
//
// Pass criterion: zero errors across all directed + random checks
// for both curves, and equal latency between curves.

`default_nettype none

module ecc_scalar_blinding_dualcurve_smoke_tb;
  import ecc_params_pkg::*;

  localparam int REG     = 384;
  localparam int RND     = 192;
  localparam int OUT_W   = REG + RND;          // 576
  localparam int N_RAND_PER_CURVE = 20;

  logic                 clk;
  logic                 reset_n;
  logic                 zeroize;

  logic                 curve_sel;
  logic                 en;
  logic [REG-1:0]       scalar;
  logic [RND-1:0]       rnd;
  logic [OUT_W-1:0]     data_o;
  logic                 busy_o;

  int p384_latency;
  int p256_latency;
  int errors;
  int trials;

  initial clk = 1'b0;
  always #5 clk = ~clk;

  // -----------------------------------------------------------------
  // DUT
  // -----------------------------------------------------------------
  ecc_scalar_blinding #(
    .REG_SIZE(REG),
    .RND_SIZE(RND),
    .RADIX   (32)
  ) dut (
    .clk        (clk),
    .reset_n    (reset_n),
    .zeroize    (zeroize),
    .curve_sel_i(curve_sel),
    .en_i       (en),
    .data_i     (scalar),
    .rnd_i      (rnd),
    .data_o     (data_o),
    .busy_o     (busy_o)
  );

  // -----------------------------------------------------------------
  // SW reference (matches fv_scalar_blinding randomize() function)
  //   ref = (scalar + rnd*grp_order) truncated to REG+RND bits.
  // -----------------------------------------------------------------
  function automatic [OUT_W-1:0] ref_blind(
      input [REG-1:0]   s,
      input [RND-1:0]   r,
      input [REG-1:0]   grp
  );
    logic [OUT_W-1:0] prod;
    prod      = OUT_W'(r) * OUT_W'(grp);
    ref_blind = prod + OUT_W'(s);
  endfunction

  // -----------------------------------------------------------------
  // SW modular reduction of an OUT_W-bit value by an REG-bit modulus.
  // Standard schoolbook-from-the-top to avoid the SV %-operator with
  // mixed-width operands.
  // -----------------------------------------------------------------
  function automatic [REG-1:0] mod_reduce(
      input [OUT_W-1:0] x,
      input [REG-1:0]   m
  );
    logic [OUT_W:0] acc;   // OUT_W+1 bits to absorb a shift+conditional sub
    int i;
    begin
      acc = '0;
      for (i = OUT_W-1; i >= 0; i--) begin
        acc = {acc[OUT_W-1:0], 1'b0} | OUT_W'(x[i]);
        if (acc >= {1'b0, m})
          acc = acc - {1'b0, m};
      end
      mod_reduce = acc[REG-1:0];
    end
  endfunction

  function automatic [REG-1:0] grp_order(input bit curve);
    grp_order = curve ? GROUP_ORDER_P256 : GROUP_ORDER_P384;
  endfunction

  function automatic [REG-1:0] rand_scalar(input [REG-1:0] m);
    logic [REG-1:0] v;
    begin
      v = {$urandom, $urandom, $urandom, $urandom,
           $urandom, $urandom, $urandom, $urandom,
           $urandom, $urandom, $urandom, $urandom};
      while (v >= m) v = v >> 1;
      rand_scalar = v;
    end
  endfunction

  function automatic [RND-1:0] rand_rnd();
    rand_rnd = {$urandom, $urandom, $urandom, $urandom, $urandom, $urandom};
  endfunction

  // -----------------------------------------------------------------
  // Driver: pulse en_i, wait for !busy_o, sample data_o. Returns the
  // number of clk edges from the en pulse to busy deassertion, so the
  // test can compare per-curve latencies.
  // -----------------------------------------------------------------
  task automatic drive_blind(
      input  bit            curve,
      input  [REG-1:0]      s,
      input  [RND-1:0]      r,
      output [OUT_W-1:0]    res,
      output int            cycles
  );
    int wait_count;
    begin
      @(posedge clk);
      curve_sel <= curve;
      scalar    <= s;
      rnd       <= r;
      en        <= 1'b1;
      @(posedge clk);
      en        <= 1'b0;
      wait_count = 0;
      @(posedge clk);
      while (busy_o == 1'b1 && wait_count < 500) begin
        @(posedge clk);
        wait_count++;
      end
      res    = data_o;
      cycles = wait_count;
    end
  endtask

  // -----------------------------------------------------------------
  // Generic check helper
  // -----------------------------------------------------------------
  task automatic check_case(
      input string      label,
      input bit         curve,
      input [REG-1:0]   s,
      input [RND-1:0]   r,
      output int        cycles
  );
    logic [OUT_W-1:0] hw;
    logic [OUT_W-1:0] expected;
    logic [REG-1:0]   grp;
    logic [REG-1:0]   reduced;
    begin
      grp      = grp_order(curve);
      expected = ref_blind(s, r, grp);
      trials++;
      drive_blind(curve, s, r, hw, cycles);

      if (hw !== expected) begin
        errors++;
        $display("[FAIL] %s  (curve=%0d)  algebraic mismatch", label, curve);
        $display("       scalar = %0h", s);
        $display("       rnd    = %0h", r);
        $display("       grp    = %0h", grp);
        $display("       hw     = %0h", hw);
        $display("       exp    = %0h", expected);
      end else begin
        // Cryptographic invariant: hw mod grp must equal scalar
        reduced = mod_reduce(hw, grp);
        if (reduced !== s) begin
          errors++;
          $display("[FAIL] %s  (curve=%0d)  data_o mod grp != scalar", label, curve);
          $display("       scalar  = %0h", s);
          $display("       hw      = %0h", hw);
          $display("       reduced = %0h", reduced);
        end else begin
          $display("[PASS] %s  (curve=%0d) cycles=%0d", label, curve, cycles);
        end
      end

      // P-256 specific: upper 128 bits of data_o must be zero (the
      // mathematical result has at most 256+192 = 448 bits).
      if (curve && hw[OUT_W-1:448] !== '0) begin
        errors++;
        $display("[FAIL] %s  P-256 upper 128 bits not zero: %0h",
                 label, hw[OUT_W-1:448]);
      end
    end
  endtask

  // -----------------------------------------------------------------
  // Per-curve workout
  // -----------------------------------------------------------------
  task automatic curve_block(
      input string label,
      input bit    curve,
      output int   latency_out
  );
    logic [REG-1:0] grp;
    logic [REG-1:0] s;
    logic [RND-1:0] r;
    string lab;
    int i;
    int c;
    int last_cycles;
    begin
      grp = grp_order(curve);
      last_cycles = -1;
      $display("------------------------------------------------------------");
      $display(" Curve: %s  curve_sel=%0d  group_order=%0h", label, curve, grp);
      $display("------------------------------------------------------------");

      // Directed: scalar=0
      $sformat(lab, "%s scalar=0  rnd=0", label);
      check_case(lab, curve, '0, '0, c);
      last_cycles = c;

      $sformat(lab, "%s scalar=0  rnd=max", label);
      check_case(lab, curve, '0, '1, c);
      if (c != last_cycles) begin
        errors++;
        $display("[FAIL] %s data-dependent latency: %0d vs %0d",
                 label, c, last_cycles);
      end

      // Directed: scalar=1
      $sformat(lab, "%s scalar=1  rnd=1", label);
      check_case(lab, curve, REG'(1), RND'(1), c);
      if (c != last_cycles) begin
        errors++;
        $display("[FAIL] %s data-dependent latency", label);
      end

      // Directed: scalar=grp-1
      $sformat(lab, "%s scalar=grp-1  rnd=0", label);
      check_case(lab, curve, grp - 1, '0, c);
      if (c != last_cycles) begin
        errors++;
        $display("[FAIL] %s data-dependent latency", label);
      end

      $sformat(lab, "%s scalar=grp-1  rnd=max", label);
      check_case(lab, curve, grp - 1, '1, c);
      if (c != last_cycles) begin
        errors++;
        $display("[FAIL] %s data-dependent latency", label);
      end

      // Random
      for (i = 0; i < N_RAND_PER_CURVE; i++) begin
        s = rand_scalar(grp);
        r = rand_rnd();
        $sformat(lab, "%s rand[%0d]", label, i);
        check_case(lab, curve, s, r, c);
        if (c != last_cycles) begin
          errors++;
          $display("[FAIL] %s rand[%0d] data-dependent latency: %0d vs %0d",
                   label, i, c, last_cycles);
        end
      end

      latency_out = last_cycles;
    end
  endtask

  // -----------------------------------------------------------------
  // Main test sequence
  // -----------------------------------------------------------------
  initial begin
    errors        = 0;
    trials        = 0;
    p384_latency  = -1;
    p256_latency  = -1;

    reset_n   = 1'b0;
    zeroize   = 1'b0;
    curve_sel = 1'b0;
    en        = 1'b0;
    scalar    = '0;
    rnd       = '0;

    repeat (8) @(posedge clk);
    reset_n = 1'b1;
    repeat (4) @(posedge clk);

    curve_block("P384", 1'b0, p384_latency);
    curve_block("P256", 1'b1, p256_latency);

    $display("============================================================");
    $display(" P-384 latency = %0d cycles", p384_latency);
    $display(" P-256 latency = %0d cycles", p256_latency);
    if (p384_latency !== p256_latency) begin
      errors++;
      $display(" *** Per-curve latency MISMATCH — constant-time violated");
    end else begin
      $display(" Constant-time across curves: OK");
    end

    if (errors == 0)
      $display(" *** All %0d scalar-blinding dual-curve checks passed", trials);
    else
      $display(" *** %0d of %0d scalar-blinding dual-curve checks FAILED",
               errors, trials);

    if (errors == 0)
      $display(" * TESTCASE PASSED");
    else
      $display(" * TESTCASE FAILED");
    $display("============================================================");
    $finish;
  end

  // Watchdog
  initial begin
    #2_000_000;
    $display(" * TESTCASE FAILED (watchdog timeout)");
    $finish;
  end

endmodule

`default_nettype wire
