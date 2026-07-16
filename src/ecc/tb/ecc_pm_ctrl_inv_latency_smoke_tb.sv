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
// Smoke TB for a-p256-inv-latency-opt:
//   * Drives ecc_pm_ctrl through KEYGEN flow on both curves
//   * Verifies P-256 leaves INV at INV_S+703 (CONV_S target) instead of INV_E_P384
//   * Verifies P-384 still leaves INV at INV_E_P384 (= INV_S+1039)
//   * Verifies P-256 leaves INVq at INVq_S+703 instead of INVq_E_P384 (SIGN_CMD)
//
// Approach: instantiate ecc_pm_ctrl with a fake digit stream (digit_i=0 keeps
// the Montgomery ladder counter consistent). The actual datapath isn't built
// here — we only need to observe prog_cntr transitions. Stalls are driven by
// the real prog_instr opcodes coming out of the dual ROM, so MULT/ADD delays
// are honored exactly as in production.

`default_nettype none

module ecc_pm_ctrl_inv_latency_smoke_tb
    import ecc_pm_uop_pkg::*;
    import ecc_params_pkg::*;
    ();

    localparam int unsigned MAX_CYCLES   = 4_000_000;

    logic                       clk;
    logic                       reset_n;
    logic                       zeroize;
    logic                       curve_sel;
    logic [3:0]                 ecc_cmd;
    logic                       digit;
    pm_instr_struct_t           instr;
    logic                       req_digit;
    logic                       busy;

    ecc_pm_ctrl #(
        .INSTR_SIZE (24)
    ) dut (
        .clk          (clk),
        .reset_n      (reset_n),
        .zeroize      (zeroize),
        .curve_sel_i  (curve_sel),
        .ecc_cmd_i    (ecc_cmd),
        .digit_i      (digit),
        .instr_o      (instr),
        .req_digit_o  (req_digit),
        .busy_o       (busy)
    );

    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    int errors = 0;

    task automatic do_reset();
        reset_n = 0;
        zeroize = 0;
        curve_sel = 0;
        ecc_cmd = '0;
        digit = 0;
        repeat (5) @(posedge clk);
        reset_n = 1;
        repeat (2) @(posedge clk);
    endtask

    // Drive a constant digit_i=0 throughout. mont_cntr decrements once per PD_E
    // visit; req_digit_o is asserted on PA_S to request next digit, but value
    // doesn't matter for FSM observation.
    initial digit = 1'b0;

    // ----------------------------------------------------------------
    // Run one keygen-like flow and capture INV exit address.
    // Returns the prog_cntr value on the cycle BEFORE prog_cntr jumps to CONV_S.
    // ----------------------------------------------------------------
    task automatic run_and_capture_inv_exit(
        input  bit                            sel_curve,
        input  bit [3:0]                      cmd,
        output bit [PROG_ADDR_W-1:0]          inv_exit_addr,
        output bit                            timed_out
    );
        int unsigned cyc;
        bit                                   in_inv;
        bit [PROG_ADDR_W-1:0]                 last_in_inv;

        timed_out     = 0;
        inv_exit_addr = '0;
        in_inv        = 0;
        last_in_inv   = '0;

        // Start with curve and command.
        curve_sel = sel_curve;
        ecc_cmd   = cmd;
        @(posedge clk);
        ecc_cmd   = '0;

        for (cyc = 0; cyc < MAX_CYCLES; cyc++) begin
            @(posedge clk);

            // Track INV section visits.
            if (dut.prog_cntr >= INV_S && dut.prog_cntr <= INV_E_P384) begin
                in_inv = 1;
                last_in_inv = dut.prog_cntr;
            end
            else if (in_inv && dut.prog_cntr == CONV_S) begin
                inv_exit_addr = last_in_inv;
                return;
            end
        end
        timed_out = 1;
    endtask

    task automatic run_and_capture_invq_exit(
        input  bit                            sel_curve,
        output bit [PROG_ADDR_W-1:0]          invq_exit_addr,
        output bit                            timed_out
    );
        int unsigned cyc;
        bit                                   in_invq;
        bit [PROG_ADDR_W-1:0]                 last_in_invq;
        bit [PROG_ADDR_W-1:0]                 target;

        timed_out      = 0;
        invq_exit_addr = '0;
        in_invq        = 0;
        last_in_invq   = '0;
        target         = SIGN1_S;

        curve_sel = sel_curve;
        ecc_cmd   = SIGN_CMD;
        @(posedge clk);
        ecc_cmd   = '0;

        for (cyc = 0; cyc < MAX_CYCLES; cyc++) begin
            @(posedge clk);

            if (dut.prog_cntr >= INVq_S && dut.prog_cntr <= INVq_E_P384) begin
                in_invq = 1;
                last_in_invq = dut.prog_cntr;
            end
            else if (in_invq && dut.prog_cntr == target) begin
                invq_exit_addr = last_in_invq;
                return;
            end
        end
        timed_out = 1;
    endtask

    // ----------------------------------------------------------------
    // Main
    // ----------------------------------------------------------------
    bit [PROG_ADDR_W-1:0]   exit_addr;
    bit                     to;

    initial begin : main
        $display("[%0t] ecc_pm_ctrl_inv_latency_smoke_tb starting", $time);
        $display("  INV_S=%0d INV_E_P256=%0d INV_E_P384=%0d INVq_S=%0d INVq_E_P256=%0d INVq_E_P384=%0d",
                 INV_S, INV_E_P256, INV_E_P384, INVq_S, INVq_E_P256, INVq_E_P384);

        // --------------------------------------------------------------
        // Check 1: P-384 KEYGEN — INV exits at INV_E_P384
        // --------------------------------------------------------------
        do_reset();
        run_and_capture_inv_exit(1'b0, KEYGEN_CMD, exit_addr, to);
        if (to) begin
            $display("FAIL: P-384 KEYGEN timed out before reaching CONV_S");
            errors++;
        end
        else if (exit_addr !== INV_E_P384) begin
            $display("FAIL: P-384 KEYGEN INV exit addr = %0d, expected INV_E_P384 = %0d",
                     exit_addr, INV_E_P384);
            errors++;
        end
        else begin
            $display("PASS: P-384 KEYGEN INV exit at INV_E_P384 (%0d)", exit_addr);
        end

        // --------------------------------------------------------------
        // Check 2: P-256 KEYGEN — INV exits at INV_E_P256
        // --------------------------------------------------------------
        do_reset();
        run_and_capture_inv_exit(1'b1, KEYGEN_CMD, exit_addr, to);
        if (to) begin
            $display("FAIL: P-256 KEYGEN timed out before reaching CONV_S");
            errors++;
        end
        else if (exit_addr !== INV_E_P256) begin
            $display("FAIL: P-256 KEYGEN INV exit addr = %0d, expected INV_E_P256 = %0d",
                     exit_addr, INV_E_P256);
            errors++;
        end
        else begin
            $display("PASS: P-256 KEYGEN INV exit at INV_E_P256 (%0d, saved %0d cycles vs INV_E_P384)",
                     exit_addr, INV_E_P384 - INV_E_P256);
        end

        // --------------------------------------------------------------
        // Check 3: P-384 SIGN — INVq exits at INVq_E_P384
        // --------------------------------------------------------------
        do_reset();
        run_and_capture_invq_exit(1'b0, exit_addr, to);
        if (to) begin
            $display("FAIL: P-384 SIGN timed out before reaching SIGN1_S");
            errors++;
        end
        else if (exit_addr !== INVq_E_P384) begin
            $display("FAIL: P-384 SIGN INVq exit addr = %0d, expected INVq_E_P384 = %0d",
                     exit_addr, INVq_E_P384);
            errors++;
        end
        else begin
            $display("PASS: P-384 SIGN INVq exit at INVq_E_P384 (%0d)", exit_addr);
        end

        // --------------------------------------------------------------
        // Check 4: P-256 SIGN — INVq exits at INVq_E_P256
        // --------------------------------------------------------------
        do_reset();
        run_and_capture_invq_exit(1'b1, exit_addr, to);
        if (to) begin
            $display("FAIL: P-256 SIGN timed out before reaching SIGN1_S");
            errors++;
        end
        else if (exit_addr !== INVq_E_P256) begin
            $display("FAIL: P-256 SIGN INVq exit addr = %0d, expected INVq_E_P256 = %0d",
                     exit_addr, INVq_E_P256);
            errors++;
        end
        else begin
            $display("PASS: P-256 SIGN INVq exit at INVq_E_P256 (%0d, saved %0d cycles vs INVq_E_P384)",
                     exit_addr, INVq_E_P384 - INVq_E_P256);
        end

        // --------------------------------------------------------------
        if (errors == 0) begin
            $display("*** All 4 INV-latency checks passed * TESTCASE PASSED ***");
        end
        else begin
            $display("*** %0d FAILURES * TESTCASE FAILED ***", errors);
        end
        $finish;
    end

endmodule

`default_nettype wire
