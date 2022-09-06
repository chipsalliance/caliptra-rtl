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

import sim_irq_pkg::irq_type_t;

module sim_irq_gen #(
    parameter NUM_INTR  = 1, // Number of interrupts per class (SWerV allows up to 255)
    parameter INTR_FREQ = "HIGH" // "HIGH" "MEDIUM" "LOW"
) (
    input clk,
    input rst_n,

    input  var irq_type_t       intr_cfg,

    output logic [NUM_INTR-1:0] intr,
    input        [NUM_INTR-1:0] intr_clr
);


////////////////////////////////////
// Assertions
initial assert (NUM_INTR inside {[1:255]}) else begin
    $error("NUM_INTR must be in the range 1:255");
    $finish;
end
initial begin
    int intr_ii;
    wait(rst_n === 1);
    for (intr_ii = 0; intr_ii < NUM_INTR; intr_ii++) begin
        assert(!$isunknown(intr_cfg.active_high[intr_ii])) else begin
            $error("Must provide legal configuration for intr [%d] in intr_cfg!", intr_ii);
            $finish;
        end
        assert(!$isunknown(intr_cfg.level_assert[intr_ii])) else begin
            $error("Must provide legal configuration for intr [%d] in intr_cfg!", intr_ii);
            $finish;
        end
    end
end


////////////////////////////////////
// Localparams
localparam time MIN_TIME_INCR = INTR_FREQ == "HIGH"   ? 100ns :
                                INTR_FREQ == "MEDIUM" ? 800ns :
                                INTR_FREQ == "LOW"    ? 4us   :
                                                        8us;
localparam time MAX_TIME_INCR = INTR_FREQ == "HIGH"   ? 1us   :
                                INTR_FREQ == "MEDIUM" ? 6us   :
                                INTR_FREQ == "LOW"    ? 15us  :
                                                        25us;


////////////////////////////////////
// Interrupt Generation Logic
realtime                     next_intr_time;
logic [NUM_INTR-1:0]         rand_intr;
logic [NUM_INTR-1:0]         intr_pending; // Always active-high, for sim readability
logic [$clog2(NUM_INTR)-1:0] intr_sel;

// Generate interrupt pulses randomly, according to the parameterized rate
initial begin
    rand_intr = {NUM_INTR{1'b0}};
    wait(rst_n === 1'b0);
    wait(rst_n === 1'b1);
    next_intr_time = $realtime + $urandom_range(MAX_TIME_INCR,MIN_TIME_INCR);
    $display("First intr at time [%t]", next_intr_time);
    forever begin
        while ($realtime < next_intr_time) @(posedge clk);
        intr_sel = $urandom_range(NUM_INTR-1,0);
//        while (intr_pending[intr_sel]) begin
//            @(posedge clk)
//            intr_sel = $urandom_range(NUM_INTR-1,0);
//        end
        @(posedge clk)
        if (!intr_pending[intr_sel]) begin
            rand_intr = NUM_INTR'(1) << intr_sel;
            $display("Setting intr bit [0x%x] at time [%t]", intr_sel, $realtime);
            repeat(2) @(posedge clk);
            rand_intr = {NUM_INTR{1'b0}}; // Pulse 1 cycle to set intr
        end
        next_intr_time = $realtime + $urandom_range(MAX_TIME_INCR,MIN_TIME_INCR);
        $display("Next intr at time [%t]", next_intr_time);
    end
end

// Register the interrupt output until cleared (by uProc)
genvar intr_ii;
generate
    for (intr_ii = 0; intr_ii < NUM_INTR; intr_ii++) begin
        always_ff@(posedge clk or negedge rst_n) begin
            if (!rst_n) begin
                intr_pending[intr_ii] <= 1'b0;
                intr[intr_ii]         <= ~intr_cfg.active_high[intr_ii];
            end
            // Only preserve the registered interrupt state when this interrupt
            // is configured as level (not pulse)
            // Set the interrupt with the randomly asserted rand_intr input and
            // clear it with some externally driven clr signal (by the testbench)
            else begin
                intr_pending[intr_ii] <= (intr_pending[intr_ii] | rand_intr[intr_ii]) & ~intr_clr[intr_ii];
                if (intr_cfg.active_high[intr_ii]) begin
                    intr [intr_ii] <=  ((intr_pending[intr_ii] & intr_cfg.level_assert[intr_ii]) | rand_intr[intr_ii]) & ~intr_clr[intr_ii]; // Output as a pulse if configured
                end
                else begin
                    intr [intr_ii] <= ~((intr_pending[intr_ii] & intr_cfg.level_assert[intr_ii]) | rand_intr[intr_ii]) |  intr_clr[intr_ii]; // Output as a pulse if configured
                end
            end
        end
    end
endgenerate
//always_comb intr_pending[254:NUM_INTR] = 0;
//always_comb intr        [254:NUM_INTR] = ~intr_cfg.active_high[254:NUM_INTR];

//assert_invalid_new_intr: assert property(@(posedge clk) |rand_intr |-> ($onehot(rand_intr) && ((rand_intr & intr_pending) == NUM_INTR'(0)))) else begin
//    $error  ("Invalid new interrupt being requested while already pending on ID!");
//    $display("    NEW INTR: [0x%x]", rand_intr   );
//    $display("    INTR:     [0x%x]", intr_pending);
//    #10ns $finish;
//end
assert_invalid_clr: assert property(@(posedge clk) |intr_clr |-> ($onehot(intr_clr) && ((intr_clr & intr_pending) == intr_clr))) else begin
    $error  ("Interrupt clear attempted for interrupt entry that is not set!");
    $display("    CLR Index:  [0x%x]", $clog2(intr_clr)                                  );
    $display("    INTR_CLR:   [0x%x]", intr_clr                                          );
    $display("    INTR_PND:   [0x%x]", intr_pending                                      );
    #10ns $finish;
end

endmodule
