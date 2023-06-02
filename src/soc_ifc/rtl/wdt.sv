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

module wdt
    import soc_ifc_pkg::*;
(
    input  logic clk,
    input  logic cptra_rst_b,
    //Timer inputs
    input  logic timer1_en,
    input  logic timer2_en,
    input  logic timer1_restart,
    input  logic timer2_restart,
    input  logic [WDT_TIMEOUT_PERIOD_W-1:0] timer1_timeout_period,
    input  logic [WDT_TIMEOUT_PERIOD_W-1:0] timer2_timeout_period,
    //Interrupts
    input  logic wdt_timer1_timeout_serviced,
    input  logic wdt_timer2_timeout_serviced,
    //WDT STATUS bits
    output logic t1_timeout,
    output logic t2_timeout
);

//Timer1
logic [WDT_TIMEOUT_PERIOD_W-1:0] timer1_count;
logic timer1_count_en;

//Timer2
logic [WDT_TIMEOUT_PERIOD_W-1:0] timer2_count;
logic timer2_count_en;

//Output assignments
assign t1_timeout = (timer1_count == timer1_timeout_period);
assign t2_timeout = (timer2_count == timer2_timeout_period);

assign timer1_count_en = timer1_en;
assign timer2_count_en = !timer2_en ? t1_timeout : timer2_en;


//Timer1
always_ff @(posedge clk or negedge cptra_rst_b) begin
    if(!cptra_rst_b) begin
        timer1_count <= 'h0;
    end
    else if(timer1_count_en) begin
        //Count up always. If restart = 1, count from 0 again
        //If it timed out, an intr is triggered to core. Don't reset
        //until intr is serviced. If serviced, and t2 has not timed out,
        //start count from 0 again. In all other cases, hold the count
        //Note: if t2 has timed out, expect a warm reset to re-init timers
        timer1_count <= timer1_restart && !t1_timeout ? 'h0 
                                                    : (wdt_timer1_timeout_serviced && (timer2_en || !t2_timeout)) ? 'h0 
                                                    : !t1_timeout ? (timer1_count + 'h1)
                                                    : timer1_count;
    end
end

//Timer2
always_ff @(posedge clk or negedge cptra_rst_b) begin
    if(!cptra_rst_b) begin
        timer2_count <= 'h0;
    end
    else if(timer2_count_en) begin
        //If t1 timed out and an intr was triggered, once that is serviced
        //and t2 has not yet timed out, restart both t1 and t2. Otherwise,
        //hold the count. In case of time out, nmi and fatal error are triggered
        //Warm reset is expected to re-init timers
        //Note: if timer1 and timer2 are independently enabled, we want to remove the dependency of timer1 on timer2 and vice versa
        timer2_count <= timer2_restart && !t2_timeout ? 'h0 
                                                    : ((wdt_timer1_timeout_serviced && !t2_timeout && !timer2_en) || wdt_timer2_timeout_serviced) ? 'h0 
                                                    : !t2_timeout ? (timer2_count + 'h1) 
                                                    : timer2_count;
    end
end

endmodule