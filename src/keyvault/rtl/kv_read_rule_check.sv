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

module kv_read_rule_check
import kv_defines_pkg::*;
(
    input logic clk,
    input logic rst_b,

    input  logic                        read_en_i,
    input  logic                        read_done,
    output logic                        read_en_o, // Delayed from read_en_i to start read client FSM in sync with rule check result

    input  var kv_read_filter_metrics_t read_metrics,
    output logic                        read_allow
);


    // --------------------------------------- //
    // Signals                                 //
    // --------------------------------------- //
    struct packed {
        logic no_read_key_release; // DOE can not write to key release slot
    } rule_fail;


    // --------------------------------------- //
    // Rules                                   //
    // --------------------------------------- //
    // IF (OCP_LOCK_IN_PROGRESS) THEN (cryptos shall not read from OCP_LOCK_KEY_RELEASE_KV_SLOT)
    always_comb begin
        rule_fail.no_read_key_release = read_metrics.ocp_lock_in_progress &&
                                        read_metrics.kv_read_dest != (8'h1 << KV_DEST_IDX_DMA_DATA) &&
                                        read_metrics.kv_key_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT;
    end


    // --------------------------------------- //
    // Output                                  //
    // --------------------------------------- //
    // Register the rule-check status; all of the input metrics will be stabilized prior to the 
    // becomes valid, so registering the output status reduces combinatorial depth
    always_ff@(posedge clk or negedge rst_b) begin
        if (!rst_b) begin
            read_allow <= 1'b0;
            read_en_o  <= 1'b0;
        end
        else if (read_done) begin
            read_allow <= 1'b0;
            read_en_o  <= 1'b0;
        end
        else if (read_en_i) begin
            read_allow <= ~|rule_fail;
            read_en_o  <= 1'b1;
        end
        else begin
            read_allow <= read_allow;
            read_en_o  <= 1'b0;
        end
    end

endmodule
