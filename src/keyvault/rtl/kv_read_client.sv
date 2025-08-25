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
//`include "kv_defines.svh"
`include "caliptra_prim_assert.sv"

module kv_read_client 
    import kv_defines_pkg::*;
    #(
    parameter DATA_WIDTH = 512
   ,parameter HMAC = 0
   ,parameter PAD = 0

   ,localparam DATA_OFFSET_W = $clog2(DATA_WIDTH/32)
)
(
    input logic clk,
    input logic rst_b,
    input logic zeroize,

    //client control register
    input kv_read_ctrl_reg_t read_ctrl_reg,

    //access filtering rule metrics
    input var kv_read_filter_metrics_t read_metrics,

    //interface with kv
    output kv_read_t kv_read,
    input kv_rd_resp_t kv_resp,

    //interface with client
    output logic write_en,
    output logic [DATA_OFFSET_W-1:0] write_offset,
    output logic [31:0] write_data,

    output kv_error_code_e error_code,
    output logic kv_ready,
    output logic read_done
);

logic validated_read_en;
logic read_allow;
logic [DATA_OFFSET_W-1:0] read_offset;
logic [DATA_OFFSET_W:0] num_dwords;
logic write_pad;
logic [31:0] pad_data;

assign num_dwords = DATA_WIDTH/32;

kv_read_rule_check kv_read_rules
(
    .clk         (clk                  ),
    .rst_b       (rst_b                ),

    .read_en_i   (read_ctrl_reg.read_en),
    .read_done   (read_done            ),
    .read_en_o   (validated_read_en    ), // Delayed from read_en_i to start read client FSM in sync with rule check result

    .read_metrics(read_metrics         ),
    .read_allow  (read_allow           )
);

//read fsm
kv_fsm #(
    .DATA_WIDTH(DATA_WIDTH),
    .HMAC(HMAC),
    .PAD(PAD)
)
kv_read_fsm
(
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize),
    .start(validated_read_en),
    .allow(read_allow),
    .last (kv_resp.last),
    .pcr_hash_extend(read_ctrl_reg.pcr_hash_extend),
    .num_dwords(num_dwords),
    .read_offset(read_offset),
    .write_en(write_en),
    .write_offset(write_offset),
    .write_pad(write_pad),
    .write_last(),
    .pad_data(pad_data),
    .ready(kv_ready),
    .done(read_done)
);

always_comb kv_read.read_entry = read_ctrl_reg.read_entry;
always_comb kv_read.read_offset = KV_ENTRY_SIZE_W'(read_offset);

always_comb write_data = write_pad ? pad_data : kv_resp.read_data;

always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        error_code <= KV_SUCCESS;
    end
    else if (zeroize) begin
        error_code <= KV_SUCCESS;
    end
    else begin
        // On first beat of kv read, latch any error conditions.
        // On subsequent beats of kv read, preserve any error that was previously
        // flagged or decode new error conditions
        error_code <= validated_read_en && |write_offset && (error_code != KV_SUCCESS) ? error_code :
                      validated_read_en & ~read_allow ? KV_READ_FAIL :
                      validated_read_en & kv_resp.error ? KV_READ_FAIL : 
                      validated_read_en & ~kv_resp.error ? KV_SUCCESS : error_code;
    end
end

`CALIPTRA_ASSERT_KNOWN(READ_METRICS_X,  read_metrics, clk, !rst_b)

endmodule
