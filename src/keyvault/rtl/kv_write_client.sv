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

module kv_write_client 
    import kv_defines_pkg::*;
    #(
    parameter DATA_WIDTH = 512
   ,parameter KV_WRITE_SWAP_DWORDS = 1 
   ,localparam DATA_OFFSET_W = $clog2(DATA_WIDTH/32)
   ,localparam DATA_NUM_DWORDS = (DATA_WIDTH/32)

)
(
    input logic clk,
    input logic rst_b,
    input logic zeroize,

    input logic [DATA_OFFSET_W:0] num_dwords,

    //client control register
    input kv_write_ctrl_reg_t write_ctrl_reg,

    //access filtering rule metrics
    //NOTE: must be stabilized 1 clock cycle prior to dest_data_avail
    input var kv_write_filter_metrics_t write_metrics,

    //interface with kv
    output kv_write_t kv_write,
    input  kv_wr_resp_t kv_resp,

    //interface with client
    output logic dest_keyvault,
    input logic dest_data_avail,
    input logic [DATA_NUM_DWORDS-1:0][31:0] dest_data,

    output kv_error_code_e error_code,
    output logic kv_ready,
    output logic dest_done
);

logic write_allow;

logic [DATA_OFFSET_W-1:0] dest_read_offset;
logic [DATA_OFFSET_W-1:0] dest_write_offset;
logic dest_write_en;
logic [31:0] pad_data;
logic write_pad;
logic write_last;

kv_write_rule_check kv_write_rules
(
    .clk  (clk  ),
    .rst_b(rst_b),

    .write_metrics(write_metrics),
    .write_allow  (write_allow  )
);

//dest write block
kv_fsm #(
    .DATA_WIDTH(DATA_WIDTH),
    .PAD(0)
)
kv_dest_write_fsm
(
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize),
    .start(dest_data_avail & write_ctrl_reg.write_en),
    .allow(write_allow),
    .last('0),
    .pcr_hash_extend(1'b0),
    .num_dwords(num_dwords),
    .read_offset(dest_read_offset),
    .write_en(dest_write_en),
    .write_offset(dest_write_offset),
    .write_pad(write_pad),
    .write_last(write_last),
    .pad_data(pad_data),
    .ready(kv_ready),
    .done(dest_done)
);

always_comb dest_keyvault = write_ctrl_reg.write_en;

always_comb kv_write.write_entry = write_ctrl_reg.write_entry;
always_comb kv_write.write_offset = KV_ENTRY_SIZE_W'(dest_write_offset);
always_comb kv_write.write_en = dest_write_en;
always_comb kv_write.write_data = KV_WRITE_SWAP_DWORDS ? dest_data[(DATA_NUM_DWORDS-1) - dest_read_offset] : dest_data[dest_read_offset];
//write zeroes here until last cycle
always_comb kv_write.write_dest_valid = write_last ? write_ctrl_reg.write_dest_vld : '0;

always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        error_code <= KV_SUCCESS;
    end
    else if (zeroize) begin
        error_code <= KV_SUCCESS;
    end
    else begin
        // On first beat of kv write, latch any error conditions.
        // On subsequent beats of kv write, preserve any error that was previously
        // flagged or decode new error conditions
        error_code <= dest_write_en && |dest_write_offset && (error_code != KV_SUCCESS) ? error_code : 
                      dest_data_avail & write_ctrl_reg.write_en & !write_allow ? KV_WRITE_FAIL :
                      dest_write_en & kv_resp.error ? KV_WRITE_FAIL : 
                      dest_write_en & ~kv_resp.error ? KV_SUCCESS : error_code;
    end
end

`CALIPTRA_ASSERT_KNOWN(WRITE_METRICS_X, write_metrics, clk, !rst_b)

endmodule
