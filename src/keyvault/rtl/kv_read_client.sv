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

module kv_read_client 
    import kv_defines_pkg::*;
    #(
    parameter DATA_WIDTH = 384
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

logic [DATA_OFFSET_W-1:0] read_offset;
logic write_pad;
logic [31:0] pad_data;

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
    .start(read_ctrl_reg.read_en),
    .last (kv_resp.last),
    .pcr_hash_extend(read_ctrl_reg.pcr_hash_extend),
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
always_comb kv_read.read_offset = read_offset[3:0];

always_comb write_data = write_pad ? pad_data : kv_resp.read_data;

always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        error_code <= KV_SUCCESS;
    end
    else if (zeroize) begin
        error_code <= KV_SUCCESS;
    end
    else begin
        error_code <= read_ctrl_reg.read_en & kv_resp.error ? KV_READ_FAIL : 
                      read_ctrl_reg.read_en & ~kv_resp.error ? KV_SUCCESS : error_code;
    end
end

endmodule
