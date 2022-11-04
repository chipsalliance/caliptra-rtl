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
   ,parameter PAD = 0

   ,localparam DATA_OFFSET_W = $clog2(DATA_WIDTH/32)
)
(
    input logic clk,
    input logic rst_b,

    //client control register
    input kv_read_ctrl_reg_t read_ctrl_reg,

    //interface with kv
    output kv_read_t kv_read,
    input kv_resp_t kv_resp,

    //interface with client
    output logic write_en,
    output logic [DATA_OFFSET_W-1:0] write_offset,
    output logic [31:0] write_data,

    output logic read_done
);

logic [DATA_OFFSET_W-1:0] read_offset;
logic write_pad;
logic [31:0] pad_data;

//read fsm
kv_fsm #(
    .DATA_WIDTH(DATA_WIDTH),
    .PAD(PAD)
)
kv_read_fsm
(
    .clk(clk),
    .rst_b(rst_b),
    .pad_data_size(read_ctrl_reg.entry_data_size),
    .start(read_ctrl_reg.read_en),
    .read_offset(read_offset),
    .write_en(write_en),
    .write_offset(write_offset),
    .write_pad(write_pad),
    .pad_data(pad_data),
    .done(read_done)
);

always_comb kv_read.entry_is_pcr = read_ctrl_reg.entry_is_pcr;
always_comb kv_read.read_entry = (PAD == 1) ? read_ctrl_reg.read_entry + read_offset[DATA_OFFSET_W-1] : read_ctrl_reg.read_entry;
always_comb kv_read.read_offset = read_offset[3:0];

always_comb write_data = write_pad ? pad_data : kv_resp.read_data;

endmodule
