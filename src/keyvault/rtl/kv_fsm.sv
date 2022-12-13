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

module kv_fsm 
    import kv_defines_pkg::*;
    #(
    parameter DATA_WIDTH = 384
   ,parameter PAD = 0
   ,localparam OFFSET_W = $clog2(DATA_WIDTH/32)
)
(
    input logic clk,
    input logic rst_b,

    input logic start,
    input logic [4:0] pad_data_size,

    output logic [OFFSET_W-1:0] read_offset,

    output logic write_en,
    output logic [OFFSET_W-1:0] write_offset,
    output logic write_pad,
    output logic [31:0] pad_data,

    output logic ready,

    output logic done
);

localparam KV_MAX_DWORDS = 1024/32;
localparam KV_NUM_DWORDS_W = $clog2(KV_MAX_DWORDS);

logic [KV_NUM_DWORDS_W:0] num_dwords_data;
logic [KV_NUM_DWORDS_W:0] num_dwords_total;
logic [31:0][31:0] full_pad_data;

//declare fsm state variables
typedef enum logic [1:0] {
    KV_IDLE   = 2'b00,
    KV_RW     = 2'b01,
    KV_PAD    = 2'b11,
    KV_DONE   = 2'b10
} kv_fsm_state_e;

kv_fsm_state_e kv_fsm_ps, kv_fsm_ns;
logic arc_KV_IDLE_KV_RW;
logic arc_KV_RW_KV_DONE;
logic arc_KV_DONE_KV_IDLE;
logic arc_KV_RW_KV_PAD;
logic arc_KV_PAD_KV_DONE;

logic offset_en;
logic [KV_NUM_DWORDS_W:0] offset, offset_nxt;

//hmac data size is encoded as N-1 128b chunks, add 1 and multiply by 4 to get dwords
//data width is in bits, divide by 32 to get dwords
assign num_dwords_data = (PAD == 1) ? ((pad_data_size+1)) : DATA_WIDTH/32;
assign num_dwords_total = (PAD == 1) ? KV_MAX_DWORDS : DATA_WIDTH/32;

always_comb ready = (kv_fsm_ps == KV_IDLE);

always_comb begin
    full_pad_data = '0;
    full_pad_data[31] = pad_data_size < 27 ? num_dwords_data*32 + 'd1024 : '0; //size of data goes in the last dword if we have room after pad
    full_pad_data[num_dwords_data[KV_NUM_DWORDS_W-1:0]] = 32'h8000_0000; //insert start of pad at dword immediately following data size
end



always_comb arc_KV_IDLE_KV_RW = start;
always_comb arc_KV_RW_KV_DONE = (offset_nxt == num_dwords_total); //jump to done when we've written all dwords
always_comb arc_KV_RW_KV_PAD = (PAD == 1) & (offset_nxt == num_dwords_data); //jump to pad when data is done, but not full block size
always_comb arc_KV_PAD_KV_DONE = (offset_nxt == num_dwords_total); 
always_comb arc_KV_DONE_KV_IDLE = '1;

always_comb begin : kv_fsm_comb
    kv_fsm_ns = kv_fsm_ps;
    write_en = '0;
    write_pad = '0;
    offset_en = '0;
    offset_nxt = '0;
    done = '0;
    unique casez (kv_fsm_ps)
        KV_IDLE: begin
            if (arc_KV_IDLE_KV_RW) kv_fsm_ns = KV_RW;
        end
        KV_RW: begin
            if (arc_KV_RW_KV_PAD) kv_fsm_ns = KV_PAD;
            if (arc_KV_RW_KV_DONE) kv_fsm_ns = KV_DONE;
            write_en = '1;
            offset_en = '1;
            offset_nxt = offset + 'd1;
        end
        KV_PAD: begin
            if (arc_KV_PAD_KV_DONE) kv_fsm_ns = KV_DONE;
            write_en = '1;
            offset_en = '1;
            offset_nxt = offset + 'd1;
            write_pad = '1;
        end
        KV_DONE: begin
            if (arc_KV_DONE_KV_IDLE) kv_fsm_ns = KV_IDLE;
            write_en = '0;
            offset_en = '1;
            offset_nxt = '0;
            done = '1;
        end
        default: begin
        end
    endcase
end

always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        kv_fsm_ps <= KV_IDLE;
        offset <= '0;
    end
    else begin
        kv_fsm_ps <= kv_fsm_ns;
        offset <= offset_en ? offset_nxt : offset;
    end
end

always_comb read_offset = offset[OFFSET_W-1:0];
always_comb write_offset = offset[OFFSET_W-1:0];

always_comb pad_data = full_pad_data[offset[KV_NUM_DWORDS_W-1:0]];

endmodule
