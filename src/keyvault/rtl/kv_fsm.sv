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

module kv_fsm 
    import kv_defines_pkg::*;
    #(
    parameter DATA_WIDTH = 512
   ,parameter PAD = 0
   ,parameter HMAC = 0
   ,localparam OFFSET_W = $clog2(DATA_WIDTH/32)
)
(
    input logic clk,
    input logic rst_b,
    input logic zeroize,

    input logic start,
    input logic allow,
    input logic last,

    input logic pcr_hash_extend,
    input logic [OFFSET_W:0] num_dwords,

    output logic [OFFSET_W-1:0] read_offset,

    output logic write_en,
    output logic [OFFSET_W-1:0] write_offset,
    output logic write_pad,
    output logic [31:0] pad_data,
    output logic write_last,

    output logic ready,

    output logic done,
    output logic fsm_error
);
//max dwords for SHA/HMAC blocks that need padding
localparam KV_MAX_DWORDS = 1024/32;
localparam KV_NUM_DWORDS_W = $clog2(KV_MAX_DWORDS);
localparam KV_PAD_LENGTH_START = 28;

logic [KV_NUM_DWORDS_W:0] num_dwords_data;
logic [KV_NUM_DWORDS_W:0] num_dwords_total;
logic [31:0] length_for_pad;

//declare fsm state variables
// Encoding generated with
// $ python3 sparse_fsm_encode.py -d 5 -m 7 -n 10 -s 27182818
//
// Minimum Hamming distance: 5
// Maximum Hamming distance: 7
//
localparam int KvStateWidth = 10;
typedef enum logic [KvStateWidth-1:0] {
    KV_IDLE   = 10'b1011010011,
    KV_RW     = 10'b0101000111,
    KV_PAD    = 10'b1110100100,
    KV_ZERO   = 10'b1001101001,
    KV_LENGTH = 10'b0111111010,
    KV_DONE   = 10'b0010011101,
    KV_ERROR  = 10'b1100011110
} kv_fsm_state_e;

kv_fsm_state_e kv_fsm_ps, kv_fsm_ns;
logic arc_KV_IDLE_KV_RW;
logic arc_KV_IDLE_KV_DONE;
logic arc_KV_RW_KV_DONE;
logic arc_KV_DONE_KV_IDLE;
logic arc_KV_RW_KV_PAD;
logic arc_KV_PAD_KV_ZERO;
logic arc_KV_ZERO_KV_LENGTH;
logic arc_KV_LENGTH_KV_DONE;

logic offset_en;
logic offset_rst;
logic [OFFSET_W:0] offset, offset_nxt;

assign num_dwords_total = pcr_hash_extend ? 'd12 :
                          ((PAD == 1) ? KV_MAX_DWORDS : $bits(num_dwords_total)'(num_dwords));

always_comb ready = (kv_fsm_ps == KV_IDLE);

// For SHA and HMAC Block -
// Padding starts with a leading 1 after the valid data followed by 0's until 
// the length of the valid data is stored in the last 4 dwords.
// HMAC adds 1024 bits to the length to account for the key
always_comb length_for_pad = (HMAC == 1) ? (32'b0 | ((num_dwords_data << 5) + 'd1024)) : (32'b0 | (num_dwords_data << 5));

always_comb arc_KV_IDLE_KV_RW = start && allow;
always_comb arc_KV_IDLE_KV_DONE = start && !allow;
always_comb arc_KV_RW_KV_DONE = ((PAD == 0) | pcr_hash_extend) & (($bits(num_dwords_total)'(offset) == (num_dwords_total-1)) | last); //jump to done when we've written all dwords
always_comb arc_KV_RW_KV_PAD  = ((PAD == 1) & ~pcr_hash_extend) & last; //jump to pad when data is done
always_comb arc_KV_PAD_KV_ZERO = (PAD == 1) && (kv_fsm_ps == KV_PAD);
always_comb arc_KV_ZERO_KV_LENGTH = (PAD == 1) && ($bits(num_dwords_total)'(offset_nxt) == 'd31); //jump to length when it's time to append length in the last dword
always_comb arc_KV_LENGTH_KV_DONE = (PAD == 1) && (kv_fsm_ps == KV_LENGTH);
always_comb arc_KV_DONE_KV_IDLE = '1;

always_comb offset_rst = arc_KV_RW_KV_DONE | arc_KV_LENGTH_KV_DONE;
always_comb write_last = arc_KV_RW_KV_DONE | arc_KV_LENGTH_KV_DONE;

always_comb begin : kv_fsm_comb
    kv_fsm_ns = kv_fsm_ps;
    write_en = '0;
    write_pad = '0;
    offset_en = '0;
    offset_nxt = '0;
    pad_data = '0;
    done = '0;
    fsm_error = '0;
    unique case (kv_fsm_ps)
        KV_IDLE: begin
            if      (zeroize) kv_fsm_ns = KV_IDLE;
            else if(arc_KV_IDLE_KV_RW)   kv_fsm_ns = KV_RW;
            else if (arc_KV_IDLE_KV_DONE) kv_fsm_ns = KV_DONE;
        end
        KV_RW: begin
            if      (zeroize) kv_fsm_ns = KV_IDLE;
            else if (arc_KV_RW_KV_PAD) kv_fsm_ns = KV_PAD;
            else if (arc_KV_RW_KV_DONE) kv_fsm_ns = KV_DONE;
            write_en = '1;
            offset_en = '1;
            offset_nxt = offset + 'd1;
        end
        KV_PAD: begin
            if      (zeroize) kv_fsm_ns = KV_IDLE;
            else if (arc_KV_PAD_KV_ZERO) kv_fsm_ns = KV_ZERO;
            write_en = '1;
            offset_en = '1;
            offset_nxt = offset + 'd1;
            write_pad = '1;
            pad_data = 32'h8000_0000;
        end
        KV_ZERO: begin
            if      (zeroize) kv_fsm_ns = KV_IDLE;
            else if (arc_KV_ZERO_KV_LENGTH) kv_fsm_ns = KV_LENGTH;
            write_en = '1;
            offset_en = '1;
            offset_nxt = offset + 'd1;
            write_pad = '1;
            pad_data = '0;
        end
        KV_LENGTH: begin
            if      (zeroize) kv_fsm_ns = KV_IDLE;
            else if (arc_KV_LENGTH_KV_DONE) kv_fsm_ns = KV_DONE;
            write_en = '1;
            offset_en = '1;
            offset_nxt = offset + 'd1;
            write_pad = '1;
            pad_data = length_for_pad;
        end
        KV_DONE: begin
            if (arc_KV_DONE_KV_IDLE) kv_fsm_ns = KV_IDLE;
            done = '1;
        end
        KV_ERROR: begin
            kv_fsm_ns = KV_ERROR; // Terminal — sticky until reset
            fsm_error = 1'b1;
        end
        default: begin
            kv_fsm_ns = KV_ERROR; // Invalid encoding detected
            fsm_error = 1'b1;
        end
    endcase
end

// Sparse FSM flop for glitch hardening (invalid encoding -> KV_ERROR)
`CALIPTRA_PRIM_FLOP_SPARSE_FSM(u_kv_state_regs, kv_fsm_ns, kv_fsm_ps, kv_fsm_state_e, KV_IDLE, clk, rst_b)

always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        offset <= '0;
    end
    else if (zeroize) begin
        offset <= '0;
    end
    else begin
        offset <= offset_rst ? '0 :
                  offset_en ? offset_nxt : offset;
    end
end

generate
    if (PAD==1) begin
        always_ff @(posedge clk or negedge rst_b) begin
            if (!rst_b) begin
                num_dwords_data <= '0;
            end
            else if (zeroize) begin
                num_dwords_data <= '0;
            end
            else begin
                //store the offset_nxt on the last cycle of valid data, this is the number of dwords of valid data
                num_dwords_data <= arc_KV_RW_KV_PAD ? $bits(num_dwords_data)'(offset_nxt) : num_dwords_data;
            end
        end
    end else begin
        always_comb num_dwords_data = '0;
    end
endgenerate

always_comb read_offset = (kv_fsm_ps == KV_RW) ? offset[OFFSET_W-1:0] : '0;
always_comb write_offset = offset[OFFSET_W-1:0];

endmodule
