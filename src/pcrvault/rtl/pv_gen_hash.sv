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


`include "caliptra_macros.svh"

module pv_gen_hash  
    import pv_defines_pkg::*;
    #(
     parameter BLOCK_W = 1024
    ,parameter DATA_W = 32
    ,localparam BLOCK_NO = BLOCK_W/DATA_W
    ,localparam BLOCK_OFFSET_W = $clog2(BLOCK_NO)
    ,localparam NONCE_LEN_DWORD = PV_SIZE_OF_NONCE/DATA_W
    ,localparam NONCE_OFFSET_W = $clog2(NONCE_LEN_DWORD)
    )
    (
    input logic clk,
    input logic rst_b,
    input logic zeroize,

    input logic start,
    input logic core_ready,
    input logic core_digest_valid,
    input [NONCE_LEN_DWORD-1:0][DATA_W-1:0] nonce,

    output logic gen_hash_ip,
    output logic gen_hash_init_reg,
    output logic gen_hash_next_reg,
    output logic gen_hash_last_reg,

    output logic block_we,
    output logic [BLOCK_OFFSET_W-1:0] block_offset,
    output logic [DATA_W-1:0] block_wr_data,

    output pv_read_t     pv_read,
    input pv_rd_resp_t pv_rd_resp

);

localparam PAD_LEN_DWORD = BLOCK_NO - 4;

typedef enum logic [3:0] {
    GEN_HASH_IDLE    = 4'b0000,
    GEN_HASH_BLOCK_0 = 4'b0001,
    GEN_HASH_BLOCK_N = 4'b0011,
    GEN_HASH_NONCE   = 4'b0010,
    GEN_HASH_PAD_LD1 = 4'b0110,
    GEN_HASH_PAD_0S  = 4'b0111,
    GEN_HASH_PAD_LEN = 4'b0101,
    GEN_HASH_WT_LAST = 4'b0100,
    GEN_HASH_DONE    = 4'b1100
  } gen_hash_fsm_state_e;

logic init_reg;
logic next_reg;

gen_hash_fsm_state_e gen_hash_fsm_ps, gen_hash_fsm_ns;

logic arc_GEN_HASH_IDLE_GEN_HASH_BLOCK_0;
logic arc_GEN_HASH_BLOCK_0_GEN_HASH_BLOCK_N;
logic arc_GEN_HASH_BLOCK_0_GEN_HASH_NONCE;
logic arc_GEN_HASH_BLOCK_N_GEN_HASH_BLOCK_N;
logic arc_GEN_HASH_BLOCK_N_GEN_HASH_NONCE;
logic arc_GEN_HASH_NONCE_GEN_HASH_PAD_LD1;
logic arc_GEN_HASH_PAD_LD1_GEN_HASH_PAD_0S;
logic arc_GEN_HASH_PAD_0S_GEN_HASH_PAD_LEN;
logic arc_GEN_HASH_PAD_LEN_GEN_HASH_WT_LAST;
logic arc_GEN_HASH_WT_LAST_GEN_HASH_DONE;

logic [3:0][31:0] pad_length;

logic [BLOCK_OFFSET_W:0] block_offset_i,block_offset_nxt;
logic block_full;
logic last_dword_wr;

logic [PV_ENTRY_ADDR_W-1:0]     read_entry, read_entry_nxt;
logic [PV_ENTRY_SIZE_WIDTH-1:0] read_offset, read_offset_nxt;
logic inc_rd_ptr;
logic rst_rd_ptr;

logic [NONCE_OFFSET_W-1:0] nonce_offset_i, nonce_offset_nxt;


assign gen_hash_ip = (gen_hash_fsm_ps != GEN_HASH_IDLE);
assign gen_hash_init_reg = arc_GEN_HASH_BLOCK_0_GEN_HASH_BLOCK_N;
assign gen_hash_next_reg = arc_GEN_HASH_BLOCK_N_GEN_HASH_BLOCK_N | 
                          (block_full & gen_hash_fsm_ps inside {GEN_HASH_NONCE, GEN_HASH_PAD_LD1, GEN_HASH_PAD_0S, GEN_HASH_PAD_LEN} & core_ready);
assign gen_hash_last_reg = gen_hash_fsm_ps == GEN_HASH_WT_LAST;
assign pad_length = (PV_NUM_PCR * PV_NUM_DWORDS * PV_DATA_W) + PV_SIZE_OF_NONCE;

assign block_offset = block_offset_i[BLOCK_OFFSET_W-1:0];

  //PCR read pointer
  always_comb read_offset_nxt = (rst_rd_ptr | (inc_rd_ptr & (read_offset == PV_NUM_DWORDS-1))) ? '0 :
                                inc_rd_ptr ? read_offset + 'd1 : 
                                read_offset;
  always_comb read_entry_nxt = rst_rd_ptr ? '0 :
                               (inc_rd_ptr & (read_offset == PV_NUM_DWORDS-1)) ? read_entry + 'd1 :
                               read_entry;

  always_comb block_we = ~(gen_hash_fsm_ps inside {GEN_HASH_IDLE,GEN_HASH_WT_LAST,GEN_HASH_DONE}) & ~block_full;
  always_comb block_offset_nxt = (gen_hash_fsm_ps != GEN_HASH_IDLE) & block_full & core_ready ? '0 :
                                 (block_we ? block_offset_i + 'd1 : block_offset_i);
  
  always_comb block_full = block_offset_i == BLOCK_NO;
  always_comb last_dword_wr = (read_offset == PV_NUM_DWORDS-1) & (read_entry == PV_NUM_PCR-1);

  always_comb inc_rd_ptr = gen_hash_fsm_ps inside {GEN_HASH_BLOCK_0, GEN_HASH_BLOCK_N} & ~block_full;
  always_comb rst_rd_ptr = arc_GEN_HASH_BLOCK_0_GEN_HASH_NONCE | arc_GEN_HASH_BLOCK_N_GEN_HASH_NONCE;


  always_comb nonce_offset_nxt = (gen_hash_fsm_ps != GEN_HASH_NONCE) ? '0 :
                                 (block_we ? nonce_offset_i + 'd1 : nonce_offset_i);

  //State Machine
  //Start processing
  always_comb arc_GEN_HASH_IDLE_GEN_HASH_BLOCK_0 = (gen_hash_fsm_ps == GEN_HASH_IDLE) & start;
  //Process first full block when full and core is ready
  always_comb arc_GEN_HASH_BLOCK_0_GEN_HASH_BLOCK_N = (gen_hash_fsm_ps == GEN_HASH_BLOCK_0) & block_full & core_ready;
  //Process Nth block when block is full and core is ready
  always_comb arc_GEN_HASH_BLOCK_N_GEN_HASH_BLOCK_N = (gen_hash_fsm_ps == GEN_HASH_BLOCK_N) & block_full & core_ready;
  //Finished reading, start padding - wait for block to process if we need to start a new block
  always_comb arc_GEN_HASH_BLOCK_0_GEN_HASH_NONCE = (gen_hash_fsm_ps == GEN_HASH_BLOCK_0) & ~block_full & last_dword_wr;
  always_comb arc_GEN_HASH_BLOCK_N_GEN_HASH_NONCE = (gen_hash_fsm_ps == GEN_HASH_BLOCK_N) & ~block_full & last_dword_wr;
  always_comb arc_GEN_HASH_NONCE_GEN_HASH_PAD_LD1 = (gen_hash_fsm_ps == GEN_HASH_NONCE) & ~block_full & (nonce_offset_i == NONCE_LEN_DWORD-1);
  always_comb arc_GEN_HASH_PAD_LD1_GEN_HASH_PAD_0S = (gen_hash_fsm_ps == GEN_HASH_PAD_LD1) & ~block_full; 
  //Switch from padding zeros to padding the length                           
  always_comb arc_GEN_HASH_PAD_0S_GEN_HASH_PAD_LEN = (gen_hash_fsm_ps == GEN_HASH_PAD_0S) & ~block_full & (block_offset_i == PAD_LEN_DWORD-1);
  //Move to wait for last state
  always_comb arc_GEN_HASH_PAD_LEN_GEN_HASH_WT_LAST = (gen_hash_fsm_ps == GEN_HASH_PAD_LEN) & block_full & core_ready;
  //move to done when finished processing the last block
  always_comb arc_GEN_HASH_WT_LAST_GEN_HASH_DONE = (gen_hash_fsm_ps == GEN_HASH_WT_LAST) & core_digest_valid;

  //GEN_HASH API FSM State Combo
  always_comb begin : sha_api_combo
    //default back to present state
    gen_hash_fsm_ns = gen_hash_fsm_ps;
    block_wr_data = '0;

    unique case (gen_hash_fsm_ps) inside
      GEN_HASH_IDLE: begin
        if (arc_GEN_HASH_IDLE_GEN_HASH_BLOCK_0) gen_hash_fsm_ns = GEN_HASH_BLOCK_0;
      end
      GEN_HASH_BLOCK_0: begin
        if (arc_GEN_HASH_BLOCK_0_GEN_HASH_BLOCK_N) gen_hash_fsm_ns = GEN_HASH_BLOCK_N;
        else if (arc_GEN_HASH_BLOCK_0_GEN_HASH_NONCE) gen_hash_fsm_ns = GEN_HASH_NONCE;
        block_wr_data = pv_rd_resp.read_data;
      end
      GEN_HASH_BLOCK_N: begin
        if (arc_GEN_HASH_BLOCK_N_GEN_HASH_BLOCK_N) gen_hash_fsm_ns = GEN_HASH_BLOCK_N;
        else if (arc_GEN_HASH_BLOCK_N_GEN_HASH_NONCE) gen_hash_fsm_ns = GEN_HASH_NONCE;
        block_wr_data = pv_rd_resp.read_data;
      end
      GEN_HASH_NONCE: begin
        if (arc_GEN_HASH_NONCE_GEN_HASH_PAD_LD1) gen_hash_fsm_ns = GEN_HASH_PAD_LD1;
        block_wr_data = nonce[NONCE_LEN_DWORD-1-nonce_offset_i];
      end
      GEN_HASH_PAD_LD1: begin
        if (arc_GEN_HASH_PAD_LD1_GEN_HASH_PAD_0S) gen_hash_fsm_ns = GEN_HASH_PAD_0S;
        block_wr_data = 'h8000_0000;
      end
      GEN_HASH_PAD_0S: begin
        if (arc_GEN_HASH_PAD_0S_GEN_HASH_PAD_LEN) gen_hash_fsm_ns = GEN_HASH_PAD_LEN;
        block_wr_data = 'h0000_0000;
      end
      GEN_HASH_PAD_LEN: begin
        if (arc_GEN_HASH_PAD_LEN_GEN_HASH_WT_LAST) gen_hash_fsm_ns = GEN_HASH_WT_LAST;
        block_wr_data = pad_length[3-block_offset_i[1:0]];
      end
      GEN_HASH_WT_LAST: begin
        if (arc_GEN_HASH_WT_LAST_GEN_HASH_DONE) gen_hash_fsm_ns = GEN_HASH_DONE;
      end
      GEN_HASH_DONE: begin
        gen_hash_fsm_ns = GEN_HASH_IDLE;
      end
      default: begin
        //TODO Error condition
        gen_hash_fsm_ns = GEN_HASH_IDLE;
      end
    endcase
  end

  assign pv_read.read_entry = read_entry;
  assign pv_read.read_offset = read_offset;

  always_ff @(posedge clk or negedge rst_b) begin : api_regs
    if (~rst_b) begin
      gen_hash_fsm_ps <= GEN_HASH_IDLE;
      block_offset_i <= '0;
      nonce_offset_i <= '0;
      read_entry <= '0;
      read_offset <= '0;
    end
    else if (zeroize) begin
      gen_hash_fsm_ps <= GEN_HASH_IDLE;
      block_offset_i <= '0;
      nonce_offset_i <= '0;
      read_entry <= '0;
      read_offset <= '0;
    end
    else begin
      gen_hash_fsm_ps <= gen_hash_fsm_ns;
      block_offset_i <= block_offset_nxt;
      nonce_offset_i <= nonce_offset_nxt;
      read_entry <= read_entry_nxt;
      read_offset <= read_offset_nxt;
    end
  end

endmodule
