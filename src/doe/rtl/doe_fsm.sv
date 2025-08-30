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

module doe_fsm 
    import doe_defines_pkg::*;
    import kv_defines_pkg::*;
    #(
    parameter SRC_WIDTH = 128
   ,parameter DEST_WIDTH = 128
    //derived params don't change
   ,localparam DEST_OFFSET_W   = $clog2(DEST_WIDTH/32)
   ,localparam DEST_NUM_DWORDS = (DEST_WIDTH/32)
   ,localparam TOTAL_OBF_FE_BITS = `CLP_OBF_FE_DWORDS * 32
   ,localparam TOTAL_OBF_UDS_BITS = `CLP_OBF_UDS_DWORDS * 32
   ,localparam TOTAL_OBF_HEK_BITS = OCP_LOCK_HEK_NUM_DWORDS * 32
   ,localparam FE_NUM_BLOCKS   = TOTAL_OBF_FE_BITS/SRC_WIDTH
   ,localparam UDS_NUM_BLOCKS  = TOTAL_OBF_UDS_BITS/SRC_WIDTH
   ,localparam HEK_NUM_BLOCKS  = TOTAL_OBF_HEK_BITS/SRC_WIDTH
)
(
    input logic clk,
    input logic rst_b,
    input logic hard_rst_b,

    //Obfuscated UDS and FE
    input logic [FE_NUM_BLOCKS-1:0][SRC_WIDTH-1:0] obf_field_entropy,
    input logic [UDS_NUM_BLOCKS-1:0][SRC_WIDTH-1:0] obf_uds_seed,
    input logic [HEK_NUM_BLOCKS-1:0][SRC_WIDTH-1:0] obf_hek_seed,

    //client control register
    input doe_cmd_reg_t doe_cmd_reg,
    input logic         ocp_lock_en,

    //interface with kv
    output kv_write_t kv_write,

    //interface with client
    output logic src_write_en,
    output logic [SRC_WIDTH-1:0] src_write_data,

    output logic doe_init,
    output logic doe_next,

    input logic init_done,
    input logic dest_data_avail,
    input logic [DEST_NUM_DWORDS-1:0][31:0] dest_data,

    output logic flow_done,
    output logic flow_error,
    output logic flow_in_progress,
    output logic lock_uds_flow,
    output logic lock_fe_flow,
    output logic lock_hek_flow,
    input  logic zeroize
);

`define CLP_MAX_OF(a,b) ((a > b) ? a : b)

localparam UDS_BLOCK_OFFSET_W = $clog2(UDS_NUM_BLOCKS);
localparam FE_BLOCK_OFFSET_W = $clog2(FE_NUM_BLOCKS);
localparam HEK_BLOCK_OFFSET_W = $clog2(HEK_NUM_BLOCKS);
localparam BLOCK_OFFSET_W = `CLP_MAX_OF(HEK_BLOCK_OFFSET_W, `CLP_MAX_OF(FE_BLOCK_OFFSET_W, UDS_BLOCK_OFFSET_W));
localparam DEST_WR_OFFSET_W = $clog2(512/32);

//declare fsm state variables
typedef enum logic [2:0] {
    DOE_IDLE    = 3'b000,
    DOE_INIT    = 3'b001,
    DOE_BLOCK   = 3'b011,
    DOE_NEXT    = 3'b010,
    DOE_WAIT    = 3'b110,
    DOE_WRITE   = 3'b100,
    DOE_DONE    = 3'b101
} kv_doe_fsm_state_e;

logic running_uds, running_fe, running_hek;

//access filtering rule metrics
//NOTE: must be stabilized 1 clock cycle prior to dest_data_avail
kv_write_filter_metrics_t kv_write_metrics;
logic                     kv_write_allow;

logic [KV_ENTRY_ADDR_W-1:0] dest_addr, dest_addr_nxt;
logic dest_addr_en;
logic [DEST_WR_OFFSET_W-1:0] dest_write_offset, dest_write_offset_nxt;
logic dest_write_offset_en;
logic dest_write_en;
logic dest_write_done;

logic [BLOCK_OFFSET_W-1:0] block_offset, block_offset_nxt;
logic block_offset_en;
logic block_done;
logic zeroize_reg;

kv_doe_fsm_state_e kv_doe_fsm_ps, kv_doe_fsm_ns;
logic arc_DOE_IDLE_DOE_INIT;
logic arc_DOE_WAIT_DOE_BLOCK;
logic arc_DOE_WAIT_DOE_WRITE;
logic arc_DOE_WRITE_DOE_BLOCK;
logic arc_DOE_WRITE_DOE_DONE;

//zeroize input is a single pulse. However, when we detect zeroize, we'd like the fsm
//to remain in IDLE until next DOE_CMD is issued. To avoid other arcs moving the fsm
//to other states, extending zeroize to a level so we can keep the fsm in IDLE. When the
//next command is issued, this extended signal is reset and fsm advances.
always_ff @(posedge clk or negedge rst_b) begin
    if (~rst_b) begin
        zeroize_reg <= 0;
    end
    else if (zeroize) begin
        zeroize_reg <= 1;
    end
    else if (running_uds || running_fe || running_hek) begin
        zeroize_reg <= 0;
    end
end

always_comb running_uds = (doe_cmd_reg.cmd == DOE_UDS);
always_comb running_fe  = (doe_cmd_reg.cmd == DOE_FE );
always_comb running_hek = (doe_cmd_reg.cmd == DOE_HEK);
always_comb block_done = running_uds ? (block_offset == (UDS_NUM_BLOCKS-1)) :
                         running_hek ? (block_offset == (HEK_NUM_BLOCKS-1)) :
                                       (block_offset == (FE_NUM_BLOCKS -1)) ;

always_comb flow_in_progress = running_uds | running_fe | running_hek;
always_comb dest_write_done = (dest_write_offset[DEST_OFFSET_W-1:0] == (DEST_NUM_DWORDS-1));

//assign arc equations
//move to init state when command is set and that command isn't locked
always_comb arc_DOE_IDLE_DOE_INIT = (running_uds & ~lock_uds_flow) |
                                    (running_fe  & ~lock_fe_flow ) |
                                    (running_hek & ~lock_hek_flow);
//wait to write when init is done and we have data to write
always_comb arc_DOE_WAIT_DOE_WRITE = init_done & dest_data_avail;
//wait to block when init is done and no data
always_comb arc_DOE_WAIT_DOE_BLOCK = init_done & ~dest_data_avail;
//done with this phase, but not done with the whole block
always_comb arc_DOE_WRITE_DOE_BLOCK = dest_write_done & ~block_done;
//done with this phase and the block is complete
always_comb arc_DOE_WRITE_DOE_DONE = dest_write_done & block_done;

//state combo block
always_comb begin : kv_doe_fsm
    kv_doe_fsm_ns = kv_doe_fsm_ps;
    src_write_en = '0;
    block_offset_nxt = block_offset;
    block_offset_en = '0;
    doe_init = '0;
    doe_next = '0;
    dest_write_en = '0;
    dest_write_offset_en ='0;
    dest_write_offset_nxt = dest_write_offset;
    flow_done = '0;
    flow_error = '0;

    unique case (kv_doe_fsm_ps)
        DOE_IDLE: begin
            if (arc_DOE_IDLE_DOE_INIT) kv_doe_fsm_ns = DOE_INIT;
            //assert flow done if a locked flow is attempted
            flow_done = (running_uds & lock_uds_flow) | (running_fe & lock_fe_flow) | (running_hek & lock_hek_flow);
        end
        DOE_INIT: begin
            kv_doe_fsm_ns = DOE_WAIT;
            doe_init = '1;
        end
        DOE_BLOCK: begin
            kv_doe_fsm_ns = DOE_NEXT;
            src_write_en = '1;
        end
        DOE_NEXT: begin
            kv_doe_fsm_ns = DOE_WAIT;
            doe_next = '1;
        end
        DOE_WAIT: begin
            if (arc_DOE_WAIT_DOE_WRITE) kv_doe_fsm_ns = DOE_WRITE;
            else if (arc_DOE_WAIT_DOE_BLOCK) kv_doe_fsm_ns = DOE_BLOCK;
        end
        DOE_WRITE: begin
            dest_write_en = kv_write_allow; // If rule-check fails, no data is written to KV and FSM hangs in this state
            //increment dest offset each clock, clear when done
            dest_write_offset_en = kv_write_allow;
            dest_write_offset_nxt = dest_write_offset + 'd1;
            flow_error = !kv_write_allow;

            //go back to idle if dest done, and done with blocks
            if (arc_DOE_WRITE_DOE_DONE) kv_doe_fsm_ns = DOE_DONE;
            //go back to block stage for next block if not done with blocks
            else if (arc_DOE_WRITE_DOE_BLOCK) begin 
                kv_doe_fsm_ns = DOE_BLOCK;
                //increment the block offset each time we write a block
                block_offset_en = '1;
                block_offset_nxt = block_offset + 'd1;
            end
        end
        DOE_DONE: begin
            kv_doe_fsm_ns = DOE_IDLE;
            flow_done = '1;
            //clear block and write offsets when we go back to idle
            block_offset_en = '1;
            block_offset_nxt = '0;
            dest_write_offset_en = '1;
            dest_write_offset_nxt = '0;
        end
        default: begin
            kv_doe_fsm_ns = kv_doe_fsm_ps;
            src_write_en = '0;
            block_offset_nxt = block_offset;
            block_offset_en = '0;
            doe_init = '0;
            doe_next = '0;
            dest_write_en = '0;
            dest_write_offset_en ='0;
            dest_write_offset_nxt = dest_write_offset;
            flow_done = '0;
            flow_error = '0;
        end
    endcase
end

//latch the dest addr when starting, and when we roll over dest offset
always_comb dest_addr_en = ((kv_doe_fsm_ps == DOE_IDLE) & arc_DOE_IDLE_DOE_INIT);
always_comb dest_addr_nxt = doe_cmd_reg.dest_sel;

// check KV filtering rules
// Use the strap ocp_lock_en instead of the register ocp_lock_in_progress because DOE
// is a ROM flow and occurs prior to setting the register
always_comb begin
    `ifdef CALIPTRA_MODE_SUBSYSTEM
    kv_write_metrics.ocp_lock_in_progress = ocp_lock_en;
    `else
    kv_write_metrics.ocp_lock_in_progress = 1'b0;
    `endif
    kv_write_metrics.kv_data0_present     = 1'b0;
    kv_write_metrics.kv_data0_entry       = '0;
    kv_write_metrics.kv_data1_present     = 1'b0;
    kv_write_metrics.kv_data1_entry       = '0;
    kv_write_metrics.kv_write_src         = KV_NUM_WRITE'(1 << KV_WRITE_IDX_DOE);
    kv_write_metrics.kv_write_entry       = dest_addr;
    kv_write_metrics.aes_decrypt_ecb_op   = 1'b0;
end

// Output kv_write_allow will stabilize by first entry to DOE_WAIT
kv_write_rule_check kv_write_rules
(
    .clk  (clk  ),
    .rst_b(rst_b),

    .write_metrics(kv_write_metrics),
    .write_allow  (kv_write_allow  )
);

//drive outputs to kv
always_comb kv_write.write_en = dest_write_en;
always_comb kv_write.write_offset = dest_write_offset;
always_comb kv_write.write_dest_valid = running_hek ? OCP_LOCK_HEK_SEED_DEST_VALID : 'd3; //FIXME tie off dest valid, or let FW program? 
always_comb kv_write.write_entry = dest_addr;
//swizzle big endian result to little endian storage
always_comb kv_write.write_data = dest_write_en ? dest_data[(DEST_NUM_DWORDS-1) - dest_write_offset[DEST_OFFSET_W-1:0]] : '0;

//pick among uds, fe, hek based on command
always_comb src_write_data = running_uds ? obf_uds_seed[block_offset[UDS_BLOCK_OFFSET_W-1:0]] : 
                             running_fe  ? obf_field_entropy[block_offset[FE_BLOCK_OFFSET_W-1:0]] : 
                             running_hek ? obf_hek_seed[block_offset[HEK_BLOCK_OFFSET_W-1:0]] : '0;

//state flops
always_ff @(posedge clk or negedge rst_b) begin
    if (~rst_b) begin
        kv_doe_fsm_ps <= DOE_IDLE;
        dest_write_offset <= '0;
        block_offset <= '0;
        dest_addr <= '0;
    end
    else if (zeroize_reg) begin
        kv_doe_fsm_ps <= DOE_IDLE;
        dest_write_offset <= '0;
        block_offset <= '0;
        dest_addr <= '0;
    end
    else begin
        kv_doe_fsm_ps <= kv_doe_fsm_ns;
        dest_write_offset <= dest_write_offset_en ? dest_write_offset_nxt : dest_write_offset;
        block_offset <= block_offset_en ? block_offset_nxt : block_offset;
        dest_addr <= dest_addr_en ? dest_addr_nxt : dest_addr;
    end
end

//sticky flops for locking UDS/FE/HEK flow after execution
always_ff @(posedge clk or negedge hard_rst_b) begin
    if (~hard_rst_b) begin
        lock_uds_flow <= '0;
        lock_fe_flow <= '0;
        lock_hek_flow <= '0;
    end
    else begin
        lock_uds_flow <= running_uds & flow_done ? '1 : lock_uds_flow;
        lock_fe_flow <= running_fe & flow_done ? '1 : lock_fe_flow;
        lock_hek_flow <= running_hek & flow_done ? '1 : lock_hek_flow;
    end
end

endmodule
