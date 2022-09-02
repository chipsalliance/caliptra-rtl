`include "kv_defines.svh"

module kv_fsm #(
    parameter DATA_WIDTH = 384
   ,parameter HMAC_PAD = 0
   ,localparam OFFSET_W = $clog2(DATA_WIDTH/32)
)
(
    input logic clk,
    input logic rst_b,

    input logic start,

    output logic [OFFSET_W-1:0] read_offset,

    output logic write_en,
    output logic [OFFSET_W-1:0] write_offset,

    output logic done
);

localparam KV_NUM_DWORDS = DATA_WIDTH/32;

//declare fsm state variables
typedef enum logic [1:0] {
    KV_IDLE   = 2'b00,
    KV_RW     = 2'b01,
    KV_DONE   = 2'b11
} kv_fsm_state_e;

kv_fsm_state_e kv_fsm_ps, kv_fsm_ns;
logic arc_KV_IDLE_KV_RW;
logic arc_KV_RW_KV_DONE;
logic arc_KV_DONE_KV_IDLE;

logic offset_en;
logic [OFFSET_W-1:0] offset, offset_nxt;

always_comb arc_KV_IDLE_KV_RW = start;
always_comb arc_KV_RW_KV_DONE = (offset_nxt == KV_NUM_DWORDS);
always_comb arc_KV_DONE_KV_IDLE = '1;

always_comb begin : kv_fsm
    kv_fsm_ns = kv_fsm_ps;
    write_en = '0;
    offset_en = '0;
    offset_nxt = '0;
    done = '0;
    unique casez (kv_fsm_ps)
        KV_IDLE: begin
            if (arc_KV_IDLE_KV_RW) kv_fsm_ns = KV_RW;
        end
        KV_RW: begin
            if (arc_KV_RW_KV_DONE) kv_fsm_ns = KV_DONE;
            write_en = '1;
            offset_en = '1;
            offset_nxt = offset + 'd1;
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

`CLP_RSTD_FF(kv_fsm_ps, kv_fsm_ns, clk, rst_b, KV_IDLE)
`CLP_EN_RST_FF(offset, offset_nxt, clk, offset_en, rst_b)

always_comb read_offset = offset;
always_comb write_offset = offset;

endmodule