`include "kv_defines.svh"

module kv_client #(
    parameter KEY_WIDTH = 384
   ,parameter SRC_WIDTH = 384
   ,parameter DEST_WIDTH = 384
   ,parameter HMAC_PAD = 0

   ,localparam KEY_OFFSET_W = $clog2(KEY_WIDTH/32)
   ,localparam SRC_OFFSET_W = $clog2(SRC_WIDTH/32)
   ,localparam DEST_OFFSET_W = $clog2(DEST_WIDTH/32)
   ,localparam DEST_NUM_DWORDS = (DEST_WIDTH/32)

)
(
    input logic clk,
    input logic rst_b,

    //client control register
    input kv_reg_t client_ctrl_reg,

    //interface with kv
    output kv_read_t kv_read,
    output kv_write_t kv_write,
    input kv_resp_t kv_resp,

    //interface with client
    output logic key_write_en,
    output logic [KEY_OFFSET_W-1:0] key_write_offset,
    output logic [31:0] key_write_data,
    output logic src_write_en,
    output logic [KEY_OFFSET_W-1:0] src_write_offset,
    output logic [31:0] src_write_data,

    output logic dest_keyvault,
    input logic dest_data_avail,
    input logic [DEST_NUM_DWORDS-1:0][31:0] dest_data,

    output logic key_done,
    output logic src_done,
    output logic dest_done
);

logic [KEY_OFFSET_W-1:0] key_read_offset;
logic [SRC_OFFSET_W-1:0] src_read_offset;
logic [DEST_OFFSET_W-1:0] dest_read_offset;
logic [DEST_OFFSET_W-1:0] dest_write_offset;
logic dest_write_en;

//key read block
kv_fsm #(
    .DATA_WIDTH(KEY_WIDTH)
)
kv_key_read_fsm
(
    .clk(clk),
    .rst_b(rst_b),
    .start(client_ctrl_reg.key_sel_en),
    .read_offset(key_read_offset),
    .write_en(key_write_en),
    .write_offset(key_write_offset),
    .done(key_done)
);

always_comb kv_read.key_is_pcr = client_ctrl_reg.key_sel_pcr;
always_comb kv_read.key_entry = client_ctrl_reg.key_sel;
always_comb kv_read.key_offset = key_read_offset;

always_comb key_write_data = kv_resp.key_data;

//src read block
kv_fsm #(
    .DATA_WIDTH(SRC_WIDTH)
)
kv_src_read_fsm
(
    .clk(clk),
    .rst_b(rst_b),
    .start(client_ctrl_reg.src_sel_en),
    .read_offset(src_read_offset),
    .write_en(src_write_en),
    .write_offset(src_write_offset),
    .done(src_done)
);

always_comb kv_read.src_is_pcr = client_ctrl_reg.src_sel_pcr;
always_comb kv_read.src_entry = client_ctrl_reg.src_sel;
always_comb kv_read.src_offset = src_read_offset;

always_comb src_write_data = kv_resp.src_data;

//dest write block
kv_fsm #(
    .DATA_WIDTH(DEST_WIDTH)
)
kv_dest_write_fsm
(
    .clk(clk),
    .rst_b(rst_b),
    .start(dest_data_avail & client_ctrl_reg.dest_sel_en),
    .read_offset(dest_read_offset),
    .write_en(dest_write_en),
    .write_offset(dest_write_offset),
    .done(dest_done)
);

always_comb dest_keyvault = client_ctrl_reg.dest_sel_en;

always_comb kv_write.dest_is_pcr = client_ctrl_reg.dest_sel_pcr;
always_comb kv_write.dest_addr = client_ctrl_reg.dest_sel;
always_comb kv_write.dest_offset = dest_write_offset;
always_comb kv_write.dest_wr_vld = dest_write_en;
always_comb kv_write.dest_data = dest_data[(DEST_NUM_DWORDS-1) - dest_read_offset];

always_comb kv_write.dest_valid = client_ctrl_reg.dest_valid;

endmodule