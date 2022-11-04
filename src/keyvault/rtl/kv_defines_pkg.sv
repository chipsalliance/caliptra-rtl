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
`ifndef KV_DEFINES_PKG
`define KV_DEFINES_PKG

package kv_defines_pkg;

parameter KV_NUM_DWORDS = 16; //number of dwords per key
parameter KV_NUM_KEYS = 8;
parameter KV_NUM_PCR = 8;
parameter KV_ADDR_W = 15;
parameter KV_DATA_W = 32;

typedef struct packed {
    logic   [KV_ADDR_W-1:0] addr;
    logic   [KV_DATA_W-1:0] wdata;
    logic                   write;
} kv_uc_req_t;

typedef struct packed {
    logic          entry_is_pcr;
    logic   [2:0]  read_entry;
    logic   [3:0]  read_offset;
} kv_read_t;

typedef struct packed {
    logic          write_en;
    logic          entry_is_pcr;
    logic   [2:0]  write_entry;
    logic   [3:0]  write_offset;
    logic   [31:0] write_data;
    logic   [5:0]  write_dest_valid;
} kv_write_t;

typedef struct packed {
    logic   [31:0] read_data;
} kv_resp_t;

typedef struct packed {
    logic dest_done;
    logic src_done;
    logic key_done;
    logic [1:0] rsvd1;
    logic [2:0] dest_valid;
    logic [2:0] rsvd_dest_sel;
    logic dest_sel_pcr;
    logic [2:0] dest_sel;
    logic dest_sel_en;
    logic [2:0] src_data_size;
    logic src_sel_pcr;
    logic [2:0] src_sel;
    logic src_sel_en;
    logic [2:0] rsvd_key_sel;
    logic key_sel_pcr;
    logic [2:0] key_sel;
    logic key_sel_en;
} kv_reg_t;

//control register for KV reads
typedef struct packed {
    logic read_done;
    logic [20:0] rsvd;
    logic [4:0] entry_data_size;
    logic entry_is_pcr;
    logic [2:0] read_entry;
    logic read_en;
} kv_read_ctrl_reg_t;

//control register for KV writes
typedef struct packed {
    logic write_done;
    logic [19:0] rsvd;
    logic [5:0] write_dest_vld;
    logic entry_is_pcr;
    logic [2:0] write_entry;
    logic write_en;
} kv_write_ctrl_reg_t;

`define KV_WRITE_CTRL_REG2STRUCT(struct_name, ctrl_reg_name)\
assign struct_name.write_done = hwif_out.``ctrl_reg_name.write_done.value;\
assign struct_name.write_dest_vld[0] = hwif_out.``ctrl_reg_name.hmac_key_dest_valid.value;\
assign struct_name.write_dest_vld[1] = hwif_out.``ctrl_reg_name.hmac_block_dest_valid.value;\
assign struct_name.write_dest_vld[2] = hwif_out.``ctrl_reg_name.sha_block_dest_valid.value;\
assign struct_name.write_dest_vld[3] = hwif_out.``ctrl_reg_name.ecc_pkey_dest_valid.value;\
assign struct_name.write_dest_vld[4] = hwif_out.``ctrl_reg_name.ecc_seed_dest_valid.value;\
assign struct_name.write_dest_vld[5] = hwif_out.``ctrl_reg_name.ecc_msg_dest_valid.value;\
assign struct_name.entry_is_pcr = hwif_out.``ctrl_reg_name.entry_is_pcr.value;\
assign struct_name.write_entry = hwif_out.``ctrl_reg_name.write_entry.value;\
assign struct_name.write_en = hwif_out.``ctrl_reg_name.write_en.value;\

`define KV_READ_CTRL_REG2STRUCT(struct_name, ctrl_reg_name)\
assign struct_name.read_done = hwif_out.``ctrl_reg_name.read_done.value;\
assign struct_name.entry_data_size = hwif_out.``ctrl_reg_name.entry_data_size.value;\
assign struct_name.entry_is_pcr = hwif_out.``ctrl_reg_name.entry_is_pcr.value;\
assign struct_name.read_entry = hwif_out.``ctrl_reg_name.read_entry.value;\
assign struct_name.read_en = hwif_out.``ctrl_reg_name.read_en.value;

endpackage

`endif


