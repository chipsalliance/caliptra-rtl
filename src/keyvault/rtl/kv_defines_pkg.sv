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
    logic          error;
} kv_wr_resp_t;

typedef struct packed {
    logic          error;
    logic   [31:0] read_data;
} kv_rd_resp_t;

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
    logic [21:0] rsvd;
    logic [4:0] entry_data_size;
    logic entry_is_pcr;
    logic [2:0] read_entry;
    logic read_en;
} kv_read_ctrl_reg_t;

//control register for KV writes
typedef struct packed {
    logic [20:0] rsvd;
    logic [5:0] write_dest_vld;
    logic entry_is_pcr;
    logic [2:0] write_entry;
    logic write_en;
} kv_write_ctrl_reg_t;

typedef enum logic [7:0] {
    KV_SUCCESS = 8'h00,
    KV_READ_FAIL = 8'h01,
    KV_WRITE_FAIL = 8'h02
} kv_error_code_e;

endpackage

`endif


