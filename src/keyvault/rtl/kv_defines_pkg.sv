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
`ifndef CALIPTRA_KV_DEFINES_PKG
`define CALIPTRA_KV_DEFINES_PKG

package kv_defines_pkg;

parameter KV_NUM_DWORDS = 12; //number of dwords per key
parameter KV_NUM_KEYS = 32;
parameter KV_ADDR_W = 13;
parameter KV_DATA_W = 32;
parameter KV_ENTRY_ADDR_W = $clog2(KV_NUM_KEYS);
parameter KV_ENTRY_SIZE_W = $clog2(KV_NUM_DWORDS);
parameter KV_NUM_READ=5;
parameter KV_NUM_WRITE=4;

parameter KV_ENTRY_FOR_SIGNING = 7;

typedef struct packed {
    logic   [KV_ADDR_W-1:0] addr;
    logic   [KV_DATA_W-1:0] wdata;
    logic                   write;
} kv_uc_req_t;

typedef struct packed {
    logic   [KV_ENTRY_ADDR_W-1:0] read_entry;
    logic   [KV_ENTRY_SIZE_W-1:0] read_offset;
} kv_read_t;

typedef struct packed {
    logic                         write_en;
    logic   [KV_ENTRY_ADDR_W-1:0] write_entry;
    logic   [KV_ENTRY_SIZE_W-1:0] write_offset;
    logic   [KV_DATA_W-1:0]       write_data;
    logic   [KV_NUM_READ-1:0]     write_dest_valid;
} kv_write_t;

typedef struct packed {
    logic          error;
} kv_wr_resp_t;

typedef struct packed {
    logic                   error;
    logic                   last;
    logic   [KV_DATA_W-1:0] read_data;
} kv_rd_resp_t;

//control register for KV reads
localparam KV_READ_CTRL_RSVD_MSB = 32 - KV_ENTRY_SIZE_W - 1 - 1;
typedef struct packed {
    logic [KV_READ_CTRL_RSVD_MSB:0] rsvd;
    logic [KV_ENTRY_ADDR_W-1:0] read_entry;
    logic pcr_hash_extend;
    logic read_en;
} kv_read_ctrl_reg_t;

//control register for KV writes
localparam KV_WRITE_CTRL_RSVD_MSB = 32 - KV_NUM_READ - KV_ENTRY_ADDR_W - 1;
typedef struct packed {
    logic [KV_WRITE_CTRL_RSVD_MSB:0] rsvd;
    logic [KV_NUM_READ-1:0] write_dest_vld;
    logic [KV_ENTRY_ADDR_W-1:0] write_entry;
    logic write_en;
} kv_write_ctrl_reg_t;

typedef enum logic [7:0] {
    KV_SUCCESS = 8'h00,
    KV_READ_FAIL = 8'h01,
    KV_WRITE_FAIL = 8'h02
} kv_error_code_e;

typedef struct packed {
    logic [KV_NUM_DWORDS-1:0][31:0] pcr_hash;
    logic [KV_NUM_DWORDS-1:0][31:0] pcr_signing_privkey;
} pcr_signing_t;

endpackage

`endif


