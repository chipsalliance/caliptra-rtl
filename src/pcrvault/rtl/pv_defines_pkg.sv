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
`ifndef PV_DEFINES_PKG
`define PV_DEFINES_PKG

package pv_defines_pkg;

parameter PV_NUM_DWORDS = 12; //number of dwords per pcr
parameter PV_NUM_PCR = 32;
parameter PV_ADDR_W = 13;
parameter PV_DATA_W = 32;
parameter PV_ENTRY_ADDR_W = $clog2(PV_NUM_PCR);
parameter PV_ENTRY_SIZE_WIDTH = $clog2(PV_NUM_DWORDS);
parameter PV_NUM_READ = 1;
parameter PV_NUM_WRITE = 1;
parameter PV_SIZE_OF_NONCE = 256;


typedef struct packed {
    logic   [PV_ADDR_W-1:0] addr;
    logic   [PV_DATA_W-1:0] wdata;
    logic                   write;
} pv_uc_req_t;

typedef struct packed {
    logic   [PV_ENTRY_ADDR_W-1:0]     read_entry;
    logic   [PV_ENTRY_SIZE_WIDTH-1:0] read_offset;
} pv_read_t;

typedef struct packed {
    logic                             write_en;
    logic   [PV_ENTRY_ADDR_W-1:0]     write_entry;
    logic   [PV_ENTRY_SIZE_WIDTH-1:0] write_offset;
    logic   [PV_DATA_W-1:0]           write_data;
} pv_write_t;

typedef struct packed {
    logic error;
} pv_wr_resp_t;

typedef struct packed {
    logic error;
    logic last;
    logic [PV_DATA_W-1:0] read_data;
} pv_rd_resp_t;

endpackage

`endif


