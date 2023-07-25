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
`ifndef DV_DEFINES_PKG
`define DV_DEFINES_PKG

package dv_defines_pkg;

    parameter DV_ADDR_W = 13;
    parameter DV_DATA_W = 32;

    parameter STICKY_DV_NUM_ENTRIES = 10;
    parameter DV_NUM_ENTRIES = 10;
    parameter LOCK_SCRATCH_NUM_ENTRIES = 10;
    parameter STICKY_LOCK_SCRATCH_NUM_ENTRIES = 8;
    parameter NONSTICKY_SCRATCH_NUM_ENTRIES = 8;
    parameter DV_NUM_DWORDS = 12;

typedef struct packed {
    logic   [DV_ADDR_W-1:0] addr;
    logic   [DV_DATA_W-1:0] wdata;
    logic                   write;
} dv_uc_req_t;

endpackage

`endif


