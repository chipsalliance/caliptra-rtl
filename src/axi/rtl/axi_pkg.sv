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

package axi_pkg;

    // AXI Burst Enum
    typedef enum logic [1:0] {
        AXI_BURST_FIXED    = 2'b00,
        AXI_BURST_INCR     = 2'b01,
        AXI_BURST_WRAP     = 2'b10,
        AXI_BURST_RESERVED = 2'b11
    } axi_burst_e;

    // AXI Resp Enum
    typedef enum logic [1:0] {
        AXI_RESP_OKAY   = 2'b00,
        AXI_RESP_EXOKAY = 2'b01,
        AXI_RESP_SLVERR = 2'b10,
        AXI_RESP_DECERR = 2'b11
    } axi_resp_e;

    // Transaction context
    typedef struct packed {
        logic [AW-1:0] addr;
        logic [1:0]    burst;
        logic [2:0]    size;
        logic [7:0]    len;
        logic [UW-1:0] user;
        logic [IW-1:0] id;
        logic          lock;
    } axi_ctx_t;

    typedef struct packed {
        logic [IW-1:0] id;
        logic [UW-1:0] user;
        axi_resp_e     resp;
        logic          last;
    } xfer_ctx_t;

    typedef struct packed {
        logic [AW-1:0] addr;
        logic [AW-1:0] addr_mask;
    } axi_ex_ctx_t;

endpackage
