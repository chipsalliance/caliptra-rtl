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
//======================================================================
//
// ecc_defines_pkg.sv
// --------
// ECC interface parameters for the digital signature algorithm (DSA).
//
//
//======================================================================

`ifndef CALIPTRA_ECC_DEFINES
`define CALIPTRA_ECC_DEFINES

package ecc_defines_pkg;

localparam ECC_ADDR_W = 32;
localparam ECC_DATA_W = 32;

//ECC REQ
typedef struct packed {
    logic   [ECC_ADDR_W-1:0] addr;
    logic   [ECC_DATA_W-1:0] wdata;
    logic                    write;
} ecc_req_t;

endpackage

`endif
