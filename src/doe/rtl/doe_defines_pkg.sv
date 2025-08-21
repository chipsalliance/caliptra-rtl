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

`ifndef DOE_DEFINES_PKG
`define DOE_DEFINES_PKG

package doe_defines_pkg;
  import kv_defines_pkg::*;

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------

  localparam DOE_CORE_NAME        = 64'h20202020_73206165; // "doe "
  localparam DOE_CORE_VERSION     = 64'h00000000_3630302e; // "0.60"

typedef enum logic [3:0] {
    DOE_NOP     = 4'b0000,
    DOE_UDS     = 4'b0001,
    DOE_FE      = 4'b0010,
    DOE_CLEAR   = 4'b0011,
    DOE_HEK     = 4'b0100,
    DOE_INV0    = 4'b0101, // INVALID
    DOE_INV1    = 4'b0110, // INVALID
    DOE_INV2    = 4'b0111, // INVALID
    DOE_RSVD0   = 4'b1000, // RESERVED
    DOE_INV3    = 4'b1001, // INVALID
    DOE_INV4    = 4'b1010, // INVALID
    DOE_INV5    = 4'b1011, // INVALID
    DOE_RSVD1   = 4'b1100, // RESERVED
    DOE_INV6    = 4'b1101, // INVALID
    DOE_INV7    = 4'b1110, // INVALID
    DOE_INV8    = 4'b1111  // INVALID
} doe_cmd_e;

typedef struct packed {
    logic [KV_ENTRY_ADDR_W-1:0] dest_sel;
    doe_cmd_e cmd;
} doe_cmd_reg_t;

endpackage

`endif
