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

typedef enum logic [1:0] {
    DOE_NOP    = 2'b00,
    DOE_UDS    = 2'b01,
    DOE_FE     = 2'b10,
    DOE_CLEAR  = 2'b11
} doe_cmd_e;

typedef struct packed {
    logic [KV_ENTRY_ADDR_W-1:0] dest_sel;
    doe_cmd_e cmd;
} doe_cmd_reg_t;

endpackage

`endif