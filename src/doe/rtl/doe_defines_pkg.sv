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
  localparam DOE_ADDR_NAME0        = 32'h00000000;
  localparam DOE_ADDR_NAME1        = 32'h00000004;
  localparam DOE_ADDR_VERSION0     = 32'h00000008;
  localparam DOE_ADDR_VERSION1     = 32'h0000000c;

  localparam DOE_ADDR_CTRL        = 32'h00000010;
  localparam DOE_CTRL_INIT_BIT    = 0;
  localparam DOE_CTRL_NEXT_BIT    = 1;

  localparam DOE_ADDR_STATUS      = 32'h00000018;
  localparam DOE_STATUS_READY_BIT = 0;
  localparam DOE_STATUS_VALID_BIT = 1;

  localparam DOE_ADDR_CONFIG      = 32'h00000020;
  localparam DOE_CTRL_ENCDEC_BIT  = 0;
  localparam DOE_CTRL_KEYLEN_BIT  = 1;

  localparam DOE_ADDR_KEY_START   = 32'h00000040;
  localparam DOE_ADDR_KEY_END     = 32'h0000005c;

  localparam DOE_ADDR_BLOCK_START = 32'h00000080;
  localparam DOE_ADDR_BLOCK_END   = 32'h0000008c;

  localparam DOE_ADDR_RESULT_START= 32'h00000100;
  localparam DOE_ADDR_RESULT_END  = 32'h0000010c;

  localparam DOE_ADDR_IV_START = 32'h00000110;
  localparam DOE_ADDR_IV_END   = 32'h0000011c;

  localparam DOE_ADDR_KV_CTRL  = 32'h00000200;

  localparam DOE_ADDR_INTR_START = 32'h00000800; // span = 0x400; 0x800 base offset matches mailbox for fw ease
  localparam DOE_ADDR_INTR_END   = 32'h00000BFC;

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