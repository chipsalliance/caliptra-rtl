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
//======================================================================
//
// hmac_param_pkg.sv
// --------
// HMAC384 Parameters
//
//
//======================================================================

`ifndef HMAC_PARAM_PKG
`define HMAC_PARAM_PKG

package hmac_param_pkg;
  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam HMAC_ADDR_NAME0       = 32'h00000000;
  localparam HMAC_ADDR_NAME1       = 32'h00000004;
  localparam HMAC_ADDR_VERSION0    = 32'h00000008;
  localparam HMAC_ADDR_VERSION1    = 32'h0000000C;

  localparam HMAC_ADDR_CTRL        = 32'h00000010;
  localparam HMAC_CTRL_INIT_BIT    = 0;
  localparam HMAC_CTRL_NEXT_BIT    = 1;

  localparam HMAC_ADDR_STATUS      = 32'h00000018;

  localparam HMAC_ADDR_KEY0        = 32'h00000040;
  localparam HMAC_ADDR_KEY11       = 32'h0000006C;

  localparam HMAC_ADDR_BLOCK0      = 32'h00000080;
  localparam HMAC_ADDR_BLOCK31     = 32'h000000fC;

  localparam HMAC_ADDR_TAG0        = 32'h00000100;
  localparam HMAC_ADDR_TAG11       = 32'h0000012C;

  localparam HMAC_KV_CTRL          = 32'h00000200;

  localparam bit [63:0] HMAC_CORE_NAME        = 64'h61327368_6163686d; // "hmacsha2"
  localparam bit [63:0] HMAC_CORE_VERSION     = 64'h00000000_3030312e; // "1.00"

`endif

endpackage