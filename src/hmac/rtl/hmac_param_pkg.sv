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
// HMAC Parameters
//
//
//======================================================================

`ifndef HMAC_PARAM_PKG
`define HMAC_PARAM_PKG

package hmac_param_pkg;
  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------

  localparam bit [63:0] HMAC_CORE_NAME        = 64'h61327368_6163686d; // "hmacsha2"
  localparam bit [63:0] HMAC_CORE_VERSION     = 64'h00000000_3030322e; // "2.00"

  localparam bit HMAC384_MODE = 1'b0;
  localparam bit HMAC512_MODE = 1'b1;
endpackage

`endif