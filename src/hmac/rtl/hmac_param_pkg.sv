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

  localparam int BLOCK_SIZE     = 1024;
  localparam int KEY_SIZE       = 512;
  localparam int TAG_SIZE       = 512;
  localparam int LFSR_SEED_SIZE = 192;

  // SHA-384 variant widths (key/tag) and zero-pad width when packed
  // into the SHA-512-sized regs.
  localparam int HMAC384_KEY_SIZE    = 384;
  localparam int HMAC384_TAG_SIZE    = 384;
  localparam int HMAC384_KEY_PAD     = KEY_SIZE - HMAC384_KEY_SIZE;
  localparam int HMAC384_TAG_PAD     = TAG_SIZE - HMAC384_TAG_SIZE;

  // HMAC inner/outer key pad bytes (RFC 2104).
  localparam bit [BLOCK_SIZE-1:0] IPAD = {(BLOCK_SIZE/8){8'h36}};
  localparam bit [BLOCK_SIZE-1:0] OPAD = {(BLOCK_SIZE/8){8'h5c}};

  localparam bit [BLOCK_SIZE-HMAC384_TAG_SIZE-1:0] HMAC384_FINAL_PAD =
      640'h8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000580;
  localparam bit [BLOCK_SIZE-TAG_SIZE-1:0]         HMAC512_FINAL_PAD =
      512'h80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000600;

  
  localparam int                                              ENTROPY_MSG_SIZE = (2 * LFSR_SEED_SIZE) + 64;
  localparam bit [BLOCK_SIZE-ENTROPY_MSG_SIZE-1:0]            ENTROPY_PAD      =
      576'h8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001C0;
endpackage

`endif