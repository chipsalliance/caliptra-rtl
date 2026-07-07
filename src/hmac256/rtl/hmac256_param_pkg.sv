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
// hmac256_param_pkg.sv
// --------
// HMAC256 Parameters
//
//
//======================================================================

`ifndef HMAC256_PARAM_PKG
`define HMAC256_PARAM_PKG

package hmac256_param_pkg;
  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------

  localparam bit [63:0] HMAC256_CORE_NAME    = 64'h36353263_6163686d; // "hmac256" (low half matches HMAC-512 family; high half is the variant tag)
  localparam bit [63:0] HMAC256_CORE_VERSION = 64'h00000000_3030302e; // "0.00"

  localparam bit HMAC224_MODE = 1'b0;
  localparam bit HMAC256_MODE = 1'b1;

  localparam int BLOCK_SIZE     = 512;
  localparam int KEY_SIZE       = 512;
  localparam int TAG_SIZE       = 256;
  localparam int LFSR_SEED_SIZE = 192;

  // SHA-224 variant widths (tag only) and zero-pad widths when packed
  // into the SHA-256-sized regs.
  localparam int HMAC224_TAG_SIZE = 224;
  localparam int HMAC224_TAG_PAD  = TAG_SIZE - HMAC224_TAG_SIZE;

  // HMAC inner/outer key pad bytes (RFC 2104).
  localparam bit [BLOCK_SIZE-1:0] IPAD = {(BLOCK_SIZE/8){8'h36}};
  localparam bit [BLOCK_SIZE-1:0] OPAD = {(BLOCK_SIZE/8){8'h5c}};

  // FIPS-180 padding for the HMAC finalization block:
  //   {0x80, zero-pad, 64-bit length}
  // Total length consumed up to this point is K_opad (BLOCK_SIZE) plus
  // the inner digest (TAG_SIZE for HMAC-256, HMAC224_TAG_SIZE for HMAC-224).
  // The padding fills the remainder of the BLOCK_SIZE-bit final block.
  localparam bit [BLOCK_SIZE-HMAC224_TAG_SIZE-1:0] HMAC224_FINAL_PAD =
      288'h8000000000000000000000000000000000000000000000000000000000000000000002E0;
  localparam bit [BLOCK_SIZE-TAG_SIZE-1:0]         HMAC256_FINAL_PAD =
      256'h8000000000000000000000000000000000000000000000000000000000000300;


  // The entropy block runs the SHA core over a fixed pattern to produce
  // a 192-bit pseudo-random refresh of the inner LFSRs. The pattern is
  // not interpreted as a hashed message by anything outside the core, so
  // the trailing space is plain zero-fill rather than valid FIPS-180
  // padding (a 448-bit "message" would not fit in one 512-bit SHA-256
  // block with valid padding).
  localparam int                                              ENTROPY_MSG_SIZE = (2 * LFSR_SEED_SIZE) + 64;
  localparam bit [BLOCK_SIZE-ENTROPY_MSG_SIZE-1:0]            ENTROPY_PAD      = '0;
endpackage

`endif
