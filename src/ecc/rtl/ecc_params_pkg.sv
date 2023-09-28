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
// ecc_params_pkg.sv
// --------
// required parameters and register address for ECC Secp384r1.
//
//======================================================================

`ifndef CALIPTRA_ECC_PARAMS_PKG
`define CALIPTRA_ECC_PARAMS_PKG

package ecc_params_pkg;

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter KEYGEN               = 2'b01;
  parameter SIGN                 = 2'b10;
  parameter VERIFY               = 2'b11;

  parameter [63  : 0] ECC_CORE_NAME        = 64'h38342D33_63707365; // "secp-384"
  parameter [63  : 0] ECC_CORE_VERSION     = 64'h00000000_3030312e; // "1.00"

  // Implementation parameters for field arithmetic
  parameter [9 : 0] REG_SIZE     = 10'd384;
  parameter [9 : 0] RND_SIZE     = 10'd192;  // half of REG_SIZE based on Schindler W, Wiemers A (2015) Efficient side-channel attacks on
                                             // scalar blinding on elliptic curves with special structure. In: NIST Workshop on ECC standards
  parameter REG_NUM_DWORDS       = REG_SIZE/32;
  parameter REG_OFFSET_W         = $clog2(REG_NUM_DWORDS);
  parameter RADIX                = 32;
  parameter ADD_NUM_ADDS         = 1;
  parameter ADD_BASE_SZ          = 384;

  // prime parameters in Montgomery domain
  parameter [REG_SIZE-1 : 0] PRIME       = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff;
  parameter [REG_SIZE-1 : 0] GROUP_ORDER = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973;

  // prime parameters in Montgomery domain
  parameter [REG_SIZE-1 : 0] ZERO_CONST  = 384'h0;
  parameter [REG_SIZE-1 : 0] ONE_CONST   = 384'h1;
  parameter [REG_SIZE-1 : 0] E_a_MONT    = 384'hfffffffffffffffffffffffffffffffffffffffffffffffcfffffffcffffffff00000001fffffffd00000000ffffffff;
  parameter [REG_SIZE-1 : 0] E_b_MONT    = 384'hb62b21f41f022094e3374bee94938ae277f2209b1920022fc431bf24a7a4043068614869d0391c816cb85152604fbff9;
  parameter [REG_SIZE-1 : 0] E_3b_MONT   = 384'h228165dc5d0661bea9a5e3cbbdbaa0a767d661d14b60068f4c953d6df6ec0c933923d93f70ab55844628f3f520ef3fed;
  parameter [REG_SIZE-1 : 0] ONE_p_MONT  = 384'h100000000ffffffffffffffff000000010000000000000000;
  parameter [REG_SIZE-1 : 0] R2_p_MONT   = 384'h200000000fffffffe000000000000000200000000fffffffe0000000200000000ffffffffffffffff00000001;
  parameter [REG_SIZE-1 : 0] G_X_MONT    = 384'h812ff723614ede2b6454868459a30eff879c3afc541b4d6e6e1e26a517af910d676e8a78fc860766239c98af299e1513;
  parameter [REG_SIZE-1 : 0] G_Y_MONT    = 384'hdd8002263969a840c6c3521968f4ffd98bade7562e83b050cd38548201431b577d1a03961f8af93bd162e5d95a15c5e9;
  parameter [RADIX-1 : 0]    PRIME_mu    = 64'h100000001;

  // group order parameters in Montgomery domain
  parameter [REG_SIZE-1 : 0] R2_q_MONT   = 384'hd40d49174aab1cc5bf030606de609f43cc9601f9f4a0e7920c42c98aa72d2d8e43bcf715399000ed42a6fc1a99562811;
  parameter [REG_SIZE-1 : 0] ONE_q_MONT  = 384'h389cb27e0bc8d220a7e5f24db74f58851313e695333ad68d0000000000000000;
  parameter [RADIX-1 : 0] GROUP_ORDER_mu = 64'h6ed46089e88fdc45;

endpackage

`endif
//======================================================================
// EOF ecc_params.sv
//======================================================================
