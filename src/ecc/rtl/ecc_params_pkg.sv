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
  parameter KEYGEN               = 3'b001;
  parameter SIGN                 = 3'b010;
  parameter VERIFY               = 3'b011;
  parameter SHARED_KEY           = 3'b100;

  parameter [63  : 0] ECC_CORE_NAME        = 64'h38342D33_63707365; // "secp-384"
  parameter [63  : 0] ECC_CORE_VERSION     = 64'h00000000_3030312e; // "1.00"

  // Implementation parameters for field arithmetic
  parameter [9 : 0] REG_SIZE     = 10'd384;
  parameter [9 : 0] RND_SIZE     = 10'd192;  // half of REG_SIZE based on Schindler W, Wiemers A (2015) Efficient side-channel attacks on
                                             // scalar blinding on elliptic curves with special structure. In: NIST Workshop on ECC standards
  parameter DATA_WIDTH           = 32;
  parameter REG_NUM_DWORDS       = REG_SIZE/DATA_WIDTH;
  parameter REG_OFFSET_W         = $clog2(REG_NUM_DWORDS);
  // Select 48 or 64, then rebuild. Geometry and Montgomery constants follow.
  parameter MULT_RADIX           = 64;
  parameter SCALAR_BLIND_RADIX   = 32;
  parameter ADD_NUM_ADDS         = 1;
  parameter ADD_BASE_SZ          = 384;

  // prime parameters in Montgomery domain
  parameter [REG_SIZE-1 : 0] PRIME       = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff;
  parameter [REG_SIZE-1 : 0] GROUP_ORDER = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973;

  // R = 2^((ceil(REG_SIZE / MULT_RADIX) + 1) * MULT_RADIX).
  // For P-384, radix 48 uses R=2^432 and radix 64 uses R=2^448.
  parameter [REG_SIZE-1   : 0] ZERO_CONST  = 384'h0;
  parameter [REG_SIZE-1   : 0] ONE_CONST   = 384'h1;
  parameter [REG_SIZE-1   : 0] E_a_MONT    = (MULT_RADIX == 48) ?
    384'hfffffffffffffffffffffffffffffffffffffffffffffffffffcfffffffcfffeffffffff0002fffffffd0000ffffffff :
    384'hfffffffffffffffffffffffffffffffffffffffffffffffcfffffffcffffffff00000001fffffffd00000000ffffffff;
  parameter [REG_SIZE-1   : 0] E_b_MONT    = (MULT_RADIX == 48) ?
    384'hbff9b62b21f41f022094e3374bee94938ae277f2209b1920022fc431bf24a7a3443768608870d0391c816cb9114b604f :
    384'hb62b21f41f022094e3374bee94938ae277f2209b1920022fc431bf24a7a4043068614869d0391c816cb85152604fbff9;
  parameter [REG_SIZE-1   : 0] E_3b_MONT   = (MULT_RADIX == 48) ?
    384'h3fed228165dc5d0661bea9a5e3cbbdbaa0a767d661d14b60068f4c953d6df6ebcca63923995270ab5584462933e220ef :
    384'h228165dc5d0661bea9a5e3cbbdbaa0a767d661d14b60068f4c953d6df6ec0c933923d93f70ab55844628f3f520ef3fed;
  parameter [REG_SIZE-1   : 0] ONE_p_MONT  = (MULT_RADIX == 48) ?
    384'h100000000ffffffffffffffff00000001000000000000 :
    384'h00000000000000000000000000000000000000000000000100000000ffffffffffffffff000000010000000000000000;
  parameter [REG_SIZE-1   : 0] R2_p_MONT   = (MULT_RADIX == 48) ?
    384'h10000000200000000fffffffe000000000000000200000000fffffffe00000001000000000000000000000000 :
    384'h0000000200000000fffffffe000000000000000200000000fffffffe0000000200000000ffffffffffffffff00000001;
  parameter [REG_SIZE-1   : 0] G_X_MONT    = (MULT_RADIX == 48) ?
    384'h1513812ff723614ede2b6454868459a30eff879c3afc541b4d6e6e1e26a517af7bfa676e7565fc860766239cadc2299e :
    384'h812ff723614ede2b6454868459a30eff879c3afc541b4d6e6e1e26a517af910d676e8a78fc860766239c98af299e1513;
  parameter [REG_SIZE-1   : 0] G_Y_MONT    = (MULT_RADIX == 48) ?
    384'hc5e9dd8002263969a840c6c3521968f4ffd98bade7562e83b050cd3854820142556e7d193dad1f8af93bd163abc25a15 :
    384'hdd8002263969a840c6c3521968f4ffd98bade7562e83b050cd38548201431b577d1a03961f8af93bd162e5d95a15c5e9;
  // Width truncation selects the inverse modulo 2^MULT_RADIX.
  parameter [MULT_RADIX-1 : 0] PRIME_mu    = 64'h0000000100000001;

  // group order parameters in Montgomery domain
  parameter [REG_SIZE-1   : 0] R2_q_MONT      = (MULT_RADIX == 48) ?
    384'h28266895d40d49174aab1cc5bf030606de609f43cc9601f9ebbfed4b3ffe90bfead8c2590449c1c55daf7abd883e5e32 :
    384'hd40d49174aab1cc5bf030606de609f43cc9601f9f4a0e7920c42c98aa72d2d8e43bcf715399000ed42a6fc1a99562811;
  parameter [REG_SIZE-1   : 0] ONE_q_MONT     = (MULT_RADIX == 48) ?
    384'h389cb27e0bc8d220a7e5f24db74f58851313e695333ad68d000000000000 :
    384'h00000000000000000000000000000000389cb27e0bc8d220a7e5f24db74f58851313e695333ad68d0000000000000000;
  parameter [MULT_RADIX-1 : 0] GROUP_ORDER_mu = 64'h6ed46089e88fdc45;

endpackage

`endif
//======================================================================
// EOF ecc_params.sv
//======================================================================
