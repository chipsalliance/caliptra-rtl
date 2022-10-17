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
// required parameters and register address for ECC Secp384.
//
//======================================================================

`ifndef ECC_PARAMS_PKG
`define ECC_PARAMS_PKG

package ecc_params_pkg;

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter ECC_BASE_ADDR        = 32'h00000000;

  parameter ECC_ADDR_NAME        = ECC_BASE_ADDR + 32'h00000000;
  parameter ECC_ADDR_VERSION     = ECC_BASE_ADDR + 32'h00000008;

  parameter ECC_ADDR_CTRL        = ECC_BASE_ADDR + 32'h00000010;
  parameter KEYGEN               = 2'b01;
  parameter SIGN                 = 2'b10;
  parameter VERIFY               = 2'b11;

  parameter ECC_ADDR_STATUS      = ECC_BASE_ADDR + 32'h00000018;

  parameter ECC_ADDR_VERIFY      = ECC_BASE_ADDR + 32'h00000020;

  parameter ECC_ADDR_SEED0       = ECC_BASE_ADDR + 32'h00000080;
  parameter ECC_ADDR_SEED11      = ECC_BASE_ADDR + 32'h000000AC;

  parameter ECC_ADDR_MSG0        = ECC_BASE_ADDR + 32'h00000100;
  parameter ECC_ADDR_MSG11       = ECC_BASE_ADDR + 32'h0000012C;

  parameter ECC_ADDR_PRIVKEY0    = ECC_BASE_ADDR + 32'h00000180;
  parameter ECC_ADDR_PRIVKEY11   = ECC_BASE_ADDR + 32'h000001AC;

  parameter ECC_ADDR_PUBKEYX0    = ECC_BASE_ADDR + 32'h00000200;
  parameter ECC_ADDR_PUBKEYX11   = ECC_BASE_ADDR + 32'h0000022C;

  parameter ECC_ADDR_PUBKEYY0    = ECC_BASE_ADDR + 32'h00000280;
  parameter AECC_DDR_PUBKEYY11   = ECC_BASE_ADDR + 32'h000002AC;

  parameter ECC_ADDR_SIGNR0      = ECC_BASE_ADDR + 32'h00000300;
  parameter ECC_ADDR_SIGNR11     = ECC_BASE_ADDR + 32'h0000032C;

  parameter ECC_ADDR_SIGNS0      = ECC_BASE_ADDR + 32'h00000380;
  parameter ECC_ADDR_SIGNS11     = ECC_BASE_ADDR + 32'h000003AC;

  parameter ECC_ADDR_VERIFYR0    = ECC_BASE_ADDR + 32'h00000400;
  parameter ECC_ADDR_VERIFYR11   = ECC_BASE_ADDR + 32'h0000042C;

  parameter ECC_ADDR_IV0         = ECC_BASE_ADDR + 32'h00000480;
  parameter ECC_ADDR_IV11        = ECC_BASE_ADDR + 32'h000004AC;

  parameter [63  : 0] ECC_CORE_NAME        = 64'h38342D33_63707365; // "secp-384"
  parameter [63  : 0] ECC_CORE_VERSION     = 64'h00000000_3030312e; // "1.00"

  // Implementation parameters for field arithmetic
  parameter REG_SIZE             = 384;
  parameter RADIX                = 32;
  parameter ADD_NUM_ADDS         = 1;
  parameter ADD_BASE_SZ          = 384;

  // prime parameters in Montgomery domain
  parameter [REG_SIZE-1 : 0] PRIME       = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff;
  parameter [REG_SIZE-1 : 0] GROUP_ORDER = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973;

  // prime parameters in Montgomery domain
  parameter [REG_SIZE-1 : 0] E_a_MONT    = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffcfffffffbffffffff00000002fffffffdffffffff;
  parameter [REG_SIZE-1 : 0] E_3b_MONT   = 384'h20ef3fed228165dc5d0661bea9a5e3cbbdbaa0a767d661d14b60068f4c953d6dd5fccca61834995270ab5584671833e2;
  parameter [REG_SIZE-1 : 0] ONE_p_MONT  = 384'h100000000ffffffffffffffff0000000100000000;
  parameter [REG_SIZE-1 : 0] R2_p_MONT   = 384'h10000000200000000fffffffe000000000000000200000000fffffffe000000010000000000000000;
  parameter [REG_SIZE-1 : 0] G_X_MONT    = 384'h299e1513812ff723614ede2b6454868459a30eff879c3afc541b4d6e6e1e26a4ee117bfa3dd07565fc8607664d3aadc2;
  parameter [REG_SIZE-1 : 0] G_Y_MONT    = 384'h5a15c5e9dd8002263969a840c6c3521968f4ffd98bade7562e83b050cd385481a72d556e23043dad1f8af93c2b78abc2;
  parameter [RADIX-1 : 0]    PRIME_mu    = 32'h00000001;

  // group order parameters in Montgomery domain
  parameter [REG_SIZE-1 : 0] R2_q_MONT   = 384'h3fb05b7a28266895d40d49174aab1cc5bf030606de609f43be80721782118942bfd3ccc974971bd0d8d34124f50ddb2d;
  parameter [REG_SIZE-1 : 0] ONE_q_MONT  = 384'h389cb27e0bc8d220a7e5f24db74f58851313e695333ad68d00000000;
  parameter [RADIX-1 : 0] GROUP_ORDER_mu = 32'he88fdc45;
  
  // Side-channel countermeasures configuration

  // Randomized Projective Coordinates countermeasure based on section 5.3 
  // "Resistance against Differential Power Analysis for Elliptic Curve 
  // Cryptosystems" in CHES 1999 by Coron, J.  
  // This countermesure uses a random value "lambda" in point multiplication
  // (Q = k * P) in keygen/signing to randomiza base point P = (X, Y, 1)
  // as follows:
  // P = (X * Lambda, Y * lambda, Lambda)
  parameter                   sca_point_rnd_init     = 1;

  // Scalar blinding countermeasure based on section 5.1 
  // "Resistance against Differential Power Analysis for Elliptic Curve 
  // Cryptosystems" in CHES 1999 by Coron, J.  
  // This countermeasure uses a random value "r" in the point multiplication
  // (Q = k * P) in keygen/signing to randomiza scalar k as follows:
  // k = k + r*group_order
  parameter                   sca_scalar_rnd_init    = 1;
  parameter [7  : 0]          RND_SIZE               = 192;
  

  // Masking sign countermeasure uses a random value "d" in the signing 
  // operation to generate signature proof s = (privkey * r + h)*k_inv 
  // as follows:
  // s = [((privkey - d) * r + (h - d)) * k_inv] + [(d * r + d) * k_inv]
  parameter                   sca_mask_sign_init     = 1;

  // openssl keygen test should be deleted after openssl keygen test.
  parameter                   openssl_init           = 0;

  `endif

endpackage
//======================================================================
// EOF ecc_params.sv
//======================================================================
