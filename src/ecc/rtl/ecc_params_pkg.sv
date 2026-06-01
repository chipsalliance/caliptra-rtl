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

  //----------------------------------------------------------------
  // Implementation parameters for field arithmetic.
  //
  // The engine supports two NIST prime curves selected at runtime:
  //   - secp384r1 (P-384) -- legacy default
  //   - secp256r1 (P-256) -- added via the dual-curve feature
  //
  // The internal datapath is sized for the widest curve (REG_SIZE = 384).
  // P-256 operands are zero-extended to 384b on the way in and produced /
  // truncated on the way out by the surrounding control logic.
  //----------------------------------------------------------------
  parameter [9 : 0] REG_SIZE     = 10'd384;
  parameter [9 : 0] RND_SIZE     = 10'd192;  // half of REG_SIZE based on Schindler W, Wiemers A (2015) Efficient side-channel attacks on
                                             // scalar blinding on elliptic curves with special structure. In: NIST Workshop on ECC standards
  parameter DATA_WIDTH           = 32;
  parameter REG_NUM_DWORDS       = REG_SIZE/DATA_WIDTH;
  parameter REG_OFFSET_W         = $clog2(REG_NUM_DWORDS);
  parameter MULT_RADIX           = 48;
  parameter SCALAR_BLIND_RADIX   = 32;
  parameter ADD_NUM_ADDS         = 1;
  parameter ADD_BASE_SZ          = 384;

  //----------------------------------------------------------------
  // Per-curve scalar / Montgomery loop bounds. Used by ecc_pm_ctrl.sv
  // and the per-curve sequencer ROMs to size the scalar-multiply loop.
  //----------------------------------------------------------------
  parameter [9 : 0] MONT_COUNT_P384     = 10'd384;
  parameter [9 : 0] MONT_COUNT_P256     = 10'd256;
  parameter [9 : 0] SCA_MONT_COUNT_P384 = MONT_COUNT_P384 + RND_SIZE; // 576
  parameter [9 : 0] SCA_MONT_COUNT_P256 = MONT_COUNT_P256 + RND_SIZE; // 448

  //================================================================
  // secp384r1 (P-384) constants -- Montgomery domain unless noted.
  //================================================================
  parameter [REG_SIZE-1 : 0] PRIME_P384       = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff;
  parameter [REG_SIZE-1 : 0] GROUP_ORDER_P384 = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973;

  parameter [REG_SIZE-1   : 0] E_a_MONT_P384   = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffcfffffffcfffeffffffff0002fffffffd0000ffffffff;
  parameter [REG_SIZE-1   : 0] E_b_MONT_P384   = 384'hbff9b62b21f41f022094e3374bee94938ae277f2209b1920022fc431bf24a7a3443768608870d0391c816cb9114b604f;
  parameter [REG_SIZE-1   : 0] E_3b_MONT_P384  = 384'h3fed228165dc5d0661bea9a5e3cbbdbaa0a767d661d14b60068f4c953d6df6ebcca63923995270ab5584462933e220ef;
  parameter [REG_SIZE-1   : 0] ONE_p_MONT_P384 = 384'h100000000ffffffffffffffff00000001000000000000;
  parameter [REG_SIZE-1   : 0] R2_p_MONT_P384  = 384'h10000000200000000fffffffe000000000000000200000000fffffffe00000001000000000000000000000000;
  parameter [REG_SIZE-1   : 0] G_X_MONT_P384   = 384'h1513812ff723614ede2b6454868459a30eff879c3afc541b4d6e6e1e26a517af7bfa676e7565fc860766239cadc2299e;
  parameter [REG_SIZE-1   : 0] G_Y_MONT_P384   = 384'hc5e9dd8002263969a840c6c3521968f4ffd98bade7562e83b050cd3854820142556e7d193dad1f8af93bd163abc25a15;
  parameter [MULT_RADIX-1 : 0] PRIME_mu_P384   = 48'h000100000001;          // -p^-1 mod 2^MULT_RADIX

  parameter [REG_SIZE-1   : 0] R2_q_MONT_P384      = 384'h28266895d40d49174aab1cc5bf030606de609f43cc9601f9ebbfed4b3ffe90bfead8c2590449c1c55daf7abd883e5e32;
  parameter [REG_SIZE-1   : 0] ONE_q_MONT_P384     = 384'h389cb27e0bc8d220a7e5f24db74f58851313e695333ad68d000000000000;
  parameter [MULT_RADIX-1 : 0] GROUP_ORDER_mu_P384 = 48'h6089e88fdc45;       // -q^-1 mod 2^MULT_RADIX

  //================================================================
  // secp256r1 (P-256) constants -- Montgomery domain unless noted.
  //
  // The engine's Montgomery multiplier uses MULT_RADIX=48 with
  // REG_SIZE=384, so its implicit Montgomery R is
  //     R = 2^((ceil(REG_SIZE/RADIX) + 1) * RADIX) = 2^(9*48) = 2^432
  // (see header of ecc_montgomerymultiplier.sv). All Mont-form P-256
  // values below are therefore computed with R = 2^432 -- the SAME R
  // used by the existing P-384 constants above.
  //
  // Affine values (PRIME, GROUP_ORDER, generator) are standard NIST.
  // Each Mont-form value reduces mod the 256-bit prime/order, so all
  // values fit in 256 bits and are zero-extended to REG_SIZE (384).
  //================================================================
  parameter [REG_SIZE-1 : 0] PRIME_P256       = { {(REG_SIZE-256){1'b0}}, 256'hFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF };
  parameter [REG_SIZE-1 : 0] GROUP_ORDER_P256 = { {(REG_SIZE-256){1'b0}}, 256'hFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551 };

  parameter [REG_SIZE-1   : 0] E_a_MONT_P256   = { {(REG_SIZE-256){1'b0}}, 256'h0002FFFFFFFCFFFFFFF9FFFFFFF9FFFFFFFD0000000300000003000000030000 };
  parameter [REG_SIZE-1   : 0] E_b_MONT_P256   = { {(REG_SIZE-256){1'b0}}, 256'hC75F93A5AABEE08154FFDB9CBCB91D5D68008B0F68E000934964C359E6515F1A };
  parameter [REG_SIZE-1   : 0] E_3b_MONT_P256  = { {(REG_SIZE-256){1'b0}}, 256'h561EBAF3003CA181FEFF92D6362B58183801A12C3AA001B9DC2E4A0DB2F41D50 };
  parameter [REG_SIZE-1   : 0] ONE_p_MONT_P256 = { {(REG_SIZE-256){1'b0}}, 256'hFFFEFFFF00010001000200000002000000010000FFFEFFFFFFFEFFFFFFFEFFFF };
  parameter [REG_SIZE-1   : 0] R2_p_MONT_P256  = { {(REG_SIZE-256){1'b0}}, 256'hFFFFFFE9FFFFFFE7FFFFFFDFFFFFFFE400000004000000180000001900000006 };
  parameter [REG_SIZE-1   : 0] G_X_MONT_P256   = { {(REG_SIZE-256){1'b0}}, 256'h23952AAF75C75B914B4A3FC326B18E72AF6D814DC8F1D8CD38C52F5505CF9DE5 };
  parameter [REG_SIZE-1   : 0] G_Y_MONT_P256   = { {(REG_SIZE-256){1'b0}}, 256'hBA1A3D06A74E0EA371FC5AD98482ED880D3230EFE40E2A987A95BD724F6BC781 };
  parameter [MULT_RADIX-1 : 0] PRIME_mu_P256   = 48'h000000000001;          // -p^-1 mod 2^48

  parameter [REG_SIZE-1   : 0] R2_q_MONT_P256      = { {(REG_SIZE-256){1'b0}}, 256'h40AF4D7B9CDACCBAED07D4A0E07EFA64BE50ADE0734BD61B980AC34490DD60A7 };
  parameter [REG_SIZE-1   : 0] ONE_q_MONT_P256     = { {(REG_SIZE-256){1'b0}}, 256'h6C21012F9164EDB00A9979318F1CE2B8D5C6F37D98098B0232FCEEF2777AA6C6 };
  parameter [MULT_RADIX-1 : 0] GROUP_ORDER_mu_P256 = 48'hC8AAEE00BC4F;       // -q^-1 mod 2^48

  //================================================================
  // Curve-defaulted (unsuffixed) aliases.
  //
  // Existing P-384-only code that has not yet been converted to mux
  // on CURVE_SEL continues to see the P-384 values via the unsuffixed
  // names.
  //================================================================
  parameter [REG_SIZE-1   : 0] ZERO_CONST     = {REG_SIZE{1'b0}};
  parameter [REG_SIZE-1   : 0] ONE_CONST      = {{(REG_SIZE-1){1'b0}}, 1'b1};

  parameter [REG_SIZE-1   : 0] PRIME          = PRIME_P384;
  parameter [REG_SIZE-1   : 0] GROUP_ORDER    = GROUP_ORDER_P384;
  parameter [REG_SIZE-1   : 0] E_a_MONT       = E_a_MONT_P384;
  parameter [REG_SIZE-1   : 0] E_b_MONT       = E_b_MONT_P384;
  parameter [REG_SIZE-1   : 0] E_3b_MONT      = E_3b_MONT_P384;
  parameter [REG_SIZE-1   : 0] ONE_p_MONT     = ONE_p_MONT_P384;
  parameter [REG_SIZE-1   : 0] R2_p_MONT      = R2_p_MONT_P384;
  parameter [REG_SIZE-1   : 0] G_X_MONT       = G_X_MONT_P384;
  parameter [REG_SIZE-1   : 0] G_Y_MONT       = G_Y_MONT_P384;
  parameter [MULT_RADIX-1 : 0] PRIME_mu       = PRIME_mu_P384;

  parameter [REG_SIZE-1   : 0] R2_q_MONT      = R2_q_MONT_P384;
  parameter [REG_SIZE-1   : 0] ONE_q_MONT     = ONE_q_MONT_P384;
  parameter [MULT_RADIX-1 : 0] GROUP_ORDER_mu = GROUP_ORDER_mu_P384;


endpackage

`endif
//======================================================================
// EOF ecc_params.sv
//======================================================================
