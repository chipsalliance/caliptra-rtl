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
// ecc_pm_uop_pkg.sv
// --------
// ECC instructin for the point multiplication (PM).
//
//
//======================================================================


`ifndef ECC_PM_UOP_PKG
`define ECC_PM_UOP_PKG

package ecc_pm_uop_pkg;

localparam integer UOP_ADDR_WIDTH       = 6;
localparam integer OPR_ADDR_WIDTH       = 6;

localparam PROG_ADDR_W                  = 12; //$clog2(VER2_PA_E+2);
localparam INSTRUCTION_LENGTH           = UOP_ADDR_WIDTH + 2*OPR_ADDR_WIDTH;    // opcode + 2 * operand

localparam [UOP_ADDR_WIDTH-1 : 0] UOP_NOP                   = 6'b00_0000;

localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_MUL_p              = 6'b01_0000;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_ST_MUL_p              = 6'b00_0001;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_ADD_p              = 6'b00_1000;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_SUB_p              = 6'b00_1100;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_ST_ADD_p              = 6'b00_0010;

localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_MUL_q              = 6'b11_0000;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_ST_MUL_q              = 6'b10_0001;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_ADD_q              = 6'b10_1000;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_SUB_q              = 6'b10_1100;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_ST_ADD_q              = 6'b10_0010;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_DONTCARE          =  0;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ZERO        =  0;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ONE         =  1;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_E_a         =  2;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_E_3b        =  3;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ONE_MONT    =  4;  // Mont_mult(1, R2) % p
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_R2_p        =  5;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_GX_MONT     =  6;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_GY_MONT     =  7;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R0_X              =  8;  // 8'b0000_1000;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R0_Y              =  9;  // 8'b0000_1001;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R0_Z              = 10;  // 8'b0000_1010;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R1_X              = 12;  // 8'b0000_1100;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R1_Y              = 13;  // 8'b0000_1101;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R1_Z              = 14;  // 8'b0000_1110;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qx_AFFN           = 16;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qy_AFFN           = 17;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_SIGN_R            = 18;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_SIGN_S            = 19;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_PRIVKEY           = 20;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_HASH_MSG          = 21;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_SCALAR_G          = 22;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_SCALAR_PK         = 23;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_LAMBDA            = 24;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_MASKING           = 25;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ONE_q_MONT  = 28;  // Mont_mult(1, R2) % q
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_R2_q        = 29;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_A                 = 32;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_B                 = 33;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_C                 = 34;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_D                 = 35;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_E                 = 36;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_F                 = 37;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_G                 = 38;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_H                 = 39;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_J                 = 40;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_IN            = UOP_OPR_R0_Z;  // operand to be inverted
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE0          = 41;  // precomputed value based on UOP_OPR_Z_INV
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE1          = 42;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE2          = 43;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE3          = 44;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE4          = 45;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE5          = 46;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE6          = 47;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE7          = 48;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_A_INV             = 49;  // intermediate results during inversion
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_OUT           = 50;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qx_MONT           = 51;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qy_MONT           = 52;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_P1_X_MONT         = 53;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_P1_Y_MONT         = 54;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_P1_Z_MONT         = 55;

//PM command listing
localparam [2 : 0] KEYGEN_CMD           = 3'b001;
localparam [2 : 0] SIGN_CMD             = 3'b010;
localparam [2 : 0] VER_PART0_CMD        = 3'b100;    
localparam [2 : 0] VER_PART1_CMD        = 3'b101;    
localparam [2 : 0] VER_PART2_CMD        = 3'b110;    

//PM Subroutine listing
localparam [PROG_ADDR_W-1 : 0] NOP                  = 0;
localparam [PROG_ADDR_W-1 : 0] PM_INIT_G_S          = 2;               // R1 INIT with G
localparam [PROG_ADDR_W-1 : 0] PM_INIT_G_E          = PM_INIT_G_S + 5;
localparam [PROG_ADDR_W-1 : 0] PM_INIT_S            = PM_INIT_G_E + 2; // R0 INIT with O
localparam [PROG_ADDR_W-1 : 0] PM_INIT_E            = PM_INIT_S + 9;
localparam [PROG_ADDR_W-1 : 0] PA_S                 = PM_INIT_E + 2;   // Point Addition
localparam [PROG_ADDR_W-1 : 0] PA_E                 = PA_S + 79;
localparam [PROG_ADDR_W-1 : 0] PD_S                 = PA_E + 2;        // Point Doubling
localparam [PROG_ADDR_W-1 : 0] PD_E                 = PD_S + 83;
localparam [PROG_ADDR_W-1 : 0] INV_S                = PD_E + 2;        // Inversion mod p
localparam [PROG_ADDR_W-1 : 0] INV_E                = INV_S + 1039;
localparam [PROG_ADDR_W-1 : 0] CONV_S               = INV_E + 2;       // PM result conversion from projective Mont (X,Y,Z) to affine normanl (x,y)
localparam [PROG_ADDR_W-1 : 0] CONV_E               = CONV_S + 11;

localparam [PROG_ADDR_W-1 : 0] SIGN0_S              = CONV_E + 2;     // signing proof r part0
localparam [PROG_ADDR_W-1 : 0] SIGN0_E              = SIGN0_S + 27;
localparam [PROG_ADDR_W-1 : 0] INVq_S               = SIGN0_E + 2;    // Inversion mod q
localparam [PROG_ADDR_W-1 : 0] INVq_E               = INVq_S + 1043;
localparam [PROG_ADDR_W-1 : 0] SIGN1_S              = INVq_E + 2;     // signing proof r part1
localparam [PROG_ADDR_W-1 : 0] SIGN1_E              = SIGN1_S + 11;

localparam [PROG_ADDR_W-1 : 0] VER0_P0_S            = SIGN1_E + 2;    // verifying0 part0 to convert inputs to Mont domain
localparam [PROG_ADDR_W-1 : 0] VER0_P0_E            = VER0_P0_S + 9;
localparam [PROG_ADDR_W-1 : 0] VER0_P1_S            = VER0_P0_E + 2;  // verifying0 part1 to compute (h*s_inv) and (r*s_inv)
localparam [PROG_ADDR_W-1 : 0] VER0_P1_E            = VER0_P1_S + 11;
localparam [PROG_ADDR_W-1 : 0] VER1_ST_S            = VER0_P1_E + 2;  // verifying1 store ver1 result (h*s_inv)*G
localparam [PROG_ADDR_W-1 : 0] VER1_ST_E            = VER1_ST_S + 5;
localparam [PROG_ADDR_W-1 : 0] PM_INIT_PK_S         = VER1_ST_E + 2;  // verifying2 R1 INIT with PK
localparam [PROG_ADDR_W-1 : 0] PM_INIT_PK_E         = PM_INIT_PK_S + 5;
localparam [PROG_ADDR_W-1 : 0] VER2_PA_S            = PM_INIT_PK_E + 2;  // verifying2 point addtion of PA((h*s_inv)*G, (r*s_inv)*PK)
localparam [PROG_ADDR_W-1 : 0] VER2_PA_E            = VER2_PA_S + 81;

`endif

endpackage