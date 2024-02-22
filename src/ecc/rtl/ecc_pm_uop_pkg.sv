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


`ifndef CALIPTRA_ECC_PM_UOP_PKG
`define CALIPTRA_ECC_PM_UOP_PKG

package ecc_pm_uop_pkg;

localparam integer UOP_ADDR_WIDTH       = 6;
localparam integer OPR_ADDR_WIDTH       = 6;

localparam PROG_ADDR_W                  = 12; //$clog2(VER2_PA_E+2);
localparam INSTRUCTION_LENGTH           = UOP_ADDR_WIDTH + (2*OPR_ADDR_WIDTH);    // opcode + 2 * operand

typedef struct packed
{
    logic       mult_we;
    logic       add_we;
    logic       sub_sel;
    logic       add_en;
    logic       mult_en;
    logic       mod_q_sel;
} pm_opcode_t;

typedef struct packed
{
    pm_opcode_t                     opcode;
    logic [OPR_ADDR_WIDTH-1 : 0]    opa_addr;
    logic [OPR_ADDR_WIDTH-1 : 0]    opb_addr;
} pm_instr_struct_t;

localparam pm_opcode_t UOP_NOP      = '{mult_we:1'b0, add_we:1'b0, sub_sel:1'b0, add_en:1'b0, mult_en:1'b0, mod_q_sel:1'b0}; // = 6'b00_0000;
localparam pm_opcode_t UOP_DO_MUL_p = '{mult_we:1'b0, add_we:1'b0, sub_sel:1'b0, add_en:1'b0, mult_en:1'b1, mod_q_sel:1'b0}; // = 6'b01_0000;
localparam pm_opcode_t UOP_ST_MUL_p = '{mult_we:1'b1, add_we:1'b0, sub_sel:1'b0, add_en:1'b0, mult_en:1'b0, mod_q_sel:1'b0}; // = 6'b00_0001;
localparam pm_opcode_t UOP_DO_ADD_p = '{mult_we:1'b0, add_we:1'b0, sub_sel:1'b0, add_en:1'b1, mult_en:1'b0, mod_q_sel:1'b0}; // = 6'b00_1000;
localparam pm_opcode_t UOP_DO_SUB_p = '{mult_we:1'b0, add_we:1'b0, sub_sel:1'b1, add_en:1'b1, mult_en:1'b0, mod_q_sel:1'b0}; // = 6'b00_1100;
localparam pm_opcode_t UOP_ST_ADD_p = '{mult_we:1'b0, add_we:1'b1, sub_sel:1'b0, add_en:1'b0, mult_en:1'b0, mod_q_sel:1'b0}; // = 6'b00_0010;

localparam pm_opcode_t UOP_DO_MUL_q = '{mult_we:1'b0, add_we:1'b0, sub_sel:1'b0, add_en:1'b0, mult_en:1'b1, mod_q_sel:1'b1}; // = 6'b11_0000;
localparam pm_opcode_t UOP_ST_MUL_q = '{mult_we:1'b1, add_we:1'b0, sub_sel:1'b0, add_en:1'b0, mult_en:1'b0, mod_q_sel:1'b1}; // = 6'b10_0001;
localparam pm_opcode_t UOP_DO_ADD_q = '{mult_we:1'b0, add_we:1'b0, sub_sel:1'b0, add_en:1'b1, mult_en:1'b0, mod_q_sel:1'b1}; // = 6'b10_1000;
localparam pm_opcode_t UOP_DO_SUB_q = '{mult_we:1'b0, add_we:1'b0, sub_sel:1'b1, add_en:1'b1, mult_en:1'b0, mod_q_sel:1'b1}; // = 6'b10_1100;
localparam pm_opcode_t UOP_ST_ADD_q = '{mult_we:1'b0, add_we:1'b1, sub_sel:1'b0, add_en:1'b0, mult_en:1'b0, mod_q_sel:1'b1}; // = 6'b10_0010;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_DONTCARE          = 6'd0;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ZERO        = 6'd0;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ONE         = 6'd1;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_E_a         = 6'd2;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_E_3b        = 6'd3;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ONE_MONT    = 6'd4;  // Mont_mult(1, R2) % p
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_R2_p        = 6'd5;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_GX_MONT     = 6'd6;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_GY_MONT     = 6'd7;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R0_X              = 6'd8;   // 8'b0000_1000;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R0_Y              = 6'd9;   // 8'b0000_1001;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R0_Z              = 6'd10;  // 8'b0000_1010;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R1_X              = 6'd12;  // 8'b0000_1100;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R1_Y              = 6'd13;  // 8'b0000_1101;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R1_Z              = 6'd14;  // 8'b0000_1110;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qx_AFFN           = 6'd16;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qy_AFFN           = 6'd17;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_SIGN_R            = 6'd18;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_SIGN_S            = 6'd19;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_PRIVKEY           = 6'd20;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_HASH_MSG          = 6'd21;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_SCALAR_G          = 6'd22;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_SCALAR_PK         = 6'd23;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_LAMBDA            = 6'd24;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_MASKING           = 6'd25;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ONE_q_MONT  = 6'd28;  // Mont_mult(1, R2) % q
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_R2_q        = 6'd29;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_A                 = 6'd32;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_B                 = 6'd33;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_C                 = 6'd34;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_D                 = 6'd35;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_E                 = 6'd36;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_F                 = 6'd37;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_G                 = 6'd38;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_H                 = 6'd39;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_J                 = 6'd40;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_IN            = UOP_OPR_R0_Z;  // operand to be inverted
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE0          = 6'd41;  // precomputed value based on UOP_OPR_Z_INV
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE1          = 6'd42;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE2          = 6'd43;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE3          = 6'd44;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE4          = 6'd45;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE5          = 6'd46;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE6          = 6'd47;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE7          = 6'd48;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_A_INV             = 6'd49;  // intermediate results during inversion
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_OUT           = 6'd50;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qx_MONT           = 6'd51;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qy_MONT           = 6'd52;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_P1_X_MONT         = 6'd53;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_P1_Y_MONT         = 6'd54;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_P1_Z_MONT         = 6'd55;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_E_b         = 6'd56;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_PK_VALID          = 6'd57;

//PM command listing
localparam [3 : 0] KEYGEN_CMD           = 4'b0001;
localparam [3 : 0] SIGN_CMD             = 4'b0010;
localparam [3 : 0] VER_PART0_CMD        = 4'b0100;    
localparam [3 : 0] VER_PART1_CMD        = 4'b0101;    
localparam [3 : 0] VER_PART2_CMD        = 4'b0110;
localparam [3 : 0] CHK_PK_CMD           = 4'b0111;
localparam [3 : 0] DH_SHARED_CMD        = 4'b1000;

//PM Subroutine listing
localparam [PROG_ADDR_W-1 : 0] NOP                  = 12'd0;
localparam [PROG_ADDR_W-1 : 0] PM_INIT_G_S          = 12'd2;               // R1 INIT with G
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

localparam [PROG_ADDR_W-1 : 0] CHK_PK_S             = SIGN1_E + 2;    // check the given public key is a valid curve point
localparam [PROG_ADDR_W-1 : 0] CHK_PK_E             = CHK_PK_S + 21;
localparam [PROG_ADDR_W-1 : 0] VER0_P0_S            = CHK_PK_E + 2;   // verifying0 part0 to convert inputs to Mont domain
localparam [PROG_ADDR_W-1 : 0] VER0_P0_E            = VER0_P0_S + 9;
localparam [PROG_ADDR_W-1 : 0] VER0_P1_S            = VER0_P0_E + 2;  // verifying0 part1 to compute (h*s_inv) and (r*s_inv)
localparam [PROG_ADDR_W-1 : 0] VER0_P1_E            = VER0_P1_S + 11;
localparam [PROG_ADDR_W-1 : 0] VER1_ST_S            = VER0_P1_E + 2;  // verifying1 store ver1 result (h*s_inv)*G
localparam [PROG_ADDR_W-1 : 0] VER1_ST_E            = VER1_ST_S + 5;
localparam [PROG_ADDR_W-1 : 0] PM_INIT_PK_S         = VER1_ST_E + 2;  // verifying2 R1 INIT with PK
localparam [PROG_ADDR_W-1 : 0] PM_INIT_PK_E         = PM_INIT_PK_S + 5;
localparam [PROG_ADDR_W-1 : 0] VER2_PA_S            = PM_INIT_PK_E + 2;  // verifying2 point addtion of PA((h*s_inv)*G, (r*s_inv)*PK)
localparam [PROG_ADDR_W-1 : 0] VER2_PA_E            = VER2_PA_S + 81;

localparam [PROG_ADDR_W-1 : 0] PM_INIT_DH_S         = VER2_PA_E + 2;  // Deffie-Helman Shared Key R1 INIT with PK
localparam [PROG_ADDR_W-1 : 0] PM_INIT_DH_E         = PM_INIT_DH_S + 9;

endpackage

`endif
