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
// ecc_pm_sequencer.sv
// --------
// ECC point multiplication sequencer for the Secp384.
// 1) Point Addition (PA) and Point Doubling (PD) are based on 
//    "Complete Addition Formulas for Prime Order Elliptic Curves"
//    by Renes et. al. (Algorithm 1)
// 2) Modular Inversion (mod p, mod q) is based on "Fermat's little 
//    theorem (FLT)" implemented by exponentiation by squaring methos 
//    with window size of 3 bits.
// 3) All modular operations are performed in Montgomery domain.
//    mod p are modular operation respect to PRIME of SECP384 curve.
//    mod q are modular operation respect to GROUP ORDER of SECP384 curve.
// 4) To validate the given public key, we compare YY = Y^2 with 
//    RHS = X^3 + A X + B.
//
//======================================================================

module ecc_pm_sequencer 
    import ecc_pm_uop_pkg::*;
    #(
    parameter ADDR_WIDTH = 10,
    parameter DATA_WIDTH = 32
    )
    (      
    input  wire                      clka,
    input  wire                      reset_n,
    input  wire                      zeroize,
    input  wire                      ena,
    input  wire  [ADDR_WIDTH-1 : 0]  addra,
    output logic [DATA_WIDTH-1 : 0]  douta
    );

  //----------------------------------------------------------------
  // ROM content
  //----------------------------------------------------------------
 
    always_ff @(posedge clka or negedge reset_n) 
    begin : prog_rom
        if (!reset_n) begin
            douta <= '0;
        end
        else if (zeroize) begin
            douta <= '0;
        end
        else begin
            if (ena) begin
                unique case(addra)
                    NOP : douta <= '0;
                    1   : douta <= '0;
                    
                    //R1 INIT with Randomized G
                    PM_INIT_G_S     : douta <= {UOP_DO_MUL_p,   UOP_OPR_LAMBDA,            UOP_OPR_CONST_R2_p};   // R1_Z = mm(Lambda, R2)
                    PM_INIT_G_S+ 1  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_Z};
                    PM_INIT_G_S+ 2  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_GX_MONT,     UOP_OPR_R1_Z};         // R1_X = mm(GX_MONT, R0_Z)
                    PM_INIT_G_S+ 3  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_X};
                    PM_INIT_G_S+ 4  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_GY_MONT,     UOP_OPR_R1_Z};         // R1_Y = mm(GY_MONT, R0_Z)
                    PM_INIT_G_S+ 5  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_Y};
                    
                    //R0 INIT with O
                    PM_INIT_S       : douta <= {UOP_DO_ADD_p,   UOP_OPR_CONST_ZERO,        UOP_OPR_CONST_ZERO};  // R0_X = 0
                    PM_INIT_S+ 1    : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_X,              UOP_OPR_DONTCARE};
                    PM_INIT_S+ 2    : douta <= {UOP_DO_ADD_p,   UOP_OPR_CONST_ONE_MONT,    UOP_OPR_CONST_ZERO};  // R0_Y = fp_mult(1, R2, p)
                    PM_INIT_S+ 3    : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_Y,              UOP_OPR_DONTCARE};
                    PM_INIT_S+ 4    : douta <= {UOP_DO_ADD_p,   UOP_OPR_CONST_ZERO,        UOP_OPR_CONST_ZERO};  // R0_Z = 0
                    PM_INIT_S+ 5    : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_Z,              UOP_OPR_DONTCARE};
                    PM_INIT_S+ 6    : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,          UOP_OPR_DONTCARE};
                    PM_INIT_S+ 7    : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,          UOP_OPR_DONTCARE};
                    PM_INIT_S+ 8    : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,          UOP_OPR_DONTCARE};
                    PM_INIT_S+ 9    : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,          UOP_OPR_DONTCARE}; 

                    // PA : R1 = PA(R0, R1)
                    PA_S      : douta <= {UOP_DO_MUL_p,   UOP_OPR_R0_X,       UOP_OPR_R1_X};  // A = fp_mult(P0.X, P1.X, p)
                    PA_S+ 1   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A};
                    PA_S+ 2   : douta <= {UOP_DO_MUL_p,   UOP_OPR_R0_Y,       UOP_OPR_R1_Y};  // B = fp_mult(P0.Y, P1.Y, p)
                    PA_S+ 3   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_B};
                    PA_S+ 4   : douta <= {UOP_DO_MUL_p,   UOP_OPR_R0_Z,       UOP_OPR_R1_Z};  // C = fp_mult(P0.Z, P1.Z, p)
                    PA_S+ 5   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C};
                    PA_S+ 6   : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Y};  // D = (P0.X + P0.Y) % p
                    PA_S+ 7   : douta <= {UOP_ST_ADD_p,   UOP_OPR_D,          UOP_OPR_DONTCARE};
                    PA_S+ 8   : douta <= {UOP_DO_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_R1_Y};  // E = (P1.X + P1.Y) % p
                    PA_S+ 9   : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    PA_S+ 10  : douta <= {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_E};     // D = fp_mult(D, E, p)
                    PA_S+ 11  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_D};
                    PA_S+ 12  : douta <= {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_B};     // E = (A + B) % p
                    PA_S+ 13  : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    PA_S+ 14  : douta <= {UOP_DO_SUB_p,   UOP_OPR_D,          UOP_OPR_E};     // D = (D - E) % p
                    PA_S+ 15  : douta <= {UOP_ST_ADD_p,   UOP_OPR_D,          UOP_OPR_DONTCARE};
                    PA_S+ 16  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z};  // E = (P0.X + P0.Z) % p
                    PA_S+ 17  : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    PA_S+ 18  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_R1_Z};  // F = (P1.X + P1.Z) % p
                    PA_S+ 19  : douta <= {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE};
                    PA_S+ 20  : douta <= {UOP_DO_MUL_p,   UOP_OPR_E,          UOP_OPR_F};     // E = fp_mult(E, F, p)
                    PA_S+ 21  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_E};
                    PA_S+ 22  : douta <= {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_C};     // F = (A + C) % p
                    PA_S+ 23  : douta <= {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE};
                    PA_S+ 24  : douta <= {UOP_DO_SUB_p,   UOP_OPR_E,          UOP_OPR_F};     // E = (E - F) % p
                    PA_S+ 25  : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    PA_S+ 26  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_R0_Z};  // F = (P0.Y + P0.Z) % p
                    PA_S+ 27  : douta <= {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE};
                    PA_S+ 28  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R1_Y,       UOP_OPR_R1_Z};  // X3 = (P1.Y + P1.Z) % p
                    PA_S+ 29  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_DONTCARE};        
                    PA_S+ 30  : douta <= {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_R1_X};  // F = fp_mult(F, X3, p)
                    PA_S+ 31  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_F};
                    PA_S+ 32  : douta <= {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_C};     // X3 = (B + C) % p
                    PA_S+ 33  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_DONTCARE};
                    PA_S+ 34  : douta <= {UOP_DO_SUB_p,   UOP_OPR_F,          UOP_OPR_R1_X};  // F = (F - X3) % p
                    PA_S+ 35  : douta <= {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE};    
                    PA_S+ 36  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_E};     // Z3 = fp_mult(ECC.a, E, p)
                    PA_S+ 37  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R1_Z};
                    PA_S+ 38  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_3b, UOP_OPR_C};     // X3 = fp_mult(ECC.3b, C, p)
                    PA_S+ 39  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R1_X};
                    PA_S+ 40  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_R1_Z};  // Z3 = (X3 + Z3) % p
                    PA_S+ 41  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R1_Z,       UOP_OPR_DONTCARE};
                    PA_S+ 42  : douta <= {UOP_DO_SUB_p,   UOP_OPR_B,          UOP_OPR_R1_Z};  // X3 = (B - Z3) % p
                    PA_S+ 43  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_DONTCARE};
                    PA_S+ 44  : douta <= {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_R1_Z};  // Z3 = (B + Z3) % p
                    PA_S+ 45  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R1_Z,       UOP_OPR_DONTCARE};
                    PA_S+ 46  : douta <= {UOP_DO_MUL_p,   UOP_OPR_R1_X,       UOP_OPR_R1_Z};  // Y3 = fp_mult(X3, Z3, p)
                    PA_S+ 47  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R1_Y};
                    PA_S+ 48  : douta <= {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_A};     // B = (A + A) % p
                    PA_S+ 49  : douta <= {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE};
                    PA_S+ 50  : douta <= {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_A};     // B = (B + A) % p
                    PA_S+ 51  : douta <= {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE};
                    PA_S+ 52  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_C};     // C = fp_mult(ECC.a, C, p)
                    PA_S+ 53  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C};
                    PA_S+ 54  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_3b, UOP_OPR_E};     // E = fp_mult(ECC.3b, E, p)
                    PA_S+ 55  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_E};
                    PA_S+ 56  : douta <= {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_C};     // B = (B + C) % p
                    PA_S+ 57  : douta <= {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE};
                    PA_S+ 58  : douta <= {UOP_DO_SUB_p,   UOP_OPR_A,          UOP_OPR_C};     // C = (A - C) % p
                    PA_S+ 59  : douta <= {UOP_ST_ADD_p,   UOP_OPR_C,          UOP_OPR_DONTCARE};            
                    PA_S+ 60  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_C};     // C = fp_mult(ECC.a, C, p)
                    PA_S+ 61  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C};
                    PA_S+ 62  : douta <= {UOP_DO_ADD_p,   UOP_OPR_E,          UOP_OPR_C};     // E = (E + C) % p
                    PA_S+ 63  : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    PA_S+ 64  : douta <= {UOP_DO_MUL_p,   UOP_OPR_B,          UOP_OPR_E};     // A = fp_mult(B, E, p)
                    PA_S+ 65  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A};            
                    PA_S+ 66  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R1_Y,       UOP_OPR_A};     // Y3 = (Y3 + A) % p
                    PA_S+ 67  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R1_Y,       UOP_OPR_DONTCARE};
                    PA_S+ 68  : douta <= {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_E};     // A = fp_mult(F, E, p)
                    PA_S+ 69  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A};
                    PA_S+ 70  : douta <= {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_R1_X};  // X3 = fp_mult(D, X3, p)
                    PA_S+ 71  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R1_X};            
                    PA_S+ 72  : douta <= {UOP_DO_SUB_p,   UOP_OPR_R1_X,       UOP_OPR_A};     // X3 = (X3 - A) % p
                    PA_S+ 73  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_DONTCARE};
                    PA_S+ 74  : douta <= {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_B};     // A = fp_mult(D, B, p)
                    PA_S+ 75  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A};
                    PA_S+ 76  : douta <= {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_R1_Z};  // Z3 = fp_mult(F, Z3, p)
                    PA_S+ 77  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R1_Z};            
                    PA_S+ 78  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R1_Z,       UOP_OPR_A};     // Z3 = (Z3 + A) % p
                    PA_S+ 79  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R1_Z,       UOP_OPR_DONTCARE};

                    //PD : R0 = PD(R0)
                    PD_S      : douta <= {UOP_DO_MUL_p,   UOP_OPR_R0_X,       UOP_OPR_R0_X};  // A = fp_mult(P0.X, P0.X, p)
                    PD_S+ 1   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A};
                    PD_S+ 2   : douta <= {UOP_DO_MUL_p,   UOP_OPR_R0_Y,       UOP_OPR_R0_Y};  // B = fp_mult(P0.Y, P0.Y, p)
                    PD_S+ 3   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_B};
                    PD_S+ 4   : douta <= {UOP_DO_MUL_p,   UOP_OPR_R0_Z,       UOP_OPR_R0_Z};  // C = fp_mult(P0.Z, P0.Z, p)
                    PD_S+ 5   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C};
                    PD_S+ 6   : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Y};  // D = (P0.X + P0.Y) % p
                    PD_S+ 7   : douta <= {UOP_ST_ADD_p,   UOP_OPR_D,          UOP_OPR_DONTCARE};
                    PD_S+ 8   : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Y};  // E = (P0.X + P0.Y) % p
                    PD_S+ 9   : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    PD_S+ 10  : douta <= {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_E};     // D = fp_mult(D, E, p)
                    PD_S+ 11  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_D};
                    PD_S+ 12  : douta <= {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_B};     // E = (A + B) % p
                    PD_S+ 13  : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    PD_S+ 14  : douta <= {UOP_DO_SUB_p,   UOP_OPR_D,          UOP_OPR_E};     // D = (D - E) % p
                    PD_S+ 15  : douta <= {UOP_ST_ADD_p,   UOP_OPR_D,          UOP_OPR_DONTCARE};
                    PD_S+ 16  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z};  // E = (P0.X + P0.Z) % p
                    PD_S+ 17  : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    PD_S+ 18  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z};  // F = (P0.X + P0.Z) % p
                    PD_S+ 19  : douta <= {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE};
                    PD_S+ 20  : douta <= {UOP_DO_MUL_p,   UOP_OPR_E,          UOP_OPR_F};     // E = fp_mult(E, F, p)
                    PD_S+ 21  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_E};
                    PD_S+ 22  : douta <= {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_C};     // F = (A + C) % p
                    PD_S+ 23  : douta <= {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE};
                    PD_S+ 24  : douta <= {UOP_DO_SUB_p,   UOP_OPR_E,          UOP_OPR_F};     // E = (E - F) % p
                    PD_S+ 25  : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    PD_S+ 26  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_R0_Z};  // F = (P0.Y + P0.Z) % p
                    PD_S+ 27  : douta <= {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE};
                    PD_S+ 28  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_R0_Z};  // X3 = (P0.Y + P0.Z) % p
                    PD_S+ 29  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE};        
                    PD_S+ 30  : douta <= {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_R0_X};  // F = fp_mult(F, X3, p)
                    PD_S+ 31  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_F};
                    PD_S+ 32  : douta <= {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_C};     // X3 = (B + C) % p
                    PD_S+ 33  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE};
                    PD_S+ 34  : douta <= {UOP_DO_SUB_p,   UOP_OPR_F,          UOP_OPR_R0_X};  // F = (F - X3) % p
                    PD_S+ 35  : douta <= {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE};    
                    PD_S+ 36  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_E};     // Z3 = fp_mult(ECC.a, E, p)
                    PD_S+ 37  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_Z};
                    PD_S+ 38  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_3b, UOP_OPR_C};     // X3 = fp_mult(ECC.3b, C, p)
                    PD_S+ 39  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_X};
                    PD_S+ 40  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z};  // Z3 = (X3 + Z3) % p
                    PD_S+ 41  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_DONTCARE};
                    PD_S+ 42  : douta <= {UOP_DO_SUB_p,   UOP_OPR_B,          UOP_OPR_R0_Z};  // X3 = (B - Z3) % p
                    PD_S+ 43  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE};
                    PD_S+ 44  : douta <= {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_R0_Z};  // Z3 = (B + Z3) % p
                    PD_S+ 45  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_DONTCARE};
                    PD_S+ 46  : douta <= {UOP_DO_MUL_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z};  // Y3 = fp_mult(X3, Z3, p)
                    PD_S+ 47  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_Y};
                    PD_S+ 48  : douta <= {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_A};     // B = (A + A) % p
                    PD_S+ 49  : douta <= {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE};
                    PD_S+ 50  : douta <= {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_A};     // B = (B + A) % p
                    PD_S+ 51  : douta <= {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE};
                    PD_S+ 52  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_C};     // C = fp_mult(ECC.a, C, p)
                    PD_S+ 53  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C};
                    PD_S+ 54  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_3b, UOP_OPR_E};     // E = fp_mult(ECC.3b, E, p)
                    PD_S+ 55  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_E};
                    PD_S+ 56  : douta <= {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_C};     // B = (B + C) % p
                    PD_S+ 57  : douta <= {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE};
                    PD_S+ 58  : douta <= {UOP_DO_SUB_p,   UOP_OPR_A,          UOP_OPR_C};     // C = (A - C) % p
                    PD_S+ 59  : douta <= {UOP_ST_ADD_p,   UOP_OPR_C,          UOP_OPR_DONTCARE};            
                    PD_S+ 60  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_C};     // C = fp_mult(ECC.a, C, p)
                    PD_S+ 61  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C};
                    PD_S+ 62  : douta <= {UOP_DO_ADD_p,   UOP_OPR_E,          UOP_OPR_C};     // E = (E + C) % p
                    PD_S+ 63  : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    PD_S+ 64  : douta <= {UOP_DO_MUL_p,   UOP_OPR_B,          UOP_OPR_E};     // A = fp_mult(B, E, p)
                    PD_S+ 65  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A};            
                    PD_S+ 66  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_A};     // Y3 = (Y3 + A) % p
                    PD_S+ 67  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_DONTCARE};
                    PD_S+ 68  : douta <= {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_E};     // A = fp_mult(F, E, p)
                    PD_S+ 69  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A};
                    PD_S+ 70  : douta <= {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_R0_X};  // X3 = fp_mult(D, X3, p)
                    PD_S+ 71  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_X};            
                    PD_S+ 72  : douta <= {UOP_DO_SUB_p,   UOP_OPR_R0_X,       UOP_OPR_A};     // X3 = (X3 - A) % p
                    PD_S+ 73  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE};
                    PD_S+ 74  : douta <= {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_B};     // A = fp_mult(D, B, p)
                    PD_S+ 75  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A};
                    PD_S+ 76  : douta <= {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_R0_Z};  // Z3 = fp_mult(F, Z3, p)
                    PD_S+ 77  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_Z};            
                    PD_S+ 78  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_A};     // Z3 = (Z3 + A) % p
                    PD_S+ 79  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_DONTCARE};
                    PD_S+ 80  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    PD_S+ 81  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    PD_S+ 82  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    PD_S+ 83  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE}; 

                    //INV mod p
                    INV_S      : douta <= {UOP_DO_ADD_p,   UOP_OPR_CONST_ZERO, UOP_OPR_CONST_ONE_MONT};    // precompute[0] = UOP_OPR_CONST_ONE_MONT % p
                    INV_S+ 1   : douta <= {UOP_ST_ADD_p,   UOP_OPR_INV_PRE0,   UOP_OPR_DONTCARE};
                    INV_S+ 2   : douta <= {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE0};    // precompute[1] = fp_mult(Z, precompute[0], p)
                    INV_S+ 3   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE1};
                    INV_S+ 4   : douta <= {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE1};    // precompute[2] = fp_mult(Z, precompute[1], p)
                    INV_S+ 5   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE2};
                    INV_S+ 6   : douta <= {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE2};    // precompute[3] = fp_mult(Z, precompute[2], p)
                    INV_S+ 7   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE3};
                    INV_S+ 8   : douta <= {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE3};    // precompute[4] = fp_mult(Z, precompute[3], p)
                    INV_S+ 9   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE4};
                    INV_S+ 10  : douta <= {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE4};    // precompute[5] = fp_mult(Z, precompute[4], p)
                    INV_S+ 11  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE5};
                    INV_S+ 12  : douta <= {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE5};    // precompute[6] = fp_mult(Z, precompute[5], p)
                    INV_S+ 13  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE6};
                    INV_S+ 14  : douta <= {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE6};    // precompute[7] = fp_mult(Z, precompute[6], p)
                    INV_S+ 15  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE7};
                    INV_S+ 16  : douta <= {UOP_DO_MUL_p,   UOP_OPR_INV_PRE0,   UOP_OPR_INV_PRE0};    // a_inv = fp_mult(precompute[0], precompute[0], p)
                    INV_S+ 17  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 18  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 19  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 20  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 21  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 22  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 23  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 24  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 25  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 26  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 27  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 28  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 29  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 30  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 31  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 32  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 33  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 34  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 35  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 36  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 37  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 38  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 39  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 40  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 41  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 42  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 43  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 44  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 45  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 46  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 47  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 48  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 49  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 50  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 51  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 52  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 53  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 54  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 55  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 56  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 57  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 58  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 59  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 60  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 61  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 62  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 63  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 64  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 65  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 66  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 67  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 68  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 69  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 70  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 71  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 72  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 73  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 74  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 75  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 76  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 77  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 78  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 79  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 80  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 81  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 82  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 83  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 84  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 85  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 86  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 87  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 88  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 89  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 90  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 91  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 92  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 93  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 94  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 95  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 96  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 97  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 98  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 99  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 100  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 101  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 102  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 103  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 104  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 105  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 106  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 107  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 108  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 109  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 110  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 111  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 112  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 113  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 114  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 115  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 116  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 117  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 118  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 119  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 120  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 121  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 122  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 123  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 124  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 125  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 126  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 127  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 128  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 129  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 130  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 131  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 132  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 133  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 134  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 135  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 136  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 137  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 138  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 139  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 140  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 141  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 142  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 143  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 144  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 145  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 146  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 147  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 148  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 149  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 150  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 151  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 152  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 153  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 154  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 155  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 156  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 157  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 158  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 159  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 160  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 161  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 162  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 163  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 164  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 165  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 166  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 167  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 168  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 169  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 170  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 171  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 172  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 173  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 174  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 175  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 176  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 177  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 178  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 179  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 180  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 181  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 182  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 183  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 184  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 185  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 186  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 187  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 188  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 189  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 190  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 191  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 192  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 193  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 194  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 195  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 196  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 197  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 198  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 199  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 200  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 201  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 202  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 203  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 204  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 205  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 206  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 207  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 208  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 209  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 210  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 211  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 212  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 213  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 214  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 215  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 216  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 217  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 218  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 219  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 220  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 221  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 222  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 223  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 224  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 225  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 226  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 227  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 228  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 229  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 230  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 231  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 232  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 233  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 234  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 235  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 236  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 237  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 238  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 239  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 240  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 241  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 242  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 243  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 244  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 245  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 246  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 247  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 248  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 249  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 250  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 251  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 252  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 253  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 254  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 255  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 256  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 257  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 258  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 259  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 260  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 261  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 262  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 263  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 264  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 265  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 266  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 267  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 268  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 269  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 270  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 271  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 272  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 273  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 274  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 275  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 276  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 277  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 278  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 279  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 280  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 281  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 282  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 283  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 284  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 285  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 286  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 287  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 288  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 289  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 290  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 291  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 292  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 293  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 294  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 295  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 296  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 297  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 298  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 299  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 300  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 301  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 302  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 303  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 304  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 305  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 306  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 307  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 308  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 309  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 310  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 311  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 312  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 313  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 314  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 315  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 316  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 317  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 318  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 319  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 320  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 321  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 322  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 323  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 324  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 325  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 326  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 327  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 328  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 329  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 330  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 331  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 332  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 333  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 334  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 335  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 336  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 337  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 338  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 339  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 340  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 341  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 342  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 343  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 344  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 345  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 346  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 347  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 348  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 349  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 350  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 351  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 352  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 353  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 354  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 355  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 356  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 357  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 358  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 359  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 360  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 361  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 362  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 363  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 364  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 365  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 366  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 367  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 368  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 369  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 370  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 371  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 372  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 373  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 374  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 375  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 376  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 377  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 378  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 379  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 380  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 381  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 382  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 383  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 384  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 385  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 386  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 387  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 388  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 389  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 390  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 391  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 392  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 393  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 394  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 395  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 396  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 397  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 398  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 399  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 400  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 401  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 402  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 403  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 404  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 405  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 406  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 407  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 408  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 409  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 410  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 411  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 412  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 413  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 414  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 415  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 416  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 417  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 418  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 419  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 420  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 421  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 422  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 423  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 424  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 425  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 426  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 427  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 428  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 429  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 430  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 431  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 432  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 433  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 434  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 435  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 436  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 437  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 438  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 439  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 440  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 441  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 442  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 443  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 444  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 445  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 446  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 447  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 448  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 449  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 450  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 451  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 452  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 453  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 454  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 455  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 456  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 457  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 458  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 459  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 460  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 461  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 462  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 463  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 464  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 465  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 466  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 467  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 468  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 469  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 470  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 471  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 472  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 473  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 474  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 475  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 476  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 477  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 478  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 479  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 480  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 481  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 482  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 483  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 484  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 485  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 486  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 487  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 488  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 489  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 490  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 491  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 492  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 493  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 494  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 495  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 496  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 497  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 498  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 499  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 500  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 501  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 502  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 503  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 504  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 505  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 506  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 507  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 508  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 509  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 510  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 511  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 512  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 513  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 514  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 515  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 516  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 517  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 518  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 519  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 520  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 521  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 522  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 523  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 524  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 525  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 526  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 527  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 528  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 529  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 530  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 531  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 532  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 533  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 534  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 535  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 536  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 537  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 538  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 539  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 540  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 541  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 542  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 543  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 544  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 545  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 546  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 547  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 548  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 549  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 550  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 551  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 552  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 553  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 554  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 555  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 556  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 557  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 558  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 559  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 560  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 561  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 562  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 563  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 564  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 565  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 566  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 567  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 568  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 569  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 570  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 571  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 572  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 573  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 574  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 575  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 576  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 577  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 578  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 579  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 580  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 581  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 582  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 583  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 584  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 585  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 586  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 587  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 588  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 589  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 590  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 591  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 592  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 593  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 594  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 595  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 596  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 597  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 598  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 599  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 600  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 601  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 602  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 603  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 604  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 605  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 606  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 607  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 608  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 609  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 610  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 611  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 612  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 613  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 614  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 615  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 616  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 617  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 618  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 619  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 620  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 621  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 622  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 623  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 624  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 625  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 626  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 627  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 628  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 629  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 630  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 631  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 632  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 633  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 634  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 635  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 636  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 637  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 638  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 639  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 640  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 641  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 642  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 643  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 644  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 645  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 646  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 647  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 648  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 649  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 650  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 651  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 652  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 653  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 654  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 655  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 656  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 657  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 658  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 659  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 660  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 661  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 662  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 663  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 664  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 665  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 666  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 667  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 668  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 669  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 670  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 671  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 672  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 673  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 674  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 675  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 676  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 677  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 678  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 679  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 680  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 681  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 682  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 683  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 684  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 685  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 686  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 687  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 688  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 689  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 690  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 691  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 692  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 693  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 694  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 695  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 696  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 697  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 698  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 699  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 700  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 701  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 702  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE3};    // a_inv = fp_mult(a_inv, precompute[3], p)
                    INV_S+ 703  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 704  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 705  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 706  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 707  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 708  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 709  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 710  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 711  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 712  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 713  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 714  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 715  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 716  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 717  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 718  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 719  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 720  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 721  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 722  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 723  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 724  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 725  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 726  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 727  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 728  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 729  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 730  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 731  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 732  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 733  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 734  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 735  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 736  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 737  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 738  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 739  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 740  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 741  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 742  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 743  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 744  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 745  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 746  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 747  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 748  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 749  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 750  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 751  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 752  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 753  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 754  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 755  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 756  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 757  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 758  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 759  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 760  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 761  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 762  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 763  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 764  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 765  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 766  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 767  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 768  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 769  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 770  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 771  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 772  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 773  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 774  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 775  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 776  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 777  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 778  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 779  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 780  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 781  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 782  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 783  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 784  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 785  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 786  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 787  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 788  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 789  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 790  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 791  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 792  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 793  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 794  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 795  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 796  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 797  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 798  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 799  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 800  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 801  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 802  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 803  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 804  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 805  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 806  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 807  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 808  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 809  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 810  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 811  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 812  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 813  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 814  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 815  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 816  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 817  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 818  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 819  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 820  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 821  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 822  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 823  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 824  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 825  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 826  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 827  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 828  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 829  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 830  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 831  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 832  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 833  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 834  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 835  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 836  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 837  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 838  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 839  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 840  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 841  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 842  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 843  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 844  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 845  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 846  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 847  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 848  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 849  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 850  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 851  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 852  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 853  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 854  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 855  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 856  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 857  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 858  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 859  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 860  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 861  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 862  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 863  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 864  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 865  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 866  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 867  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 868  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 869  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 870  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 871  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 872  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 873  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 874  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 875  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 876  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 877  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 878  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 879  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 880  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 881  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 882  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 883  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 884  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 885  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 886  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 887  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 888  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 889  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 890  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 891  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 892  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 893  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 894  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 895  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 896  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 897  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 898  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 899  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 900  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 901  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 902  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 903  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 904  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 905  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 906  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 907  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 908  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 909  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 910  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 911  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 912  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 913  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 914  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 915  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 916  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 917  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 918  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 919  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 920  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 921  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 922  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 923  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 924  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 925  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 926  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 927  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 928  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 929  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 930  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 931  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 932  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 933  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 934  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 935  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 936  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 937  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 938  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 939  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 940  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 941  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 942  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 943  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 944  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 945  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 946  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 947  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 948  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 949  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 950  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], p)
                    INV_S+ 951  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 952  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 953  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 954  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 955  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 956  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 957  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 958  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE3};    // a_inv = fp_mult(a_inv, precompute[3], p)
                    INV_S+ 959  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 960  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 961  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 962  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 963  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 964  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 965  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 966  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 967  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 968  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 969  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 970  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 971  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 972  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 973  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 974  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 975  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 976  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 977  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 978  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 979  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 980  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 981  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 982  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 983  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 984  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 985  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 986  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 987  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 988  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 989  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 990  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 991  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 992  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 993  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 994  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 995  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 996  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 997  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 998  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 999  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1000  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1001  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1002  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1003  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1004  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1005  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1006  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 1007  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1008  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1009  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1010  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1011  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1012  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1013  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1014  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 1015  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1016  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1017  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1018  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1019  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1020  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1021  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1022  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 1023  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1024  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1025  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1026  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1027  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1028  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1029  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1030  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], p)
                    INV_S+ 1031  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1032  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1033  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1034  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1035  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1036  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, p)
                    INV_S+ 1037  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INV_S+ 1038  : douta <= {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE5};    // INV_OUT = fp_mult(a_inv, precompute[5], p)
                    INV_S+ 1039  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_OUT};

                    //Conversion from projective Mont (X,Y,Z) to affine normanl (x,y)
                    CONV_S      : douta <= {UOP_DO_MUL_p,   UOP_OPR_INV_OUT,    UOP_OPR_R0_Y};          // y_MONT = fp_mult(Z_inv, Y_MONT, p)
                    CONV_S+ 1   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_Qy_MONT};
                    CONV_S+ 2   : douta <= {UOP_DO_MUL_p,   UOP_OPR_INV_OUT,    UOP_OPR_R0_X};          // x_MONT = fp_mult(Z_inv, X_MONT, p)
                    CONV_S+ 3   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_Qx_MONT};
                    CONV_S+ 4   : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_ONE,  UOP_OPR_Qy_MONT};       // y_affine = fp_mult(y_MONT, 1, p)
                    CONV_S+ 5   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_Qy_AFFN};
                    CONV_S+ 6   : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_ONE,  UOP_OPR_Qx_MONT};       // y_affine = fp_mult(y_MONT, 1, p)
                    CONV_S+ 7   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_Qx_AFFN};
                    CONV_S+ 8   : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    CONV_S+ 9   : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    CONV_S+ 10  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    CONV_S+ 11  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};

                    // SIGNATURE R
                    SIGN0_S     : douta <= {UOP_DO_ADD_q,   UOP_OPR_CONST_ZERO, UOP_OPR_Qx_AFFN};       // R = Qx_AFFN
                    SIGN0_S+ 1  : douta <= {UOP_ST_ADD_q,   UOP_OPR_SIGN_R,     UOP_OPR_DONTCARE};
                    SIGN0_S+ 2  : douta <= {UOP_DO_MUL_q,   UOP_OPR_SIGN_R,     UOP_OPR_CONST_R2_q};    // E = mm(R, R2) % q
                    SIGN0_S+ 3  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_E};
                    SIGN0_S+ 4  : douta <= {UOP_DO_MUL_q,   UOP_OPR_SCALAR_G,   UOP_OPR_CONST_R2_q};    // k_MONT = mm(k, R2) % q
                    SIGN0_S+ 5  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_IN};
                    SIGN0_S+ 6  : douta <= {UOP_DO_MUL_q,   UOP_OPR_PRIVKEY,    UOP_OPR_CONST_R2_q};    // A = mm(privKey, R2) % q
                    SIGN0_S+ 7  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A};
                    SIGN0_S+ 8  : douta <= {UOP_DO_MUL_q,   UOP_OPR_HASH_MSG,   UOP_OPR_CONST_R2_q};    // B = mm(h, R2) % q
                    SIGN0_S+ 9  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_B};
                    SIGN0_S+ 10 : douta <= {UOP_DO_MUL_q,   UOP_OPR_MASKING,    UOP_OPR_CONST_R2_q};    // D = mm(masking_d, R2) % q
                    SIGN0_S+ 11 : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_D};
                    SIGN0_S+ 12 : douta <= {UOP_DO_SUB_q,   UOP_OPR_A,          UOP_OPR_D};             // A = (A - D) % q
                    SIGN0_S+ 13 : douta <= {UOP_ST_ADD_q,   UOP_OPR_A,          UOP_OPR_DONTCARE};
                    SIGN0_S+ 14 : douta <= {UOP_DO_SUB_q,   UOP_OPR_B,          UOP_OPR_D};             // B = (B - D) % q
                    SIGN0_S+ 15 : douta <= {UOP_ST_ADD_q,   UOP_OPR_B,          UOP_OPR_DONTCARE};
                    SIGN0_S+ 16 : douta <= {UOP_DO_MUL_q,   UOP_OPR_A,          UOP_OPR_E};             // C = mm(A, E) % q
                    SIGN0_S+ 17 : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_C};
                    SIGN0_S+ 18 : douta <= {UOP_DO_MUL_q,   UOP_OPR_D,          UOP_OPR_E};             // F = mm(D, E) % q
                    SIGN0_S+ 19 : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_F};
                    SIGN0_S+ 20 : douta <= {UOP_DO_ADD_q,   UOP_OPR_D,          UOP_OPR_C};             // C = (C + D) % q
                    SIGN0_S+ 21 : douta <= {UOP_ST_ADD_q,   UOP_OPR_C,          UOP_OPR_DONTCARE};
                    SIGN0_S+ 22 : douta <= {UOP_DO_ADD_q,   UOP_OPR_B,          UOP_OPR_F};             // D = (B + F) % q
                    SIGN0_S+ 23 : douta <= {UOP_ST_ADD_q,   UOP_OPR_D,          UOP_OPR_DONTCARE};
                    SIGN0_S+ 24 : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    SIGN0_S+ 25 : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    SIGN0_S+ 26 : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    SIGN0_S+ 27 : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};

                    //INV MOD q
                    INVq_S      : douta <= {UOP_DO_ADD_q,   UOP_OPR_CONST_ZERO, UOP_OPR_CONST_ONE_q_MONT};    // precompute[0] = UOP_OPR_CONST_ONE_q_MONT % q
                    INVq_S+ 1   : douta <= {UOP_ST_ADD_q,   UOP_OPR_INV_PRE0,   UOP_OPR_DONTCARE};
                    INVq_S+ 2   : douta <= {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE0};    // precompute[1] = fp_mult(Z, precompute[0], q)
                    INVq_S+ 3   : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE1};
                    INVq_S+ 4   : douta <= {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE1};    // precompute[2] = fp_mult(Z, precompute[1], q)
                    INVq_S+ 5   : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE2};
                    INVq_S+ 6   : douta <= {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE2};    // precompute[3] = fp_mult(Z, precompute[2], q)
                    INVq_S+ 7   : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE3};
                    INVq_S+ 8   : douta <= {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE3};    // precompute[4] = fp_mult(Z, precompute[3], q)
                    INVq_S+ 9   : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE4};
                    INVq_S+ 10  : douta <= {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE4};    // precompute[5] = fp_mult(Z, precompute[4], q)
                    INVq_S+ 11  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE5};
                    INVq_S+ 12  : douta <= {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE5};    // precompute[6] = fp_mult(Z, precompute[5], q)
                    INVq_S+ 13  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE6};
                    INVq_S+ 14  : douta <= {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE6};    // precompute[7] = fp_mult(Z, precompute[6], q)
                    INVq_S+ 15  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE7};
                    INVq_S+ 16  : douta <= {UOP_DO_MUL_q,   UOP_OPR_INV_PRE0,   UOP_OPR_INV_PRE0};    // a_inv = fp_mult(precompute[0], precompute[0], q)
                    INVq_S+ 17  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 18  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 19  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 20  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 21  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 22  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 23  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 24  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 25  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 26  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 27  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 28  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 29  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 30  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 31  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 32  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 33  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 34  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 35  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 36  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 37  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 38  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 39  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 40  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 41  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 42  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 43  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 44  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 45  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 46  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 47  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 48  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 49  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 50  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 51  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 52  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 53  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 54  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 55  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 56  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 57  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 58  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 59  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 60  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 61  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 62  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 63  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 64  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 65  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 66  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 67  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 68  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 69  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 70  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 71  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 72  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 73  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 74  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 75  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 76  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 77  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 78  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 79  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 80  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 81  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 82  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 83  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 84  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 85  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 86  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 87  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 88  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 89  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 90  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 91  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 92  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 93  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 94  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 95  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 96  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 97  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 98  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 99  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 100  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 101  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 102  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 103  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 104  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 105  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 106  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 107  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 108  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 109  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 110  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 111  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 112  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 113  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 114  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 115  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 116  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 117  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 118  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 119  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 120  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 121  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 122  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 123  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 124  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 125  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 126  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 127  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 128  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 129  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 130  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 131  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 132  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 133  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 134  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 135  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 136  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 137  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 138  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 139  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 140  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 141  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 142  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 143  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 144  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 145  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 146  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 147  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 148  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 149  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 150  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 151  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 152  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 153  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 154  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 155  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 156  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 157  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 158  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 159  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 160  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 161  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 162  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 163  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 164  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 165  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 166  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 167  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 168  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 169  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 170  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 171  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 172  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 173  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 174  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 175  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 176  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 177  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 178  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 179  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 180  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 181  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 182  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 183  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 184  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 185  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 186  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 187  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 188  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 189  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 190  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 191  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 192  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 193  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 194  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 195  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 196  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 197  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 198  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 199  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 200  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 201  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 202  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 203  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 204  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 205  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 206  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 207  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 208  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 209  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 210  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 211  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 212  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 213  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 214  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 215  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 216  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 217  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 218  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 219  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 220  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 221  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 222  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 223  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 224  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 225  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 226  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 227  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 228  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 229  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 230  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 231  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 232  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 233  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 234  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 235  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 236  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 237  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 238  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 239  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 240  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 241  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 242  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 243  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 244  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 245  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 246  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 247  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 248  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 249  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 250  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 251  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 252  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 253  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 254  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 255  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 256  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 257  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 258  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 259  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 260  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 261  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 262  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 263  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 264  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 265  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 266  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 267  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 268  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 269  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 270  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 271  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 272  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 273  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 274  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 275  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 276  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 277  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 278  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 279  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 280  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 281  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 282  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 283  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 284  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 285  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 286  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 287  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 288  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 289  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 290  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 291  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 292  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 293  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 294  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 295  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 296  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 297  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 298  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 299  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 300  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 301  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 302  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 303  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 304  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 305  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 306  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 307  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 308  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 309  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 310  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 311  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 312  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 313  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 314  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 315  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 316  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 317  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 318  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 319  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 320  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 321  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 322  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 323  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 324  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 325  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 326  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 327  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 328  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 329  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 330  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 331  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 332  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 333  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 334  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 335  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 336  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 337  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 338  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 339  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 340  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 341  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 342  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 343  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 344  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 345  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 346  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 347  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 348  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 349  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 350  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 351  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 352  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 353  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 354  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 355  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 356  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 357  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 358  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 359  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 360  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 361  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 362  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 363  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 364  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 365  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 366  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 367  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 368  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 369  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 370  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 371  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 372  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 373  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 374  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 375  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 376  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 377  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 378  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 379  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 380  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 381  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 382  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 383  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 384  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 385  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 386  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 387  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 388  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 389  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 390  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 391  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 392  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 393  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 394  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 395  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 396  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 397  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 398  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 399  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 400  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 401  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 402  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 403  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 404  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 405  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 406  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 407  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 408  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 409  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 410  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 411  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 412  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 413  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 414  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 415  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 416  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 417  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 418  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 419  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 420  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 421  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 422  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 423  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 424  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 425  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 426  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 427  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 428  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 429  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 430  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 431  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 432  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 433  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 434  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 435  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 436  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 437  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 438  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 439  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 440  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 441  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 442  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 443  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 444  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 445  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 446  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 447  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 448  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 449  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 450  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 451  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 452  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 453  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 454  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 455  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 456  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 457  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 458  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 459  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 460  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 461  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 462  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 463  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 464  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 465  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 466  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 467  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 468  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 469  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 470  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 471  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 472  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 473  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 474  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 475  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 476  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 477  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 478  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 479  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 480  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 481  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 482  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 483  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 484  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 485  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 486  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 487  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 488  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 489  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 490  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 491  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 492  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 493  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 494  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 495  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 496  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 497  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 498  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 499  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 500  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 501  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 502  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 503  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 504  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 505  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 506  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 507  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 508  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 509  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 510  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 511  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 512  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 513  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 514  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 515  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 516  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 517  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 518  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 519  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 520  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 521  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 522  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 523  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 524  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 525  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 526  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 527  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 528  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 529  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 530  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 531  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 532  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 533  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 534  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 535  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 536  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 537  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 538  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 539  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 540  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 541  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 542  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE1};    // a_inv = fp_mult(a_inv, precompute[1], q)
                    INVq_S+ 543  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 544  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 545  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 546  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 547  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 548  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 549  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 550  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 551  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 552  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 553  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 554  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 555  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 556  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 557  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 558  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 559  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 560  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 561  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 562  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 563  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 564  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 565  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 566  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE1};    // a_inv = fp_mult(a_inv, precompute[1], q)
                    INVq_S+ 567  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 568  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 569  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 570  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 571  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 572  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 573  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 574  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE5};    // a_inv = fp_mult(a_inv, precompute[5], q)
                    INVq_S+ 575  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 576  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 577  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 578  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 579  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 580  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 581  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 582  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE1};    // a_inv = fp_mult(a_inv, precompute[1], q)
                    INVq_S+ 583  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 584  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 585  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 586  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 587  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 588  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 589  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 590  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE5};    // a_inv = fp_mult(a_inv, precompute[5], q)
                    INVq_S+ 591  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 592  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 593  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 594  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 595  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 596  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 597  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 598  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE4};    // a_inv = fp_mult(a_inv, precompute[4], q)
                    INVq_S+ 599  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 600  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 601  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 602  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 603  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 604  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 605  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 606  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], q)
                    INVq_S+ 607  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 608  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 609  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 610  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 611  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 612  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 613  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 614  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE3};    // a_inv = fp_mult(a_inv, precompute[3], q)
                    INVq_S+ 615  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 616  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 617  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 618  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 619  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 620  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 621  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 622  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 623  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 624  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 625  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 626  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 627  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 628  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 629  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 630  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE2};    // a_inv = fp_mult(a_inv, precompute[2], q)
                    INVq_S+ 631  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 632  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 633  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 634  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 635  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 636  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 637  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 638  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], q)
                    INVq_S+ 639  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 640  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 641  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 642  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 643  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 644  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 645  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 646  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 647  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 648  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 649  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 650  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 651  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 652  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 653  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 654  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 655  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 656  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 657  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 658  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 659  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 660  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 661  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 662  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE1};    // a_inv = fp_mult(a_inv, precompute[1], q)
                    INVq_S+ 663  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 664  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 665  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 666  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 667  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 668  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 669  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 670  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE3};    // a_inv = fp_mult(a_inv, precompute[3], q)
                    INVq_S+ 671  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 672  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 673  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 674  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 675  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 676  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 677  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 678  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE3};    // a_inv = fp_mult(a_inv, precompute[3], q)
                    INVq_S+ 679  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 680  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 681  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 682  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 683  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 684  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 685  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 686  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE5};    // a_inv = fp_mult(a_inv, precompute[5], q)
                    INVq_S+ 687  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 688  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 689  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 690  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 691  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 692  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 693  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 694  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 695  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 696  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 697  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 698  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 699  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 700  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 701  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 702  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE5};    // a_inv = fp_mult(a_inv, precompute[5], q)
                    INVq_S+ 703  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 704  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 705  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 706  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 707  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 708  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 709  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 710  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE3};    // a_inv = fp_mult(a_inv, precompute[3], q)
                    INVq_S+ 711  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 712  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 713  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 714  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 715  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 716  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 717  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 718  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], q)
                    INVq_S+ 719  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 720  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 721  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 722  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 723  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 724  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 725  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 726  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], q)
                    INVq_S+ 727  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 728  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 729  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 730  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 731  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 732  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 733  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 734  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 735  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 736  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 737  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 738  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 739  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 740  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 741  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 742  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE4};    // a_inv = fp_mult(a_inv, precompute[4], q)
                    INVq_S+ 743  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 744  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 745  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 746  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 747  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 748  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 749  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 750  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], q)
                    INVq_S+ 751  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 752  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 753  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 754  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 755  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 756  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 757  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 758  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 759  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 760  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 761  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 762  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 763  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 764  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 765  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 766  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 767  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 768  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 769  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 770  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 771  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 772  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 773  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 774  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 775  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 776  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 777  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 778  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 779  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 780  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 781  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 782  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE2};    // a_inv = fp_mult(a_inv, precompute[2], q)
                    INVq_S+ 783  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 784  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 785  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 786  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 787  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 788  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 789  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 790  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE2};    // a_inv = fp_mult(a_inv, precompute[2], q)
                    INVq_S+ 791  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 792  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 793  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 794  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 795  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 796  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 797  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 798  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE2};    // a_inv = fp_mult(a_inv, precompute[2], q)
                    INVq_S+ 799  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 800  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 801  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 802  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 803  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 804  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 805  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 806  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE1};    // a_inv = fp_mult(a_inv, precompute[1], q)
                    INVq_S+ 807  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 808  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 809  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 810  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 811  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 812  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 813  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 814  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE3};    // a_inv = fp_mult(a_inv, precompute[3], q)
                    INVq_S+ 815  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 816  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 817  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 818  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 819  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 820  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 821  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 822  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], q)
                    INVq_S+ 823  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 824  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 825  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 826  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 827  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 828  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 829  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 830  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE2};    // a_inv = fp_mult(a_inv, precompute[2], q)
                    INVq_S+ 831  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 832  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 833  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 834  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 835  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 836  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 837  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 838  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE4};    // a_inv = fp_mult(a_inv, precompute[4], q)
                    INVq_S+ 839  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 840  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 841  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 842  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 843  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 844  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 845  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 846  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE7};    // a_inv = fp_mult(a_inv, precompute[7], q)
                    INVq_S+ 847  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 848  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 849  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 850  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 851  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 852  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 853  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 854  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE3};    // a_inv = fp_mult(a_inv, precompute[3], q)
                    INVq_S+ 855  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 856  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 857  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 858  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 859  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 860  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 861  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 862  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 863  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 864  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 865  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 866  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 867  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 868  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 869  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 870  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE5};    // a_inv = fp_mult(a_inv, precompute[5], q)
                    INVq_S+ 871  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 872  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 873  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 874  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 875  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 876  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 877  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 878  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 879  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 880  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 881  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 882  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 883  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 884  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 885  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 886  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 887  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 888  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 889  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 890  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 891  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 892  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 893  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 894  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE3};    // a_inv = fp_mult(a_inv, precompute[3], q)
                    INVq_S+ 895  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 896  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 897  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 898  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 899  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 900  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 901  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 902  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE5};    // a_inv = fp_mult(a_inv, precompute[5], q)
                    INVq_S+ 903  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 904  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 905  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 906  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 907  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 908  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 909  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 910  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE4};    // a_inv = fp_mult(a_inv, precompute[4], q)
                    INVq_S+ 911  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 912  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 913  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 914  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 915  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 916  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 917  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 918  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE0};    // a_inv = fp_mult(a_inv, precompute[0], q)
                    INVq_S+ 919  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 920  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 921  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 922  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 923  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 924  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 925  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 926  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 927  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 928  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 929  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 930  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 931  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 932  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 933  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 934  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE2};    // a_inv = fp_mult(a_inv, precompute[2], q)
                    INVq_S+ 935  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 936  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 937  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 938  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 939  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 940  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 941  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 942  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 943  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 944  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 945  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 946  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 947  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 948  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 949  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 950  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE5};    // a_inv = fp_mult(a_inv, precompute[5], q)
                    INVq_S+ 951  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 952  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 953  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 954  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 955  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 956  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 957  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 958  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE3};    // a_inv = fp_mult(a_inv, precompute[3], q)
                    INVq_S+ 959  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 960  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 961  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 962  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 963  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 964  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 965  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 966  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE1};    // a_inv = fp_mult(a_inv, precompute[1], q)
                    INVq_S+ 967  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 968  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 969  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 970  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 971  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 972  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 973  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 974  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE4};    // a_inv = fp_mult(a_inv, precompute[4], q)
                    INVq_S+ 975  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 976  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 977  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 978  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 979  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 980  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 981  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 982  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 983  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 984  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 985  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 986  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 987  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 988  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 989  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 990  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE1};    // a_inv = fp_mult(a_inv, precompute[1], q)
                    INVq_S+ 991  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 992  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 993  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 994  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 995  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 996  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 997  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 998  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE2};    // a_inv = fp_mult(a_inv, precompute[2], q)
                    INVq_S+ 999  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1000  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1001  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1002  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1003  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1004  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1005  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1006  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE2};    // a_inv = fp_mult(a_inv, precompute[2], q)
                    INVq_S+ 1007  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1008  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1009  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1010  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1011  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1012  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1013  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1014  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE4};    // a_inv = fp_mult(a_inv, precompute[4], q)
                    INVq_S+ 1015  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1016  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1017  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1018  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1019  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1020  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1021  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1022  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE5};    // a_inv = fp_mult(a_inv, precompute[5], q)
                    INVq_S+ 1023  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1024  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1025  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1026  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1027  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1028  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1029  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1030  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE6};    // a_inv = fp_mult(a_inv, precompute[6], q)
                    INVq_S+ 1031  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1032  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1033  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1034  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1035  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1036  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV};       // a_inv = fp_mult(a_inv, a_inv, q)
                    INVq_S+ 1037  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV};
                    INVq_S+ 1038  : douta <= {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_INV_PRE1};    // INV_OUT = fp_mult(a_inv, precompute[1], q)
                    INVq_S+ 1039  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_OUT};
                    INVq_S+ 1040  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    INVq_S+ 1041  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    INVq_S+ 1042  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    INVq_S+ 1043  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};

                    //SIGNING part1
                    SIGN1_S       : douta <= {UOP_DO_MUL_q,   UOP_OPR_INV_OUT,    UOP_OPR_C};           // C = fp_mult(C, k_inv, q)
                    SIGN1_S+ 1    : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_C};
                    SIGN1_S+ 2    : douta <= {UOP_DO_MUL_q,   UOP_OPR_INV_OUT,    UOP_OPR_D};           // D = fp_mult(D, k_inv, q)
                    SIGN1_S+ 3    : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_D};
                    SIGN1_S+ 4    : douta <= {UOP_DO_ADD_q,   UOP_OPR_C,          UOP_OPR_D};           // B = C + D % q
                    SIGN1_S+ 5    : douta <= {UOP_ST_ADD_q,   UOP_OPR_B,          UOP_OPR_DONTCARE};
                    SIGN1_S+ 6    : douta <= {UOP_DO_MUL_q,   UOP_OPR_CONST_ONE,  UOP_OPR_B};           // B = fp_mult(B, 1, q)
                    SIGN1_S+ 7    : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_SIGN_S};
                    SIGN1_S+ 8    : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    SIGN1_S+ 9    : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    SIGN1_S+ 10   : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    SIGN1_S+ 11   : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};

                    // check the given public key is a valid curve point
                    CHK_PK_S       : douta <= {UOP_DO_MUL_p,   UOP_OPR_Qy_AFFN,   UOP_OPR_CONST_R2_p};  // A = mm(Qy, R2) % q
                    CHK_PK_S+ 1    : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,  UOP_OPR_A};
                    CHK_PK_S+ 2    : douta <= {UOP_DO_MUL_p,   UOP_OPR_A,         UOP_OPR_A};           // A = A*A % q
                    CHK_PK_S+ 3    : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,  UOP_OPR_A};
                    CHK_PK_S+ 4    : douta <= {UOP_DO_MUL_p,   UOP_OPR_Qx_AFFN,   UOP_OPR_CONST_R2_p};  // B = mm(Qx, R2) % q
                    CHK_PK_S+ 5    : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,  UOP_OPR_B};
                    CHK_PK_S+ 6    : douta <= {UOP_DO_MUL_p,   UOP_OPR_B,         UOP_OPR_B};           // C = B*B % q
                    CHK_PK_S+ 7    : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,  UOP_OPR_C};
                    CHK_PK_S+ 8    : douta <= {UOP_DO_MUL_p,   UOP_OPR_C,         UOP_OPR_B};           // C = C*B % q
                    CHK_PK_S+ 9    : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,  UOP_OPR_C};
                    CHK_PK_S+ 10   : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a, UOP_OPR_B};           // D = ECC.a*B % q
                    CHK_PK_S+ 11   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,  UOP_OPR_D};
                    CHK_PK_S+ 12   : douta <= {UOP_DO_ADD_p,   UOP_OPR_C,         UOP_OPR_D};           // C = C + D % q
                    CHK_PK_S+ 13   : douta <= {UOP_ST_ADD_p,   UOP_OPR_C,         UOP_OPR_DONTCARE};
                    CHK_PK_S+ 14   : douta <= {UOP_DO_ADD_p,   UOP_OPR_C,         UOP_OPR_CONST_E_b};   // C = C + ECC.b % q
                    CHK_PK_S+ 15   : douta <= {UOP_ST_ADD_p,   UOP_OPR_C,         UOP_OPR_DONTCARE};
                    CHK_PK_S+ 16   : douta <= {UOP_DO_SUB_p,   UOP_OPR_A,         UOP_OPR_C};           // C = C + ECC.b % q
                    CHK_PK_S+ 17   : douta <= {UOP_ST_ADD_p,   UOP_OPR_PK_VALID,  UOP_OPR_DONTCARE};
                    CHK_PK_S+ 18   : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,  UOP_OPR_DONTCARE};
                    CHK_PK_S+ 19   : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,  UOP_OPR_DONTCARE};
                    CHK_PK_S+ 20   : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,  UOP_OPR_DONTCARE};
                    CHK_PK_S+ 21   : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,  UOP_OPR_DONTCARE};
    
                    // VERIFY0 SCALAR part0 to convert inputs to Mont domain
                    VER0_P0_S     : douta <= {UOP_DO_MUL_q,   UOP_OPR_HASH_MSG,   UOP_OPR_CONST_R2_q};    // A = mm(h, R2) % q
                    VER0_P0_S+ 1  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A};
                    VER0_P0_S+ 2  : douta <= {UOP_DO_MUL_q,   UOP_OPR_SIGN_R,     UOP_OPR_CONST_R2_q};    // B = mm(R, R2) % q
                    VER0_P0_S+ 3  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_B};
                    VER0_P0_S+ 4  : douta <= {UOP_DO_MUL_q,   UOP_OPR_SIGN_S,     UOP_OPR_CONST_R2_q};    // INV_IN = mm(S, R2) % q
                    VER0_P0_S+ 5  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_IN};
                    VER0_P0_S+ 6  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    VER0_P0_S+ 7  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    VER0_P0_S+ 8  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    VER0_P0_S+ 9  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};

                    // VERIFY0 SCALAR part1 to compute (h*s_inv) and (r*s_inv)
                    VER0_P1_S     : douta <= {UOP_DO_MUL_q,   UOP_OPR_INV_OUT,    UOP_OPR_A};             // A = mm(h, S_INV) % q
                    VER0_P1_S+ 1  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A};
                    VER0_P1_S+ 2  : douta <= {UOP_DO_MUL_q,   UOP_OPR_CONST_ONE,  UOP_OPR_A};             // hs1 = mm(A, 1) % q
                    VER0_P1_S+ 3  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_SCALAR_G};
                    VER0_P1_S+ 4  : douta <= {UOP_DO_MUL_q,   UOP_OPR_INV_OUT,    UOP_OPR_B};             // B = mm(r, S_INV) % q
                    VER0_P1_S+ 5  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_B};
                    VER0_P1_S+ 6  : douta <= {UOP_DO_MUL_q,   UOP_OPR_CONST_ONE,  UOP_OPR_B};             // rs1 = mm(B, 1) % q
                    VER0_P1_S+ 7  : douta <= {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_SCALAR_PK};
                    VER0_P1_S+ 8  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    VER0_P1_S+ 9  : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    VER0_P1_S+ 10 : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
                    VER0_P1_S+ 11 : douta <= {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};

                    //STORE VER1 result (h*s_inv)*G
                    VER1_ST_S     : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_CONST_ZERO};
                    VER1_ST_S+ 1  : douta <= {UOP_ST_ADD_p,   UOP_OPR_P1_X_MONT,  UOP_OPR_DONTCARE};
                    VER1_ST_S+ 2  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_CONST_ZERO};
                    VER1_ST_S+ 3  : douta <= {UOP_ST_ADD_p,   UOP_OPR_P1_Y_MONT,  UOP_OPR_DONTCARE};
                    VER1_ST_S+ 4  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_CONST_ZERO};
                    VER1_ST_S+ 5  : douta <= {UOP_ST_ADD_p,   UOP_OPR_P1_Z_MONT,  UOP_OPR_DONTCARE};

                    //VER2 R1 INIT with PK
                    PM_INIT_PK_S    : douta <= {UOP_DO_MUL_p,   UOP_OPR_Qx_AFFN,           UOP_OPR_CONST_R2_p};
                    PM_INIT_PK_S+ 1 : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_X};
                    PM_INIT_PK_S+ 2 : douta <= {UOP_DO_MUL_p,   UOP_OPR_Qy_AFFN,           UOP_OPR_CONST_R2_p};
                    PM_INIT_PK_S+ 3 : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_Y};
                    PM_INIT_PK_S+ 4 : douta <= {UOP_DO_ADD_p,   UOP_OPR_CONST_ONE_MONT,    UOP_OPR_CONST_ZERO};
                    PM_INIT_PK_S+ 5 : douta <= {UOP_ST_ADD_p,   UOP_OPR_R1_Z,              UOP_OPR_DONTCARE};

                    //VER2 point addtion of PA((h*s_inv)*G, (r*s_inv)*PK)
                    VER2_PA_S      : douta <= {UOP_DO_MUL_p,   UOP_OPR_R0_X,       UOP_OPR_P1_X_MONT};  // A = fp_mult(P0.X, P1.X, p)
                    VER2_PA_S+ 1   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A};
                    VER2_PA_S+ 2   : douta <= {UOP_DO_MUL_p,   UOP_OPR_R0_Y,       UOP_OPR_P1_Y_MONT};  // B = fp_mult(P0.Y, P1.Y, p)
                    VER2_PA_S+ 3   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_B};
                    VER2_PA_S+ 4   : douta <= {UOP_DO_MUL_p,   UOP_OPR_R0_Z,       UOP_OPR_P1_Z_MONT};  // C = fp_mult(P0.Z, P1.Z, p)
                    VER2_PA_S+ 5   : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C};
                    VER2_PA_S+ 6   : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Y};       // D = (P0.X + P0.Y) % p
                    VER2_PA_S+ 7   : douta <= {UOP_ST_ADD_p,   UOP_OPR_D,          UOP_OPR_DONTCARE};
                    VER2_PA_S+ 8   : douta <= {UOP_DO_ADD_p,   UOP_OPR_P1_X_MONT,  UOP_OPR_P1_Y_MONT};  // E = (P1.X + P1.Y) % p
                    VER2_PA_S+ 9   : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    VER2_PA_S+ 10  : douta <= {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_E};          // D = fp_mult(D, E, p)
                    VER2_PA_S+ 11  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_D};
                    VER2_PA_S+ 12  : douta <= {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_B};          // E = (A + B) % p
                    VER2_PA_S+ 13  : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    VER2_PA_S+ 14  : douta <= {UOP_DO_SUB_p,   UOP_OPR_D,          UOP_OPR_E};          // D = (D - E) % p
                    VER2_PA_S+ 15  : douta <= {UOP_ST_ADD_p,   UOP_OPR_D,          UOP_OPR_DONTCARE};
                    VER2_PA_S+ 16  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z};       // E = (P0.X + P0.Z) % p
                    VER2_PA_S+ 17  : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    VER2_PA_S+ 18  : douta <= {UOP_DO_ADD_p,   UOP_OPR_P1_X_MONT,  UOP_OPR_P1_Z_MONT};  // F = (P1.X + P1.Z) % p
                    VER2_PA_S+ 19  : douta <= {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE};
                    VER2_PA_S+ 20  : douta <= {UOP_DO_MUL_p,   UOP_OPR_E,          UOP_OPR_F};          // E = fp_mult(E, F, p)
                    VER2_PA_S+ 21  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_E};
                    VER2_PA_S+ 22  : douta <= {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_C};          // F = (A + C) % p
                    VER2_PA_S+ 23  : douta <= {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE};
                    VER2_PA_S+ 24  : douta <= {UOP_DO_SUB_p,   UOP_OPR_E,          UOP_OPR_F};          // E = (E - F) % p
                    VER2_PA_S+ 25  : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    VER2_PA_S+ 26  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_R0_Z};       // F = (P0.Y + P0.Z) % p
                    VER2_PA_S+ 27  : douta <= {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE};
                    VER2_PA_S+ 28  : douta <= {UOP_DO_ADD_p,   UOP_OPR_P1_Y_MONT,  UOP_OPR_P1_Z_MONT};  // X3 = (P1.Y + P1.Z) % p
                    VER2_PA_S+ 29  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE};        
                    VER2_PA_S+ 30  : douta <= {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_R0_X};       // F = fp_mult(F, X3, p)
                    VER2_PA_S+ 31  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_F};
                    VER2_PA_S+ 32  : douta <= {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_C};          // X3 = (B + C) % p
                    VER2_PA_S+ 33  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE};
                    VER2_PA_S+ 34  : douta <= {UOP_DO_SUB_p,   UOP_OPR_F,          UOP_OPR_R0_X};       // F = (F - X3) % p
                    VER2_PA_S+ 35  : douta <= {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE};    
                    VER2_PA_S+ 36  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_E};          // Z3 = fp_mult(ECC.a, E, p)
                    VER2_PA_S+ 37  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_Z};
                    VER2_PA_S+ 38  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_3b, UOP_OPR_C};          // X3 = fp_mult(ECC.3b, C, p)
                    VER2_PA_S+ 39  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_X};
                    VER2_PA_S+ 40  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z};       // Z3 = (X3 + Z3) % p
                    VER2_PA_S+ 41  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_DONTCARE};
                    VER2_PA_S+ 42  : douta <= {UOP_DO_SUB_p,   UOP_OPR_B,          UOP_OPR_R0_Z};       // X3 = (B - Z3) % p
                    VER2_PA_S+ 43  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE};
                    VER2_PA_S+ 44  : douta <= {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_R0_Z};       // Z3 = (B + Z3) % p
                    VER2_PA_S+ 45  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_DONTCARE};
                    VER2_PA_S+ 46  : douta <= {UOP_DO_MUL_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z};       // Y3 = fp_mult(X3, Z3, p)
                    VER2_PA_S+ 47  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_Y};
                    VER2_PA_S+ 48  : douta <= {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_A};          // B = (A + A) % p
                    VER2_PA_S+ 49  : douta <= {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE};
                    VER2_PA_S+ 50  : douta <= {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_A};          // B = (B + A) % p
                    VER2_PA_S+ 51  : douta <= {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE};
                    VER2_PA_S+ 52  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_C};          // C = fp_mult(ECC.a, C, p)
                    VER2_PA_S+ 53  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C};
                    VER2_PA_S+ 54  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_3b, UOP_OPR_E};          // E = fp_mult(ECC.3b, E, p)
                    VER2_PA_S+ 55  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_E};
                    VER2_PA_S+ 56  : douta <= {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_C};          // B = (B + C) % p
                    VER2_PA_S+ 57  : douta <= {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE};
                    VER2_PA_S+ 58  : douta <= {UOP_DO_SUB_p,   UOP_OPR_A,          UOP_OPR_C};          // C = (A - C) % p
                    VER2_PA_S+ 59  : douta <= {UOP_ST_ADD_p,   UOP_OPR_C,          UOP_OPR_DONTCARE};            
                    VER2_PA_S+ 60  : douta <= {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_C};          // C = fp_mult(ECC.a, C, p)
                    VER2_PA_S+ 61  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C};
                    VER2_PA_S+ 62  : douta <= {UOP_DO_ADD_p,   UOP_OPR_E,          UOP_OPR_C};          // E = (E + C) % p
                    VER2_PA_S+ 63  : douta <= {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE};
                    VER2_PA_S+ 64  : douta <= {UOP_DO_MUL_p,   UOP_OPR_B,          UOP_OPR_E};          // A = fp_mult(B, E, p)
                    VER2_PA_S+ 65  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A};            
                    VER2_PA_S+ 66  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_A};          // Y3 = (Y3 + A) % p
                    VER2_PA_S+ 67  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_DONTCARE};
                    VER2_PA_S+ 68  : douta <= {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_E};          // A = fp_mult(F, E, p)
                    VER2_PA_S+ 69  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A};
                    VER2_PA_S+ 70  : douta <= {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_R0_X};       // X3 = fp_mult(D, X3, p)
                    VER2_PA_S+ 71  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_X};            
                    VER2_PA_S+ 72  : douta <= {UOP_DO_SUB_p,   UOP_OPR_R0_X,       UOP_OPR_A};          // X3 = (X3 - A) % p
                    VER2_PA_S+ 73  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE};
                    VER2_PA_S+ 74  : douta <= {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_B};          // A = fp_mult(D, B, p)
                    VER2_PA_S+ 75  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A};
                    VER2_PA_S+ 76  : douta <= {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_R0_Z};       // Z3 = fp_mult(F, Z3, p)
                    VER2_PA_S+ 77  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_Z};            
                    VER2_PA_S+ 78  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_A};          // Z3 = (Z3 + A) % p
                    VER2_PA_S+ 79  : douta <= {UOP_ST_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_DONTCARE};
                    VER2_PA_S+ 80  : douta <= {UOP_DO_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_CONST_ZERO}; // Zinv_IN = P1_Z
                    VER2_PA_S+ 81  : douta <= {UOP_ST_ADD_p,   UOP_OPR_INV_IN,     UOP_OPR_DONTCARE};

                    //DH SHARED KEY R1 INIT with PK
                    PM_INIT_DH_S     : douta <= {UOP_DO_MUL_p,   UOP_OPR_LAMBDA,            UOP_OPR_CONST_R2_p};   // R1_Z = mm(Lambda, R2)
                    PM_INIT_DH_S+ 1  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_Z};
                    PM_INIT_DH_S+ 2  : douta <= {UOP_DO_MUL_p,   UOP_OPR_Qx_AFFN,           UOP_OPR_CONST_R2_p};   // R1_X = mm(PK_X, R2)
                    PM_INIT_DH_S+ 3  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_X};
                    PM_INIT_DH_S+ 4  : douta <= {UOP_DO_MUL_p,   UOP_OPR_R1_X,              UOP_OPR_R1_Z};         // R1_X = mm(PKX_MONT, R0_Z)
                    PM_INIT_DH_S+ 5  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_X};
                    PM_INIT_DH_S+ 6  : douta <= {UOP_DO_MUL_p,   UOP_OPR_Qy_AFFN,           UOP_OPR_CONST_R2_p};   // R1_Y = mm(PK_Y, R2)
                    PM_INIT_DH_S+ 7  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_Y};
                    PM_INIT_DH_S+ 8  : douta <= {UOP_DO_MUL_p,   UOP_OPR_R1_Y,              UOP_OPR_R1_Z};         // R1_Y = mm(PKY_MONT, R0_Z)
                    PM_INIT_DH_S+ 9  : douta <= {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_Y};

                    default : douta <= {UOP_NOP,     UOP_OPR_DONTCARE,  UOP_OPR_DONTCARE};
                endcase 
            end
        end
    end // prog_rom

endmodule
