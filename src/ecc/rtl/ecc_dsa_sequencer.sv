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
// ecc_dsa_sequencer.sv
// --------
// 
//
//
//======================================================================

module ecc_dsa_sequencer #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 32
    )
    (      
    input  wire                      clka,
    input  wire                      ena,
    input  wire  [ADDR_WIDTH-1 : 0]  addra,
    output logic [DATA_WIDTH-1 : 0]  douta
);

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  `include "ecc_pm_uop.sv"
  `include "ecc_dsa_uop.sv"
 

  //----------------------------------------------------------------
  // ROM content
  //----------------------------------------------------------------
 
    always_ff @(posedge clka) begin
        case(addra)
            //PM CORE INIT
            0       : douta <= {DSA_UOP_NOP,       NOP_ID,                  UOP_OPR_DONTCARE};
            1       : douta <= {DSA_UOP_WR_CORE,   CONST_ZERO_ID,           UOP_OPR_CONST_ZERO};
            2       : douta <= {DSA_UOP_WR_CORE,   CONST_ONE_ID,            UOP_OPR_CONST_ONE};
            3       : douta <= {DSA_UOP_WR_CORE,   CONST_E_a_MONT_ID,       UOP_OPR_CONST_E_a};
            4       : douta <= {DSA_UOP_WR_CORE,   CONST_E_3b_MONT_ID,      UOP_OPR_CONST_E_3b};
            5       : douta <= {DSA_UOP_WR_CORE,   CONST_ONE_p_MONT_ID,     UOP_OPR_CONST_ONE_MONT};
            6       : douta <= {DSA_UOP_WR_CORE,   CONST_R2_p_MONT_ID,      UOP_OPR_CONST_R2_p};
            7       : douta <= {DSA_UOP_WR_CORE,   CONST_G_X_MONT_ID,       UOP_OPR_CONST_GX_MONT};
            8       : douta <= {DSA_UOP_WR_CORE,   CONST_G_Y_MONT_ID,       UOP_OPR_CONST_GY_MONT};
            9       : douta <= {DSA_UOP_WR_CORE,   CONST_R2_q_MONT_ID,      UOP_OPR_CONST_R2_q};
            10      : douta <= {DSA_UOP_WR_CORE,   CONST_ONE_q_MONT_ID,     UOP_OPR_CONST_ONE_q_MONT};
            11      : douta <= {DSA_UOP_NOP,       NOP_ID,                  UOP_OPR_DONTCARE};

            //KEYGEN
            DSA_KG_S       : douta <= {DSA_UOP_HMAC_DRBG,  NOP_ID,             UOP_OPR_DONTCARE};
            DSA_KG_S+ 1    : douta <= {DSA_UOP_WR_CORE,    SCALAR_G_ID,        UOP_OPR_SCALAR_G};
            DSA_KG_S+ 2    : douta <= {DSA_UOP_RD_CORE,    PRIVKEY_ID,         UOP_OPR_SCALAR_G};
            DSA_KG_S+ 3    : douta <= {DSA_UOP_FIXED_MSB,  SCALAR_G_ID,        UOP_OPR_DONTCARE};
            DSA_KG_S+ 4    : douta <= {DSA_UOP_WR_SCALAR,  SCALAR_ID,          UOP_OPR_DONTCARE};
            DSA_KG_S+ 5    : douta <= {DSA_UOP_WR_CORE,    LAMBDA_ID,          UOP_OPR_LAMBDA};
            DSA_KG_S+ 6    : douta <= {DSA_UOP_KEYGEN,     NOP_ID,             UOP_OPR_DONTCARE};
            DSA_KG_S+ 7    : douta <= {DSA_UOP_NOP,        NOP_ID,             UOP_OPR_DONTCARE};
            DSA_KG_S+ 8    : douta <= {DSA_UOP_RD_CORE,    PUBKEYX_ID,         UOP_OPR_Qx_AFFN};
            DSA_KG_S+ 9    : douta <= {DSA_UOP_RD_CORE,    PUBKEYY_ID,         UOP_OPR_Qy_AFFN};
            DSA_KG_S+ 10   : douta <= {DSA_UOP_NOP,        NOP_ID,             UOP_OPR_DONTCARE};
            
            //SIGN
            DSA_SGN_S      : douta <= {DSA_UOP_WR_CORE,    MSG_ID,             UOP_OPR_HASH_MSG};
            DSA_SGN_S+ 1   : douta <= {DSA_UOP_WR_CORE,    PRIVKEY_ID,         UOP_OPR_PRIVKEY};
            DSA_SGN_S+ 2   : douta <= {DSA_UOP_HMAC_DRBG,  NOP_ID,             UOP_OPR_DONTCARE};
            DSA_SGN_S+ 3   : douta <= {DSA_UOP_WR_CORE,    SCALAR_G_ID,        UOP_OPR_SCALAR_G};
            DSA_SGN_S+ 4   : douta <= {DSA_UOP_FIXED_MSB,  SCALAR_G_ID,        UOP_OPR_DONTCARE};
            DSA_SGN_S+ 5   : douta <= {DSA_UOP_WR_SCALAR,  SCALAR_ID,          UOP_OPR_DONTCARE};
            DSA_SGN_S+ 6   : douta <= {DSA_UOP_WR_CORE,    LAMBDA_ID,          UOP_OPR_LAMBDA};
            DSA_SGN_S+ 7   : douta <= {DSA_UOP_SIGN,       NOP_ID,             UOP_OPR_DONTCARE};
            DSA_SGN_S+ 8   : douta <= {DSA_UOP_NOP,        NOP_ID,             UOP_OPR_DONTCARE};
            DSA_SGN_S+ 9   : douta <= {DSA_UOP_RD_CORE,    R_ID,               UOP_OPR_SIGN_R};
            DSA_SGN_S+ 10  : douta <= {DSA_UOP_RD_CORE,    S_ID,               UOP_OPR_SIGN_S};
            DSA_SGN_S+ 11  : douta <= {DSA_UOP_NOP,        NOP_ID,             UOP_OPR_DONTCARE};

            //VERIFY
            DSA_VER_S     : douta <= {DSA_UOP_WR_CORE,    MSG_ID,             UOP_OPR_HASH_MSG};
            DSA_VER_S+ 1  : douta <= {DSA_UOP_WR_CORE,    R_ID,               UOP_OPR_SIGN_R};
            DSA_VER_S+ 2  : douta <= {DSA_UOP_WR_CORE,    S_ID,               UOP_OPR_SIGN_S};
            DSA_VER_S+ 3  : douta <= {DSA_UOP_WR_CORE,    CONST_ONE_ID,       UOP_OPR_LAMBDA};
            DSA_VER_S+ 4  : douta <= {DSA_UOP_VERIFY0,    NOP_ID,             UOP_OPR_DONTCARE};
            DSA_VER_S+ 5  : douta <= {DSA_UOP_NOP,        NOP_ID,             UOP_OPR_DONTCARE};
            DSA_VER_S+ 6  : douta <= {DSA_UOP_RD_CORE,    SCALAR_G_ID,        UOP_OPR_SCALAR_G};
            DSA_VER_S+ 7  : douta <= {DSA_UOP_RD_CORE,    SCALAR_PK_ID,       UOP_OPR_SCALAR_PK};
            DSA_VER_S+ 8  : douta <= {DSA_UOP_FIXED_MSB,  SCALAR_G_ID,        UOP_OPR_DONTCARE};
            DSA_VER_S+ 9  : douta <= {DSA_UOP_WR_SCALAR,  SCALAR_ID,          UOP_OPR_DONTCARE};
            DSA_VER_S+ 10 : douta <= {DSA_UOP_VERIFY1,    NOP_ID,             UOP_OPR_DONTCARE};
            DSA_VER_S+ 11 : douta <= {DSA_UOP_NOP,        NOP_ID,             UOP_OPR_DONTCARE};
            DSA_VER_S+ 12 : douta <= {DSA_UOP_WR_CORE,    PUBKEYX_ID,         UOP_OPR_Qx_AFFN};
            DSA_VER_S+ 13 : douta <= {DSA_UOP_WR_CORE,    PUBKEYY_ID,         UOP_OPR_Qy_AFFN};
            DSA_VER_S+ 14 : douta <= {DSA_UOP_FIXED_MSB,  SCALAR_PK_ID,       UOP_OPR_DONTCARE};
            DSA_VER_S+ 15 : douta <= {DSA_UOP_WR_SCALAR,  SCALAR_ID,          UOP_OPR_DONTCARE};
            DSA_VER_S+ 16 : douta <= {DSA_UOP_VERIFY2,    NOP_ID,             UOP_OPR_DONTCARE};
            DSA_VER_S+ 17 : douta <= {DSA_UOP_NOP,        NOP_ID,             UOP_OPR_DONTCARE};
            DSA_VER_S+ 18 : douta <= {DSA_UOP_RD_CORE,    VERIFY_R_ID,        UOP_OPR_Qx_AFFN};
            DSA_VER_S+ 19 : douta <= {DSA_UOP_NOP,        NOP_ID,             UOP_OPR_DONTCARE};

            default : douta <= {DSA_UOP_NOP,     NOP_ID,  UOP_OPR_DONTCARE};
        endcase 
    end

endmodule
