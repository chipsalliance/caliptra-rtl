//======================================================================
//
// ecc_dsa_sequencer.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
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
  `include "ecc_uop.sv"
  `include "ecc_dsa_uop.sv"
 

  //----------------------------------------------------------------
  // ROM content
  //----------------------------------------------------------------
 
    always_ff @(posedge clka) begin
        case(addra)
            DSA_RE_START    : douta <= '0;

            //PM CORE INIT
            DSA_INIT_S      : douta <= {DSA_UOP_WR_CORE,   CONST_ZERO_ID,           UOP_OPR_CONST_ZERO};
            DSA_INIT_S+ 1   : douta <= {DSA_UOP_WR_CORE,   CONST_ONE_ID,            UOP_OPR_CONST_ONE};
            DSA_INIT_S+ 2   : douta <= {DSA_UOP_WR_CORE,   CONST_E_a_MONT_ID,       UOP_OPR_CONST_E_a};
            DSA_INIT_S+ 3   : douta <= {DSA_UOP_WR_CORE,   CONST_ONE_p_MONT_ID,     UOP_OPR_CONST_ONE_MONT};
            DSA_INIT_S+ 4   : douta <= {DSA_UOP_WR_CORE,   CONST_G_X_MONT_ID,       UOP_OPR_CONST_GX_MONT};
            DSA_INIT_S+ 5   : douta <= {DSA_UOP_WR_CORE,   CONST_G_Y_MONT_ID,       UOP_OPR_CONST_GY_MONT};
            DSA_INIT_S+ 6   : douta <= {DSA_UOP_WR_CORE,   CONST_G_Z_MONT_ID,       UOP_OPR_CONST_GZ_MONT};
            DSA_INIT_S+ 7   : douta <= {DSA_UOP_WR_CORE,   CONST_R2_q_MONT_ID,      UOP_OPR_CONST_q_R2};
            DSA_INIT_S+ 8   : douta <= {DSA_UOP_WR_CORE,   CONST_ONE_q_MONT_ID,     UOP_OPR_CONST_ONE_q_MONT};

            //KEYGEN INIT
            DSA_KG_INIT_S       : douta <= {DSA_UOP_FIXED_MSB,  SCALAR_G_ID,        UOP_OPR_DONTCARE};
            DSA_KG_INIT_S+ 1    : douta <= {DSA_UOP_WR_SCALAR,  SCALAR_ID,          UOP_OPR_DONTCARE};
            DSA_KG_INIT_S+ 2    : douta <= {DSA_UOP_KEYGEN,     NOP_ID,             UOP_OPR_DONTCARE};
            DSA_KG_INIT_S+ 3    : douta <= {DSA_UOP_NOP,        NOP_ID,             UOP_OPR_DONTCARE};
            
            DSA_KG_RES_S        : douta <= {DSA_UOP_RD_CORE,    PUBKEYX_ID,         UOP_OPR_Qx_AFFN};
            DSA_KG_RES_S+ 1     : douta <= {DSA_UOP_RD_CORE,    PUBKEYY_ID,         UOP_OPR_Qy_AFFN};
            DSA_KG_RES_S+ 2     : douta <= {DSA_UOP_NOP,        NOP_ID,             UOP_OPR_DONTCARE};
            
            DSA_SGN_INIT_S      : douta <= {DSA_UOP_WR_CORE,    MSG_ID,             UOP_OPR_HASH_MSG};
            DSA_SGN_INIT_S+ 1   : douta <= {DSA_UOP_WR_CORE,    PRIVKEY_ID,         UOP_OPR_PRIVKEY};
            //DSA_SGN_INIT_S+ 2   : douta <= {DSA_UOP_WR_CORE,    SEED_ID,            UOP_OPR_SCALAR_G};
            DSA_SGN_INIT_S+ 2   : douta <= {DSA_UOP_WR_CORE,    SCALAR_G_ID,        UOP_OPR_SCALAR_G};
            DSA_SGN_INIT_S+ 3   : douta <= {DSA_UOP_FIXED_MSB,  SCALAR_G_ID,        UOP_OPR_DONTCARE};
            DSA_SGN_INIT_S+ 4   : douta <= {DSA_UOP_WR_SCALAR,  SCALAR_ID,          UOP_OPR_DONTCARE};
            DSA_SGN_INIT_S+ 5   : douta <= {DSA_UOP_SIGN,       NOP_ID,             UOP_OPR_DONTCARE};
            DSA_SGN_INIT_S+ 6   : douta <= {DSA_UOP_NOP,        NOP_ID,             UOP_OPR_DONTCARE};

            DSA_SGN_RES_S       : douta <= {DSA_UOP_RD_CORE,    R_ID,               UOP_OPR_SIGN_R};
            DSA_SGN_RES_S+ 1    : douta <= {DSA_UOP_RD_CORE,    S_ID,               UOP_OPR_SIGN_S};
            DSA_SGN_RES_S+ 2    : douta <= {DSA_UOP_NOP,        NOP_ID,             UOP_OPR_DONTCARE};


            default : douta <= {DSA_UOP_NOP,     NOP_ID,  UOP_OPR_DONTCARE};
        endcase 
    end

endmodule