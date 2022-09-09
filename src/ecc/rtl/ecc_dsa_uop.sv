//======================================================================
//
// ecc_dsa_uop.sv
// --------
// ECC instructin for the digital signature algorithm.
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

localparam DSA_INSTRUCTION_LENGTH       = 24;    // opcode + 2 * operand
localparam DSA_PROG_ADDR_W              = 6;

localparam integer DSA_UOP_ADDR_WIDTH    = 8;
localparam integer DSA_OPR_ADDR_WIDTH    = 8;

localparam [DSA_UOP_ADDR_WIDTH-1 : 0] DSA_UOP_NOP                  = 8'b0000_0000;
localparam [DSA_UOP_ADDR_WIDTH-1 : 0] DSA_UOP_WR_CORE              = 8'b0000_0010;
localparam [DSA_UOP_ADDR_WIDTH-1 : 0] DSA_UOP_WR_SCALAR            = 8'b0000_0011;
localparam [DSA_UOP_ADDR_WIDTH-1 : 0] DSA_UOP_RD_CORE              = 8'b0000_0100;
localparam [DSA_UOP_ADDR_WIDTH-1 : 0] DSA_UOP_KEYGEN               = 8'b0000_1000;
localparam [DSA_UOP_ADDR_WIDTH-1 : 0] DSA_UOP_SIGN                 = 8'b0001_0000;
localparam [DSA_UOP_ADDR_WIDTH-1 : 0] DSA_UOP_VERIFY0              = 8'b0010_0000;
localparam [DSA_UOP_ADDR_WIDTH-1 : 0] DSA_UOP_VERIFY1              = 8'b0010_1000;
localparam [DSA_UOP_ADDR_WIDTH-1 : 0] DSA_UOP_VERIFY2              = 8'b0011_0000;
localparam [DSA_UOP_ADDR_WIDTH-1 : 0] DSA_UOP_HMAC_DRBG            = 8'b0100_0000;
localparam [DSA_UOP_ADDR_WIDTH-1 : 0] DSA_UOP_FIXED_MSB            = 8'b1000_0000;



localparam [DSA_OPR_ADDR_WIDTH-1 : 0] NOP_ID                   = 0;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_ZERO_ID            = 1;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_ONE_ID             = 2;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_E_a_MONT_ID        = 3;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_ONE_p_MONT_ID      = 4;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_R2_p_MONT_ID       = 5;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_G_X_MONT_ID        = 6;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_G_Y_MONT_ID        = 7;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_G_Z_MONT_ID        = 8;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_R2_q_MONT_ID       = 9;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_ONE_q_MONT_ID      = 10;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] SEED_ID                  = 16;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] MSG_ID                   = 17;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] PRIVKEY_ID               = 18;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] PUBKEYX_ID               = 19;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] PUBKEYY_ID               = 20;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] R_ID                     = 21;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] S_ID                     = 22;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] SCALAR_ID                = 23;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] SCALAR_G_ID              = 24;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] SCALAR_PK_ID             = 25;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] R_VERIFY_ID              = 26;

localparam DSA_NOP                      = 12;  
localparam DSA_KG_S                     = DSA_NOP + 2; 
localparam DSA_KG_E                     = DSA_KG_S + 9; 
localparam DSA_SGN_S                    = DSA_KG_E + 2; 
localparam DSA_SGN_E                    = DSA_SGN_S + 10; 
localparam DSA_VER_S                    = DSA_SGN_E + 2; 
localparam DSA_VER_E                    = DSA_VER_S + 18;