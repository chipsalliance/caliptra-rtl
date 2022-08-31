//======================================================================
//
// ecc_uop.sv
// --------
// ECC instructin for the point multiplication.
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
localparam [DSA_UOP_ADDR_WIDTH-1 : 0] DSA_UOP_FIXED_MSB            = 8'b1000_0000;

localparam [DSA_OPR_ADDR_WIDTH-1 : 0] NOP_ID                   = 0;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_ZERO_ID            = 1;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_ONE_ID             = 2;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_E_a_MONT_ID        = 3;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_ONE_p_MONT_ID      = 4;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_G_X_MONT_ID        = 5;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_G_Y_MONT_ID        = 6;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_G_Z_MONT_ID        = 7;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_R2_q_MONT_ID       = 8;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_ONE_q_MONT_ID      = 9;
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

localparam DSA_RE_START                 = 0;
localparam DSA_INIT_S                   = 2;
localparam DSA_INIT_E                   = DSA_INIT_S + 8;
localparam DSA_NOP                      = DSA_INIT_E + 2;  //12
localparam DSA_KG_INIT_S                = DSA_NOP + 2;  //14
localparam DSA_KG_INIT_E                = DSA_KG_INIT_S + 3; //17
localparam DSA_KG_RES_S                 = DSA_KG_INIT_E + 1;  //18
localparam DSA_KG_RES_E                 = DSA_KG_RES_S + 2; //20
localparam DSA_SGN_INIT_S               = DSA_KG_RES_E + 2; //22
localparam DSA_SGN_INIT_E               = DSA_SGN_INIT_S + 6; //28
localparam DSA_SGN_RES_S                = DSA_SGN_INIT_E + 1; //29
localparam DSA_SGN_RES_E                = DSA_SGN_RES_S + 2; //31

localparam DSA_VER0_INIT_S              = 0;
localparam DSA_VER0_INIT_E              = 0;
localparam DSA_VER0_RES_S               = 0;
localparam DSA_VER0_RES_E               = 0;
localparam DSA_VER1_INIT_S              = 0;
localparam DSA_VER1_INIT_E              = 0;
localparam DSA_VER1_RES_S               = 0;
localparam DSA_VER1_RES_E               = 0;
localparam DSA_VER2_INIT_S              = 0;
localparam DSA_VER2_INIT_E              = 0;
localparam DSA_VER2_RES_S               = 0;
localparam DSA_VER2_RES_E               = 0;


