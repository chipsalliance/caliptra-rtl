//======================================================================
//
// ecc_pm_uop.sv
// --------
// ECC instructin for the point multiplication (PM).
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

localparam INSTRUCTION_LENGTH       = 24;    // opcode + 2 * operand
localparam PROG_ADDR_W              = 15;

localparam integer UOP_ADDR_WIDTH    = 8;
localparam integer OPR_ADDR_WIDTH    = 8;

localparam [UOP_ADDR_WIDTH-1 : 0] UOP_NOP                   = 8'b0000_0000;

localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_MUL_p              = 8'b0001_0000;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_ST_MUL_p              = 8'b0000_0001;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_ADD_p              = 8'b0000_1000;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_SUB_p              = 8'b0000_1100;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_ST_ADD_p              = 8'b0000_0010;

localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_MUL_q              = 8'b0011_0000;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_ST_MUL_q              = 8'b0010_0001;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_ADD_q              = 8'b0010_1000;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_SUB_q              = 8'b0010_1100;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_ST_ADD_q              = 8'b0010_0010;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_DONTCARE          = 8'dX;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ZERO        = 8'd00;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ONE         = 8'd01;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_E_a         = 8'd02;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_E_3b        = 8'd03;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ONE_MONT    = 8'd04;  // Mont_mult(1, R2) % p
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_R2_p        = 8'd05;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_GX_MONT     = 8'd06;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_GY_MONT     = 8'd07;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R0_X              = 8'd08;  // 8'b0000_1000;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R0_Y              = 8'd09;  // 8'b0000_1001;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R0_Z              = 8'd10;  // 8'b0000_1010;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R1_X              = 8'd12;  // 8'b0000_1100;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R1_Y              = 8'd13;  // 8'b0000_1101;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R1_Z              = 8'd14;  // 8'b0000_1110;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qx_AFFN           = 8'd16;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qy_AFFN           = 8'd17;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_SIGN_R            = 8'd18;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_SIGN_S            = 8'd19;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_PRIVKEY           = 8'd20;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_HASH_MSG          = 8'd21;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_SCALAR_G          = 8'd22;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_SCALAR_PK         = 8'd23;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_LAMBDA            = 8'd24;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ONE_q_MONT  = 8'd28;  // Mont_mult(1, R2) % q
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_R2_q        = 8'd29;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_A                 = 8'd32;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_B                 = 8'd33;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_C                 = 8'd34;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_D                 = 8'd35;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_E                 = 8'd36;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_F                 = 8'd37;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_G                 = 8'd38;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_H                 = 8'd39;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_J                 = 8'd40;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_IN            = UOP_OPR_R0_Z;  // operand to be inverted
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE0          = 8'd41;  // precomputed value based on UOP_OPR_Z_INV
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE1          = 8'd42;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE2          = 8'd43;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE3          = 8'd44;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE4          = 8'd45;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE5          = 8'd46;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE6          = 8'd47;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE7          = 8'd48;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_A_INV             = 8'd49;  // intermediate results during inversion
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_OUT           = 8'd50;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qx_MONT           = 8'd51;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qy_MONT           = 8'd52;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_P1_X_MONT         = 8'd53;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_P1_Y_MONT         = 8'd54;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_P1_Z_MONT         = 8'd55;

//PM command listing
localparam [2 : 0] KEYGEN_CMD           = 3'b001;
localparam [2 : 0] SIGN_CMD             = 3'b010;
localparam [2 : 0] VER_PART0_CMD        = 3'b100;    
localparam [2 : 0] VER_PART1_CMD        = 3'b101;    
localparam [2 : 0] VER_PART2_CMD        = 3'b110;    

//PM Subroutine listing
localparam NOP                  = 0;
localparam PM_INIT_G_S          = 2;               // R1 INIT with G
localparam PM_INIT_G_E          = PM_INIT_G_S + 5;
localparam PM_INIT_S            = PM_INIT_G_E + 2; // R0 INIT with O
localparam PM_INIT_E            = PM_INIT_S + 9;
localparam PA_S                 = PM_INIT_E + 2;   // Point Addition
localparam PA_E                 = PA_S + 79;
localparam PD_S                 = PA_E + 2;        // Point Doubling
localparam PD_E                 = PD_S + 83;
localparam INV_S                = PD_E + 2;        // Inversion mod p
localparam INV_E                = INV_S + 1039;
localparam CONV_S               = INV_E + 2;       // PM result conversion from projective Mont (X,Y,Z) to affine normanl (x,y)
localparam CONV_E               = CONV_S + 11;

localparam SIGN0_S              = CONV_E + 2;     // signing proof r part0
localparam SIGN0_E              = SIGN0_S + 17;
localparam INVq_S               = SIGN0_E + 2;    // Inversion mod q
localparam INVq_E               = INVq_S + 1043;
localparam SIGN1_S              = INVq_E + 2;     // signing proof r part1
localparam SIGN1_E              = SIGN1_S + 7;

localparam VER0_P0_S            = SIGN1_E + 2;    // verifying0 part0 to convert inputs to Mont domain
localparam VER0_P0_E            = VER0_P0_S + 9;
localparam VER0_P1_S            = VER0_P0_E + 2;  // verifying0 part1 to compute (h*s_inv) and (r*s_inv)
localparam VER0_P1_E            = VER0_P1_S + 11;
localparam VER1_ST_S            = VER0_P1_E + 2;  // verifying1 store ver1 result (h*s_inv)*G
localparam VER1_ST_E            = VER1_ST_S + 5;
localparam PM_INIT_PK_S         = VER1_ST_E + 2;  // verifying2 R1 INIT with PK
localparam PM_INIT_PK_E         = PM_INIT_PK_S + 5;
localparam VER2_PA_S            = PM_INIT_PK_E + 2;  // verifying2 point addtion of PA((h*s_inv)*G, (r*s_inv)*PK)
localparam VER2_PA_E            = VER2_PA_S + 81;