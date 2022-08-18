//======================================================================
//
// ecc_uop.sv
// --------
// ECC instructin for the point multiplication.
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

localparam INSTRUCTION_LENGTH       = 24;    // opcode + 2 * operand
localparam PROG_ADDR_W              = 15;

localparam integer UOP_ADDR_WIDTH    = 8;
localparam integer OPR_ADDR_WIDTH    = 8;

localparam [UOP_ADDR_WIDTH-1 : 0] UOP_NOP                   = 8'b0000_0000;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_CPY_A2B               = 8'b0100_0001;

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
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ONE_MONT    = 8'd03;  // Mont_mult(1, R2) % p

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_GX_MONT     = 8'd05;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_GY_MONT     = 8'd06;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_GZ_MONT     = 8'd07;

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

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_SCALAR            = 8'd20;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_PRIVKEY           = 8'd21;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_HASH_MSG          = 8'd22;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ONE_q_MONT  = 8'd28;  // Mont_mult(1, R2) % q
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_q_R2        = 8'd29;

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
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_A_INV             = UOP_OPR_A;  // intermediate results during inversion
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_OUT           = 8'd49;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qx_MONT           = 8'd50;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_Qy_MONT           = UOP_OPR_A;


//Subroutine listing
localparam NOP                  = 0;
localparam PM_INIT_S            = 2;
localparam PM_INIT_E            = PM_INIT_S + 57;

localparam PA_S                 = PM_INIT_E + 2;  // Point Addition
localparam PA_E                 = PA_S + 41;
localparam PD_S                 = PA_E + 2;       // Point Doubling
localparam PD_E                 = PD_S + 51;
localparam INV_S                = PD_E + 2;       // Inversion
localparam INV_E                = INV_S + 1039;
localparam CONV_S               = INV_E + 2;      // PM result conversion from projective Mont (X,Y,Z) to affine normanl (x,y)
localparam CONV_E               = CONV_S + 11;
localparam SIGN_S               = CONV_E + 2;     // signing proof r
localparam SIGN_E               = SIGN_S + 1061;


localparam PT_LADDER_INIT_E     = 7000;
localparam PT_LADDER1_S         = 8000;
localparam PT_LADDER2_S         = 9000;
