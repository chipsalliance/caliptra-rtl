//======================================================================
//
// ecc_ctrl.sv
// --------
// ECC controller for the .
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module ecc_ctrl (
    // Clock and reset.
    input  wire           clk,
    input  wire           reset_n,

    // from SLAVES PORT
    input  wire  [2  :   0] ecc_cmd_i,
    input  wire             digit_i,
    output reg [23   : 0] instr_o,
    output reg            req_digit_o,
    output wire             busy_o
);


    //----------------------------------------------------------------
    // Internal constant and parameter definitions.
    //----------------------------------------------------------------
    //begin
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
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_CPY_A2B               = 8'b0010_0001;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_MUL                = 8'b0001_0000;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_ST_MUL                = 8'b0000_0001;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_ADD                = 8'b0000_1000;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_DO_SUB                = 8'b0000_1100;
localparam [UOP_ADDR_WIDTH-1 : 0] UOP_ST_ADD                = 8'b0000_0010;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_DONTCARE          = 8'dX;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ZERO        = 8'd00;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ONE         = 8'd01;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_E_a         = 8'd02;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_ONE_MONT    = 8'd03;  // Mont_mult(1, R2)


localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_GX_MONT     = 8'd04;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_GY_MONT     = 8'd05;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_GZ_MONT     = 8'd06;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R0_X              = 8'd08;  // 8'b0000_1000;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R0_Y              = 8'd09;  // 8'b0000_1001;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R0_Z              = 8'd10;  // 8'b0000_1010;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R1_X              = 8'd12;  // 8'b0000_1100;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R1_Y              = 8'd13;  // 8'b0000_1101;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_R1_Z              = 8'd14;  // 8'b0000_1110;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_Qx_AFFN     = 8'd16;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_CONST_Qy_AFFN     = 8'd17;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_A                 = 8'd22;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_B                 = 8'd23;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_C                 = 8'd24;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_D                 = 8'd25;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_E                 = 8'd26;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_F                 = 8'd27;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_G                 = 8'd28;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_H                 = 8'd29;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_J                 = 8'd30;

localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_IN            = UOP_OPR_R0_Z;  // operand to be inverted
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE0          = UOP_OPR_CONST_ONE_MONT;  // precomputed value based on UOP_OPR_Z_INV
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE1          = 8'd32;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE2          = 8'd33;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE3          = 8'd34;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE4          = 8'd35;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE5          = 8'd36;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE6          = 8'd37;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_PRE7          = 8'd38;
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_A_INV             = UOP_OPR_A;  // intermediate results during inversion
localparam [OPR_ADDR_WIDTH-1 : 0] UOP_OPR_INV_OUT           = 8'd39;



//Subroutine listing
localparam NOP                  = 0;
localparam PM_INIT_S            = 2;
localparam PM_INIT_E            = PM_INIT_S + 57;

localparam PA_S                 = PM_INIT_E + 2;
localparam PA_E                 = PA_S + 41;
localparam PD_S                 = PA_E + 2;
localparam PD_E                 = PD_S + 51;
localparam INV_S                = PD_E + 2;
localparam INV_E                = INV_S + 1037;
localparam CONV_S               = INV_E + 2;
localparam CONV_E               = CONV_S + 11;
localparam PT_LADDER_INIT_E     = 7000;
localparam PT_LADDER1_S         = 8000;
localparam PT_LADDER2_S         = 9000;

    //end

    localparam PROG_LENGTH         = 2**PROG_ADDR_W;

    localparam MULT_DELAY          = 38;
    localparam ADD_DELAY           = 1 -1;
    
    localparam Secp384_MONT_COUNT  = 384;
    
    //----------------------------------------------------------------
    // ecc
    //----------------------------------------------------------------
    reg  [PROG_ADDR_W-1  : 0] prog_cntr;
    reg  [9 : 0]              mont_cntr;
    reg  [7 : 0]              delay_cntr;   
    reg  [7 : 0]              stall_cntr;
    
    // Program pipeline signals
    wire [PROG_ADDR_W-1 : 0]        prog_addr;
    wire [INSTRUCTION_LENGTH-1 : 0] prog_line;
    reg [INSTRUCTION_LENGTH-1 : 0] prog_line_pipe1;
    reg [INSTRUCTION_LENGTH-1 : 0] prog_line_pipe2;
    
    reg first_round;
    wire busy_s,busy_d1,busy_d2,busy_d3;
    reg busy_r;

    reg stalled, stalled_pipe1;
    reg delayed, delayed_pipe1;
    reg delay_op;
    reg mont_ladder;

    // Program Sequencer
    assign prog_addr = prog_cntr;

    ecc_sequencer #(
        .ADDR_WIDTH(PROG_ADDR_W),
        .DATA_WIDTH(INSTRUCTION_LENGTH)
        )
        i_ecc_sequencer(
        .clka(clk),
        .ena(1'b1),
        .addra(prog_addr),
        .douta(prog_line)
    );
    
    always @(posedge clk or negedge reset_n) begin
        if(!reset_n) begin
            prog_cntr   <= 0;
            mont_cntr   <= 0;
            delay_cntr  <= 0;
            delayed     <= 0;
            stall_cntr  <= 0;
            req_digit_o <= 0;
            first_round <= 0;
            mont_ladder <= 0;
        end
        else begin
            stalled_pipe1 <= stalled;
            delayed_pipe1 <= delayed;
            if (stalled & (stall_cntr > 0)) begin
                req_digit_o <= 0;
                stall_cntr <= stall_cntr - 1;
            end
            else if (prog_line[23] & ~stalled & ~stalled_pipe1) begin //stall counter to prevent more reads from program ROM
                req_digit_o <= 0;
                stalled <= 1;
                stall_cntr <= prog_line[7 : 0];
            end
            
            else if (delayed & (delay_cntr > 0)) begin
                delay_cntr <= delay_cntr - 1;
            end
            else if (delay_op & ~delayed & ~delayed_pipe1) begin
                case (prog_line[16 +: 8])
                    UOP_DO_ADD :  begin delayed <= 1; delay_cntr <= ADD_DELAY; end // ADD
                    UOP_DO_SUB :  begin delayed <= 1; delay_cntr <= ADD_DELAY; end // SUB
                    UOP_DO_MUL :  begin delayed <= 1; delay_cntr <= MULT_DELAY; end // MULT
                    default    :  begin delayed <= 0; delay_cntr <= 0; end
                endcase
            end
            else if ((~delayed | (delayed & ~delay_cntr)) & (~stalled | (stalled & ~stall_cntr))) begin
                stalled <= 0;
                delayed <= 0;
                case (prog_cntr)
		            // Waiting for new valid command    
                    NOP : begin
                        case (ecc_cmd_i)
                            1 : begin  // keygen
                                mont_cntr <= Secp384_MONT_COUNT;
                                prog_cntr <= PM_INIT_S;
                                first_round <= 1;
                            end                                   
                            2 : begin 
                                prog_cntr <= PD_S; // Point Doubling
                                first_round <= 1;
                            end
                            default : 
                                prog_cntr <= NOP;
                        endcase
                        req_digit_o <= 0;
                    end
                    
                    // Montgoemry Ladder
                    PM_INIT_E : begin
                        mont_cntr <= mont_cntr - 1;
                        req_digit_o <= 1;
                        prog_cntr <= PA_S;
                        mont_ladder <= 1;
                    end
                                        
                    PA_S : begin
                        req_digit_o <= 0;
                        prog_cntr <= prog_cntr + 1;
                    end
                    
                    PA_E : begin
                        prog_cntr <= PD_S;
                    end
                    
                    PD_E : begin
                        if (mont_cntr == 0) begin
                            prog_cntr <= INV_S;
                            mont_ladder <= 0;
                        end
                        else begin
                            mont_cntr <= mont_cntr - 1;
                            req_digit_o <= 1;
                            prog_cntr <= PA_S;
                        end
                    end
                    
                    INV_E : begin
                        prog_cntr <= CONV_S;
                    end
                    
                    CONV_E : begin
                        prog_cntr <= NOP;
                    end

                    // DOUBLE POINT MULTIPLICATION
                    
                    PT_LADDER_INIT_E : begin
                        //mont_count <= mont_count - 1;
                        req_digit_o <= 1;
                        case (digit_i)
                            0 : prog_cntr <= PT_LADDER1_S;
                            1 : prog_cntr <= PT_LADDER2_S;
                            default : begin end
                        endcase
                    end

                    default : begin
                        prog_cntr <= prog_cntr + 1;
                    end
                endcase
            end
               
        end
    end

    assign busy_s = (prog_cntr == NOP);

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            prog_line_pipe1 <= 0;
            prog_line_pipe2 <= 0;
            busy_r  <= 0;
        end
        else begin
            if (stalled_pipe1 | delayed_pipe1) begin
                prog_line_pipe1 <= prog_line_pipe1;
                prog_line_pipe2 <= prog_line_pipe2;
            end else begin
                prog_line_pipe1 <= prog_line;
                prog_line_pipe2 <= prog_line_pipe1;
            end
            busy_r  <= busy_s;
        end
    end


    always @* begin
        case (prog_line[16 +: 8])
            UOP_DO_ADD :  delay_op = 1;
            UOP_DO_SUB :  delay_op = 1;
            UOP_DO_MUL :  delay_op = 1;
            default    :  delay_op = 0;
        endcase
    end
     

    //Instruction out to arithmetic units and memory
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            instr_o <= 0;
	    else begin
	        if (prog_line_pipe2[23])
                instr_o <= 0;
	        else begin
                instr_o[23 : 21] <= 0;
                case (prog_line_pipe2[20 : 18])
                    3'b000 :  instr_o[20 : 18] <= 3'b000; // NOP
                    3'b001 :  instr_o[20 : 18] <= 3'b010; // RED
                    3'b010 :  instr_o[20 : 18] <= 3'b000; // ADD
                    3'b011 :  instr_o[20 : 18] <= 3'b001; // SUB
                    3'b100 :  instr_o[20 : 18] <= 3'b100; // MULT
                    default:  instr_o[20 : 18] <= 3'b000;
                endcase

                instr_o[17]      <= prog_line_pipe2[17];        //Mem writeA
                instr_o[16]      <= prog_line_pipe2[16];        //Mem writeB
                if (mont_ladder) begin
                    if (prog_line_pipe2[15 : 11] == 5'b00001)
                        instr_o[15 : 8]  <= {prog_line_pipe2[15 : 11], digit_i ^ prog_line_pipe2[10], prog_line_pipe2[9 : 8]};    //Addr A for ADD/SUB result
                    else
                        instr_o[15 : 8]  <= prog_line_pipe2[15 : 8];    //Addr A for ADD/SUB result
                    if (prog_line_pipe2[7  :  3] == 5'b00001)
                        instr_o[7 : 0]   <= {prog_line_pipe2[7  :  3], digit_i ^ prog_line_pipe2[2], prog_line_pipe2[1  :  0]};    //Addr B for MULT result
                    else
                        instr_o[7 : 0]   <= prog_line_pipe2[7 : 0];     //Addr B for MULT result    
                end
                else begin
                    instr_o[15 : 8]  <= prog_line_pipe2[15 : 8];    //Addr A for ADD/SUB result
                    instr_o[7 : 0]   <= prog_line_pipe2[7 : 0];     //Addr B for MULT result
                end
                
            end
	    end
    end

    assign busy_o = ~(prog_cntr == NOP);

endmodule