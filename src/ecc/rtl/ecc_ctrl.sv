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
    output logic [23   : 0] instr_o,
    output logic            req_digit_o,
    output wire             busy_o
);


    //----------------------------------------------------------------
    // Internal constant and parameter definitions.
    //----------------------------------------------------------------
    `include "ecc_uop.sv"

    localparam PROG_LENGTH         = 2**PROG_ADDR_W;

    localparam MULT_DELAY          = 39 -1;
    localparam ADD_DELAY           = 1  -1;
    
    localparam Secp384_MONT_COUNT  = 384;
    
    //----------------------------------------------------------------
    // ecc
    //----------------------------------------------------------------
    logic  [PROG_ADDR_W-1  : 0] prog_cntr;
    logic  [9 : 0]              mont_cntr;
    logic  [7 : 0]              delay_cntr;   
    logic  [7 : 0]              stall_cntr;
    
    // Program pipeline signals
    logic [PROG_ADDR_W-1 : 0]        prog_addr;
    logic [INSTRUCTION_LENGTH-1 : 0] prog_line;
    logic [INSTRUCTION_LENGTH-1 : 0] prog_line_pipe1;
    logic [INSTRUCTION_LENGTH-1 : 0] prog_line_pipe2;
    
    logic first_round;
    logic start_ecc;
    logic busy_s,busy_r,busy_d1,busy_d2,busy_d3;

    logic stalled, stalled_pipe1;
    logic delayed, delayed_pipe1;
    logic delay_op;
    logic mont_ladder;

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
    
    always_ff @(posedge clk or negedge reset_n) begin
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
                    UOP_DO_ADD_p :  begin delayed <= 1; delay_cntr <= ADD_DELAY; end  // ADD
                    UOP_DO_SUB_p :  begin delayed <= 1; delay_cntr <= ADD_DELAY; end  // SUB
                    UOP_DO_MUL_p :  begin delayed <= 1; delay_cntr <= MULT_DELAY; end // MULT
                    UOP_DO_ADD_q :  begin delayed <= 1; delay_cntr <= ADD_DELAY; end  // ADD
                    UOP_DO_SUB_q :  begin delayed <= 1; delay_cntr <= ADD_DELAY; end  // SUB
                    UOP_DO_MUL_q :  begin delayed <= 1; delay_cntr <= MULT_DELAY; end // MULT
                    default      :  begin delayed <= 0; delay_cntr <= 0; end
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
                            end   

                            2 : begin  // signing
                                mont_cntr <= Secp384_MONT_COUNT;
                                prog_cntr <= PM_INIT_S;
                            end                                   

                            3 : begin  // verifying
                                prog_cntr <= NOP;
                            end
                            default : 
                                prog_cntr <= NOP;
                        endcase
                        req_digit_o <= 0;
                        first_round <= 0;
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
                        case (ecc_cmd_i)
                            1 :       prog_cntr <= NOP; //keygen done
                            2 :       prog_cntr <= SIGN_S;
                            default : prog_cntr <= NOP;
                        endcase
                        first_round <= 1;
                    end

                    SIGN_E : begin
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

    always_ff @(posedge clk or negedge reset_n) begin
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


    always_comb begin
        case (prog_line[16 +: 8])
            UOP_DO_ADD_p :  delay_op = 1;
            UOP_DO_SUB_p :  delay_op = 1;
            UOP_DO_MUL_p :  delay_op = 1;
            UOP_DO_ADD_q :  delay_op = 1;
            UOP_DO_SUB_q :  delay_op = 1;
            UOP_DO_MUL_q :  delay_op = 1;
            default      :  delay_op = 0;
        endcase
    end
     

    //Instruction out to arithmetic units and memory
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            instr_o <= 0;
	    else begin
	        if (prog_line_pipe2[23])
                instr_o <= 0;
	        else begin
                instr_o[23 : 22] <= 0;
                instr_o[21]      <= prog_line_pipe2[21];        //mod_p_q : performing mod_p if (mod_p_q = 0), else mod_q

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
