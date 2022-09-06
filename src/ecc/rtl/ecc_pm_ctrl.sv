//======================================================================
//
// ecc_pm_ctrl.sv
// --------
// ECC point multiplication controller for the Secp384.
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module ecc_pm_ctrl (
    // Clock and reset.
    input  wire           clk,
    input  wire           reset_n,

    // from arith_unit
    input  wire  [2  :   0] ecc_cmd_i,
    input  wire             digit_i,
    output logic [23   : 0] instr_o,
    output logic            req_digit_o,
    output wire             busy_o
);


    //----------------------------------------------------------------
    // Internal constant and parameter definitions.
    //----------------------------------------------------------------
    `include "ecc_pm_uop.sv"

    localparam PROG_LENGTH         = 2**PROG_ADDR_W;

    localparam MULT_DELAY          = 39 -1;
    localparam ADD_DELAY           = 1  -1;
    
    localparam Secp384_MONT_COUNT  = 384;
    
    //----------------------------------------------------------------
    // Registers 
    //----------------------------------------------------------------
    
    logic  [PROG_ADDR_W-1  : 0] prog_cntr;
    logic  [9 : 0]              mont_cntr;
    logic  [7 : 0]              stall_cntr;   
    
    // Program pipeline signals
    logic [PROG_ADDR_W-1 : 0]        prog_addr;
    logic [INSTRUCTION_LENGTH-1 : 0] prog_line;
    logic [INSTRUCTION_LENGTH-1 : 0] prog_line_pipe1;
    logic [INSTRUCTION_LENGTH-1 : 0] prog_line_pipe2;
    
    logic [2 : 0]  ecc_cmd_reg;

    logic stalled, stalled_pipe1;
    logic stall_flag;
    logic mont_ladder;

    //----------------------------------------------------------------
    // pm sequencer fsm
    //----------------------------------------------------------------
    assign prog_addr = prog_cntr;

    ecc_pm_sequencer #(
        .ADDR_WIDTH(PROG_ADDR_W),
        .DATA_WIDTH(INSTRUCTION_LENGTH)
        )
        i_ecc_pm_sequencer(
        .clka(clk),
        .ena(1'b1),
        .addra(prog_addr),
        .douta(prog_line)
    );
    
    always_ff @(posedge clk) 
    begin : pm_fsm
        if(!reset_n) begin
            prog_cntr   <= 0;
            mont_cntr   <= 0;
            stall_cntr  <= 0;
            stalled     <= 0;
            req_digit_o <= 0;
            mont_ladder <= 0;
            ecc_cmd_reg <= 0;
        end
        else begin
            stalled_pipe1 <= stalled;
            if (stalled & (stall_cntr > 0)) begin
                stall_cntr <= stall_cntr - 1;
            end
            else if (stall_flag & ~stalled & ~stalled_pipe1) begin
                case (prog_line[16 +: 8])
                    UOP_DO_ADD_p :  begin stalled <= 1; stall_cntr <= ADD_DELAY; end  // ADD
                    UOP_DO_SUB_p :  begin stalled <= 1; stall_cntr <= ADD_DELAY; end  // SUB
                    UOP_DO_MUL_p :  begin stalled <= 1; stall_cntr <= MULT_DELAY; end // MULT
                    UOP_DO_ADD_q :  begin stalled <= 1; stall_cntr <= ADD_DELAY; end  // ADD
                    UOP_DO_SUB_q :  begin stalled <= 1; stall_cntr <= ADD_DELAY; end  // SUB
                    UOP_DO_MUL_q :  begin stalled <= 1; stall_cntr <= MULT_DELAY; end // MULT
                    default      :  begin stalled <= 0; stall_cntr <= 0; end
                endcase
            end
            else if ((~stalled | (stalled & ~stall_cntr))) begin
                stalled <= 0;
                case (prog_cntr)
		            // Waiting for new valid command    
                    NOP : begin
                        ecc_cmd_reg <= ecc_cmd_i;
                        case (ecc_cmd_i)
                            KEYGEN_CMD : begin  // keygen
                                mont_cntr <= Secp384_MONT_COUNT;
                                prog_cntr <= PM_INIT_G_S;
                            end   

                            SIGN_CMD : begin  // signing
                                mont_cntr <= Secp384_MONT_COUNT;
                                prog_cntr <= PM_INIT_G_S;
                            end                                   

                            VER_PART0_CMD : begin  // verifying part0
                                prog_cntr <= VER0_P0_S;
                            end

                            VER_PART1_CMD : begin  // verifying part1
                                mont_cntr <= Secp384_MONT_COUNT;
                                prog_cntr <= PM_INIT_G_S;
                            end

                            VER_PART2_CMD : begin  // verifying part2
                                prog_cntr <= VER1_ST_S;
                            end

                            default : 
                                prog_cntr <= NOP;
                        endcase
                        req_digit_o <= 0;
                    end
                    
                    VER1_ST_E : begin // Storing the VER1 MONT results before starting VER2
                        mont_cntr <= Secp384_MONT_COUNT;
                        prog_cntr <= PM_INIT_PK_S;
                    end

                    // Montgoemry Ladder
                    PM_INIT_G_E : begin //End of initilize R0 = G
                        prog_cntr <= PM_INIT_S;
                    end

                    PM_INIT_PK_E : begin //End of initilize R0 = PK
                        prog_cntr <= PM_INIT_S;
                    end

                    PM_INIT_E : begin // End of initilaze R1 = PD(R0)
                        mont_cntr <= mont_cntr - 1;
                        req_digit_o <= 1;
                        prog_cntr <= PA_S;
                        mont_ladder <= 1;
                    end
                                        
                    PA_S : begin //Start of point addtion
                        req_digit_o <= 0;
                        prog_cntr <= prog_cntr + 1;
                    end
                    
                    PA_E : begin //End of point addtion
                        prog_cntr <= PD_S;
                    end
                    
                    PD_E : begin //End of point doubling
                        if (mont_cntr == 0) begin // Montgomery ladder is done
                            case (ecc_cmd_reg)
                                VER_PART1_CMD : prog_cntr <= NOP;
                                VER_PART2_CMD : prog_cntr <= VER2_PA_S;
                                default       : prog_cntr <= INV_S;
                            endcase
                            mont_ladder <= 0;
                            req_digit_o <= 0;
                        end
                        else begin
                            mont_cntr <= mont_cntr - 1;
                            req_digit_o <= 1;
                            prog_cntr <= PA_S;
                        end
                    end
                    
                    INV_E : begin // End of inversion mod p
                        prog_cntr <= CONV_S;
                    end
                    
                    CONV_E : begin // End of conversion from projective Mont (X,Y,Z) to affine normanl (x,y)
                        case (ecc_cmd_reg)
                            SIGN_CMD : prog_cntr <= SIGN0_S;
                            default  : prog_cntr <= NOP;
                        endcase
                    end

                    SIGN0_E : begin // End of signing part 0 to to convert inputs to Mont domain & compute (h + r*privKey) 
                        prog_cntr <= INVq_S;
                    end

                    INVq_E : begin // End of inversion mod q
                        case (ecc_cmd_reg)
                            SIGN_CMD      : prog_cntr <= SIGN1_S;
                            VER_PART0_CMD : prog_cntr <= VER0_P1_S;
                            default       : prog_cntr <= NOP;
                        endcase
                    end

                    SIGN1_E : begin // End of signing part 1 to compute s
                        prog_cntr <= NOP;
                    end

                    VER0_P0_E : begin // End of verfying part 0 to convert inputs to Mont domain
                        prog_cntr <= INVq_S;
                    end

                    VER0_P1_E : begin // End of verfying part 1 to compute (h*s_inv) and (r*s_inv)
                        prog_cntr <= NOP;
                    end

                    VER2_PA_E : begin // End of point addition of PA((h*s_inv)*G, (r*s_inv)*PK)
                        prog_cntr <= INV_S;
                    end

                    default : begin
                        prog_cntr <= prog_cntr + 1;
                    end
                endcase
            end
               
        end
    end // pm_fsm

    always_ff @(posedge clk) 
    begin : sequencer_pipeline
        if (!reset_n) begin
            prog_line_pipe1 <= 0;
            prog_line_pipe2 <= 0;
        end
        else begin
            if (stalled_pipe1) begin
                prog_line_pipe1 <= prog_line_pipe1;
                prog_line_pipe2 <= prog_line_pipe2;
            end else begin
                prog_line_pipe1 <= prog_line;
                prog_line_pipe2 <= prog_line_pipe1;
            end
        end
    end // sequencer_pipeline


    always_comb 
    begin : delay_flag
        case (prog_line[16 +: 8])
            UOP_DO_ADD_p :  assign stall_flag = 1;
            UOP_DO_SUB_p :  assign stall_flag = 1;
            UOP_DO_MUL_p :  assign stall_flag = 1;
            UOP_DO_ADD_q :  assign stall_flag = 1;
            UOP_DO_SUB_q :  assign stall_flag = 1;
            UOP_DO_MUL_q :  assign stall_flag = 1;
            default      :  assign stall_flag = 0;
        endcase
    end // delay_flag
     

    //Instruction out to arithmetic units and memory
    always_ff @(posedge clk) 
    begin : instruction_out
        if (!reset_n)
            instr_o <= 0;
	    else begin
            instr_o[23 : 22] <= 0;
            instr_o[21]      <= prog_line_pipe2[21];  // mod_p_q : performing mod_p if (mod_p_q = 0), else mod_q

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
    end // instruction_out

    assign busy_o = ~(prog_cntr == NOP);

endmodule