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
// ecc_pm_ctrl.sv
// --------
// ECC point multiplication controller for the Secp384.
//
// The architecture includes ecc_pm_sequencer including the required 
// sequence to perform:
//   - point multiplication (pm) based on Montgomery ladder and Fermat's little 
//    theorem (FLT) inversion
//   - Montgomery ladder initilization with base point G or public key PK in
//     keygen, signing, or verifying operations.
//   - Montgomery ladder steps: including the iterative point addition (PA)
//     and point doubling (PD) operations in Montgomery domain using projective 
//     coordinates. The number of iteration is equal to REG_SIZE of scalar in 
//     unprotected point multiplication, and REG_SIZE+RND_SIZE of scalar in the 
//     SCA protected operation.
//   - Modular Inversion (mod p, mod q) is based on Fermat's little theorem (FLT) 
//     inversion.
//   - Conversion from projective coordinates in Montgomery domain (X,Y,Z) to 
//     affine coordinates in the normal domain (x,y).
//   - Modular arithmetic operations such as (h + r*privKey) in signing
//     or (h*s_inv) and (r*s_inv) in verifying
//
//
//======================================================================

module ecc_pm_ctrl 
    import ecc_pm_uop_pkg::*;
    #(
    parameter REG_SIZE      = 384,
    parameter RND_SIZE      = 192,
    parameter INSTR_SIZE    = 24
    )
    (
    // Clock and reset.
    input  wire           clk,
    input  wire           reset_n,
    input  wire           zeroize,

    // from arith_unit
    input  wire  [3  :   0]                 ecc_cmd_i,
    input  wire                             digit_i,
    output pm_instr_struct_t                instr_o,
    output logic                            req_digit_o,
    output wire                             busy_o
);


    //----------------------------------------------------------------
    // Internal constant and parameter definitions.
    //----------------------------------------------------------------
    localparam [7 : 0] MULT_DELAY          = 8'd27; //28 -1;
    localparam [7 : 0] ADD_DELAY           = 8'd1;  // 2 -1;
    
    localparam [9 : 0] Secp384_SCA_MONT_COUNT   = REG_SIZE[9 : 0] + RND_SIZE[9 : 0];
    localparam [9 : 0] Secp384_MONT_COUNT       = REG_SIZE[9 : 0];
    
    //----------------------------------------------------------------
    // Registers 
    //----------------------------------------------------------------
    
    logic  [PROG_ADDR_W-1  : 0] prog_cntr;
    logic  [9 : 0]              mont_cntr;
    logic  [7 : 0]              stall_cntr;   
    
    // Program pipeline signals
    logic [PROG_ADDR_W-1 : 0]        prog_addr;
    pm_instr_struct_t prog_instr;
    pm_instr_struct_t prog_instr_pipe1;
    pm_instr_struct_t prog_instr_pipe2;
    
    logic [3 : 0]  ecc_cmd_reg;

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
        .reset_n(reset_n),
        .zeroize(zeroize),
        .ena(1'b1),
        .addra(prog_addr),
        .douta(prog_instr)
    );
    
    always_ff @(posedge clk or negedge reset_n) 
    begin : ff_stalled_reg
        if(!reset_n) 
            stalled_pipe1 <= '0;
        else if (zeroize) 
            stalled_pipe1 <= '0;
        else
            stalled_pipe1 <= stalled;
    end // ff_stalled_reg

    //----------------------------------------------------------------
    // Point_multiplication_FSM_flow
    //
    // This FSM starts with the keyfen/signing/verifying command to 
    // perform different operations.
    // Active low and async reset.
    //----------------------------------------------------------------
    always_ff @(posedge clk or negedge reset_n) 
    begin : pm_fsm
        if(!reset_n) begin
            prog_cntr   <= '0;
            mont_cntr   <= '0;
            stall_cntr  <= '0;
            stalled     <= '0;
            req_digit_o <= '0;
            mont_ladder <= '0;
            ecc_cmd_reg <= '0;
        end
        else if (zeroize) begin
            prog_cntr   <= '0;
            mont_cntr   <= '0;
            stall_cntr  <= '0;
            stalled     <= '0;
            req_digit_o <= '0;
            mont_ladder <= '0;
            ecc_cmd_reg <= '0;
        end
        else begin
            if (stalled & (stall_cntr > 0)) begin
                stall_cntr <= stall_cntr - 1;
            end
            else if (stall_flag & (!stalled) & (!stalled_pipe1)) begin
                unique case (prog_instr.opcode)
                    UOP_DO_ADD_p :  begin stalled <= 1'b1; stall_cntr <= ADD_DELAY; end  // ADD
                    UOP_DO_SUB_p :  begin stalled <= 1'b1; stall_cntr <= ADD_DELAY; end  // SUB
                    UOP_DO_MUL_p :  begin stalled <= 1'b1; stall_cntr <= MULT_DELAY; end // MULT
                    UOP_DO_ADD_q :  begin stalled <= 1'b1; stall_cntr <= ADD_DELAY; end  // ADD
                    UOP_DO_SUB_q :  begin stalled <= 1'b1; stall_cntr <= ADD_DELAY; end  // SUB
                    UOP_DO_MUL_q :  begin stalled <= 1'b1; stall_cntr <= MULT_DELAY; end // MULT
                    default      :  begin stalled <= 1'b0; stall_cntr <= '0; end
                endcase
            end
            else begin
                stalled <= 0;
                unique case (prog_cntr)
                    NOP : begin     // Waiting for new valid command
                        ecc_cmd_reg <= ecc_cmd_i;
                        unique case (ecc_cmd_i)
                            KEYGEN_CMD : begin  // keygen
                                mont_cntr <= Secp384_SCA_MONT_COUNT;
                                prog_cntr <= PM_INIT_G_S;
                            end   

                            SIGN_CMD : begin  // signing
                                mont_cntr <= Secp384_SCA_MONT_COUNT;
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

                            CHK_PK_CMD : begin
                                prog_cntr <= CHK_PK_S;
                            end

                            DH_SHARED_CMD : begin  // DH shared key
                                mont_cntr <= Secp384_SCA_MONT_COUNT;
                                prog_cntr <= PM_INIT_DH_S;
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
                    PM_INIT_G_E : begin //End of initilize R0 = Randomized G
                        prog_cntr <= PM_INIT_S;
                    end

                    PM_INIT_PK_E : begin //End of initilize R0 = PK
                        prog_cntr <= PM_INIT_S;
                    end

                    PM_INIT_DH_E : begin //End of initilize R0 = Randomized PK
                        prog_cntr <= PM_INIT_S;
                    end

                    PM_INIT_E : begin // End of initilaze R1 = 0
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
                            unique case (ecc_cmd_reg)
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
                        unique case (ecc_cmd_reg)
                            SIGN_CMD : prog_cntr <= SIGN0_S;
                            default  : prog_cntr <= NOP;
                        endcase
                    end

                    SIGN0_E : begin // End of signing part 0 to to convert inputs to Mont domain & compute (h + r*privKey) 
                        prog_cntr <= INVq_S;
                    end

                    INVq_E : begin // End of inversion mod q
                        unique case (ecc_cmd_reg)
                            SIGN_CMD      : prog_cntr <= SIGN1_S;
                            VER_PART0_CMD : prog_cntr <= VER0_P1_S;
                            default       : prog_cntr <= NOP;
                        endcase
                    end

                    SIGN1_E : begin // End of signing part 1 to compute s
                        prog_cntr <= NOP;
                    end

                    CHK_PK_E: begin // End of public key validation before verifying process
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

                    PM_INIT_G_S,
                    PM_INIT_PK_S,
                    PM_INIT_S,
                    PD_S,
                    INV_S,
                    INVq_S,
                    CONV_S,
                    SIGN0_S,
                    SIGN1_S,
                    VER0_P0_S,
                    VER0_P1_S,
                    VER1_ST_S,
                    VER2_PA_S,
                    PM_INIT_DH_S: begin
                        prog_cntr <= prog_cntr + 1;
                    end

                    default : begin
                        prog_cntr <= prog_cntr + 1;
                    end
                endcase
            end 
        end
    end // pm_fsm

    always_ff @(posedge clk or negedge reset_n) 
    begin : sequencer_pipeline1
        if (!reset_n) 
            prog_instr_pipe1 <= '{UOP_NOP, '0, '0};
        else if (zeroize) 
            prog_instr_pipe1 <= '{UOP_NOP, '0, '0};
        else begin
            if (stalled_pipe1) 
                prog_instr_pipe1 <= prog_instr_pipe1;
            else 
                prog_instr_pipe1 <= prog_instr;
        end
    end // sequencer_pipeline1

    always_ff @(posedge clk or negedge reset_n) 
    begin : sequencer_pipeline2
        if (!reset_n) 
            prog_instr_pipe2 <= '{UOP_NOP, '0, '0};
        else if (zeroize) 
            prog_instr_pipe2 <= '{UOP_NOP, '0, '0};
        else begin
            if (stalled_pipe1) 
                prog_instr_pipe2 <= prog_instr_pipe2;
            else 
                prog_instr_pipe2 <= prog_instr_pipe1;
        end
    end // sequencer_pipeline2

    /*
    always_comb 
    begin : delay_flag
        unique case (prog_instr.opcode)
            UOP_DO_ADD_p :  stall_flag = 1;
            UOP_DO_SUB_p :  stall_flag = 1;
            UOP_DO_MUL_p :  stall_flag = 1;
            UOP_DO_ADD_q :  stall_flag = 1;
            UOP_DO_SUB_q :  stall_flag = 1;
            UOP_DO_MUL_q :  stall_flag = 1;
            default      :  stall_flag = 0;
        endcase
    end // delay_flag
    */

    always_comb stall_flag = (prog_instr.opcode.add_en || prog_instr.opcode.mult_en);
     

    //Instruction out to arithmetic units and memory
    always_ff @(posedge clk or negedge reset_n) 
    begin : instruction_out
        if (!reset_n)
            instr_o <= '{UOP_NOP, '0, '0};
        else if (zeroize)
            instr_o <= '{UOP_NOP, '0, '0};
        else begin
            instr_o.opcode <= prog_instr_pipe2.opcode;
            
            if (mont_ladder) begin
                // constant-time conditional swaps depending on the value of the currently processed bit of secret key

                //Addr A for ADD/SUB result
                if (prog_instr_pipe2.opa_addr[3 +: OPR_ADDR_WIDTH-3] == 3'b001)
                    instr_o.opa_addr  <= {prog_instr_pipe2.opa_addr[3 +: OPR_ADDR_WIDTH-3], digit_i ^ prog_instr_pipe2.opa_addr[2], prog_instr_pipe2.opa_addr[1 : 0]};
                else
                    instr_o.opa_addr  <= prog_instr_pipe2.opa_addr;
                //Addr B for MULT result  
                if (prog_instr_pipe2.opb_addr[3 +: OPR_ADDR_WIDTH-3] == 3'b001)
                    instr_o.opb_addr  <= {prog_instr_pipe2.opb_addr[3 +: OPR_ADDR_WIDTH-3], digit_i ^ prog_instr_pipe2.opb_addr[2], prog_instr_pipe2.opb_addr[1 : 0]};
                else
                    instr_o.opb_addr  <= prog_instr_pipe2.opb_addr;  
            end
            else begin
                instr_o.opa_addr  <= prog_instr_pipe2.opa_addr;    //Addr A for ADD/SUB result
                instr_o.opb_addr  <= prog_instr_pipe2.opb_addr;    //Addr B for MULT result
            end 
        end
    end // instruction_out

    assign busy_o = ~(prog_cntr == NOP);

endmodule
