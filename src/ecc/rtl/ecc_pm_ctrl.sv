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
    input  wire                             digit_pk_i,
    input  wire                             digit_neg_i,
    input  wire                             digit_pk_neg_i,
    output pm_instr_struct_t                instr_o,
    output logic                            req_digit_o,
    input  wire                             mult_ready_i,
    input  wire                             mult_start_i,
    output wire                             busy_o
);


    //----------------------------------------------------------------
    // Internal constant and parameter definitions.
    //----------------------------------------------------------------
    // Geometry reference for the legacy formal model, not a controller stall.
    localparam [7 : 0] MULT_DELAY = 3 * ((REG_SIZE + ecc_params_pkg::MULT_RADIX - 1) /
                                       ecc_params_pkg::MULT_RADIX + 1);
    localparam [7 : 0] ADD_DELAY           = 8'd1;  // 2 -1;
    
    localparam [9 : 0] Secp384_SCA_MONT_COUNT   = REG_SIZE[9 : 0] + RND_SIZE[9 : 0];
    localparam [9 : 0] Secp384_MONT_COUNT       = REG_SIZE[9 : 0];
    localparam [9 : 0] Secp384_JSF_MONT_COUNT   = REG_SIZE[9 : 0] + 10'd1;
    
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
    logic [PROG_ADDR_W-1 : 0] prog_instr_addr;
    logic [PROG_ADDR_W-1 : 0] prog_instr_pipe1_addr;
    logic [PROG_ADDR_W-1 : 0] prog_instr_pipe2_addr;
    logic [PROG_ADDR_W-1 : 0] issued_addr;
    logic issued_valid;
    logic instruction_consumed;
    logic instruction_issue;
    logic pipeline_wait;
    logic mult_busy;
    logic mult_launch_pending;
    logic mult_issue_wait;
    logic mult_pending;
    logic mult_store_issue;
    
    logic [3 : 0]  ecc_cmd_reg;

    logic stalled, stalled_pipe1;
    logic stall_flag;
    logic add_issue;
    logic mult_issue;
    logic add_store_wait;
    logic add_pipe_store_wait;
    logic [7 : 0] add_retire_cntr;
    logic mult_pipe_store_wait;
    logic mont_ladder;
    logic shamir_digit_g;
    logic shamir_digit_pk;
    logic shamir_digit_g_neg;
    logic shamir_digit_pk_neg;
    logic shamir_addend_neg;
    logic shamir_add_pk_pending;
    logic shamir_add_pk_pending_neg;
    logic shamir_precompute_active;
    logic shamir_precompute_pk_done;
    logic shamir_precompute_gminus;
    logic                              add_store_ready;
    logic                              mult_pipe_store_ready;

    function automatic [OPR_ADDR_WIDTH-1 : 0] map_shamir_addr(
        input [OPR_ADDR_WIDTH-1 : 0] addr,
        input logic                  digit_g,
        input logic                  digit_pk
    );
        unique case (addr)
            UOP_OPR_SEL_G_X  : map_shamir_addr = digit_g  ? UOP_OPR_CONST_GX_MONT  : UOP_OPR_CONST_ZERO;
            UOP_OPR_SEL_G_Y  : map_shamir_addr = digit_g  ? UOP_OPR_CONST_GY_MONT  : UOP_OPR_CONST_ONE_MONT;
            UOP_OPR_SEL_G_Z  : map_shamir_addr = digit_g  ? UOP_OPR_CONST_ONE_MONT : UOP_OPR_CONST_ZERO;
            UOP_OPR_SEL_PK_X : map_shamir_addr = digit_pk ? UOP_OPR_Qx_AFFN        : UOP_OPR_CONST_ZERO;
            UOP_OPR_SEL_PK_Y : map_shamir_addr = digit_pk ? UOP_OPR_Qy_AFFN        : UOP_OPR_CONST_ONE;
            UOP_OPR_SEL_PK_Z : map_shamir_addr = digit_pk ? UOP_OPR_CONST_ONE_MONT : UOP_OPR_CONST_ZERO;
            default          : map_shamir_addr = addr;
        endcase
    endfunction
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
        .ena(!pipeline_wait),
        .addra(prog_addr),
        .douta(prog_instr)
    );

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            prog_instr_addr <= '0;
        else if (zeroize)
            prog_instr_addr <= '0;
        else if (!pipeline_wait)
            prog_instr_addr <= prog_addr;
    end
    
    always_ff @(posedge clk or negedge reset_n) 
    begin : ff_stalled_reg
        if(!reset_n) 
            stalled_pipe1 <= '0;
        else if (zeroize) 
            stalled_pipe1 <= '0;
        else if (!pipeline_wait)
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
            issued_addr <= '0;
            issued_valid <= 1'b0;
            mult_busy <= 1'b0;
            mult_launch_pending <= 1'b0;
            mult_pending <= 1'b0;
            add_retire_cntr <= '0;
            stalled     <= '0;
            req_digit_o <= '0;
            mont_ladder <= '0;
            ecc_cmd_reg <= '0;
            shamir_digit_g <= '0;
            shamir_digit_pk <= '0;
            shamir_digit_g_neg <= '0;
            shamir_digit_pk_neg <= '0;
            shamir_addend_neg <= '0;
            shamir_add_pk_pending <= '0;
            shamir_add_pk_pending_neg <= '0;
            shamir_precompute_active <= '0;
            shamir_precompute_pk_done <= '0;
            shamir_precompute_gminus <= '0;
        end
        else if (zeroize) begin
            prog_cntr   <= '0;
            mont_cntr   <= '0;
            stall_cntr  <= '0;
            issued_addr <= '0;
            issued_valid <= 1'b0;
            mult_busy <= 1'b0;
            mult_launch_pending <= 1'b0;
            mult_pending <= 1'b0;
            add_retire_cntr <= '0;
            stalled     <= '0;
            req_digit_o <= '0;
            mont_ladder <= '0;
            ecc_cmd_reg <= '0;
            shamir_digit_g <= '0;
            shamir_digit_pk <= '0;
            shamir_digit_g_neg <= '0;
            shamir_digit_pk_neg <= '0;
            shamir_addend_neg <= '0;
            shamir_add_pk_pending <= '0;
            shamir_add_pk_pending_neg <= '0;
            shamir_precompute_active <= '0;
            shamir_precompute_pk_done <= '0;
            shamir_precompute_gminus <= '0;
        end
        else begin
            if (instruction_issue) begin
                issued_addr <= prog_instr_pipe2_addr;
                issued_valid <= 1'b1;
            end
            if (mult_issue) begin
                mult_busy <= 1'b1;
            end
            else if (mult_ready_i && !mult_launch_pending)
                mult_busy <= 1'b0;
            if (mult_issue)
                mult_launch_pending <= 1'b1;
            else if (mult_start_i)
                mult_launch_pending <= 1'b0;
            // One multiply owns the live result until its in-order store issues.
            if (mult_issue)
                mult_pending <= 1'b1;
            else if (mult_store_issue)
                mult_pending <= 1'b0;

            if (add_issue)
                add_retire_cntr <= ADD_DELAY;
            else if (add_retire_cntr != '0)
                add_retire_cntr <= add_retire_cntr - 1'b1;

            if (pipeline_wait) begin
                // Freeze the decoded-stall pipeline along with its instructions.
                // Functional-unit retirement above must continue to release it.
            end
            else if (stalled & (stall_cntr > 0)) begin
                stall_cntr <= stall_cntr - 1;
            end
            else if (stalled & prog_instr.opcode.add_we & add_store_wait) begin
                stalled    <= 1'b1;
                stall_cntr <= '0;
            end
            else if (stall_flag & (!stalled) & (!stalled_pipe1)) begin
                unique case (prog_instr.opcode)
                    UOP_DO_ADD_p :  begin stalled <= 1'b1; stall_cntr <= ADD_DELAY; end  // ADD
                    UOP_DO_SUB_p :  begin stalled <= 1'b1; stall_cntr <= ADD_DELAY; end  // SUB
                    UOP_DO_MUL_p,
                    UOP_DO_MUL_p_red,
                    UOP_DO_MUL_SHADOW_p,
                    UOP_DO_MUL_q : begin stalled <= 1'b1; stall_cntr <= ADD_DELAY; end
                    UOP_DO_ADD_q :  begin stalled <= 1'b1; stall_cntr <= ADD_DELAY; end  // ADD
                    UOP_DO_SUB_q :  begin stalled <= 1'b1; stall_cntr <= ADD_DELAY; end  // SUB
                    UOP_ST_ADD_p,
                    UOP_ST_ADD_q :  begin stalled <= 1'b1; stall_cntr <= '0; end
                    UOP_ST_MUL_p,
                    UOP_ST_MUL_q :  begin stalled <= 1'b1; stall_cntr <= '0; end
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

                            VER_PART2_CMD : begin  // verifying part2: public double-scalar loop
                                mont_cntr <= Secp384_JSF_MONT_COUNT;
                                shamir_precompute_active <= 1'b1;
                                shamir_precompute_pk_done <= 1'b0;
                                shamir_precompute_gminus <= 1'b0;
                                prog_cntr <= PM_INIT_S;
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
                        if (ecc_cmd_reg == VER_PART2_CMD) begin
                            req_digit_o <= 0;
                            mont_ladder <= 0;
                            shamir_add_pk_pending <= 1'b0;
                            shamir_add_pk_pending_neg <= 1'b0;
                            shamir_addend_neg <= 1'b0;
                            if (shamir_precompute_active) begin
                                shamir_digit_g <= 1'b1;
                                shamir_digit_pk <= 1'b0;
                                shamir_digit_g_neg <= 1'b0;
                                shamir_digit_pk_neg <= 1'b0;
                                shamir_precompute_pk_done <= 1'b0;
                                prog_cntr <= VER_LOAD_G_S;
                            end
                            else begin
                                mont_cntr <= mont_cntr - 1;
                                req_digit_o <= 1;
                                prog_cntr <= PD_S;
                            end
                        end
                        else begin
                            mont_cntr <= mont_cntr - 1;
                            req_digit_o <= 1;
                            prog_cntr <= PA_S;
                            mont_ladder <= 1;
                        end
                    end
                                        
                    PA_S,
                    PA_S + 1 : begin // Clear the digit request even when PA's MUL was prefetched.
                        req_digit_o <= 0;
                        prog_cntr <= prog_cntr + 1;
                    end

                    PD_S : begin //Start of point doubling
                        req_digit_o <= 0;
                        prog_cntr <= prog_cntr + 1;
                    end
                    
                    PA_E : begin //End of point addtion
                        // Skip the PD multiply scheduled in PA's tail.
                        prog_cntr <= PD_S + 1;
                    end

                    PD_S + 77 : begin
                        if (mont_ladder && (mont_cntr != 0) &&
                            (ecc_cmd_reg inside {KEYGEN_CMD, SIGN_CMD, DH_SHARED_CMD}))
                            prog_cntr <= PD_PA_S;
                        else
                            prog_cntr <= prog_cntr + 1;
                    end

                    PD_PA_E : begin
                        mont_cntr <= mont_cntr - 1;
                        req_digit_o <= 1;
                        prog_cntr <= PA_S + 1;
                    end
                    
                    PD_E : begin //End of point doubling
                        if (ecc_cmd_reg == VER_PART2_CMD) begin
                            req_digit_o <= 0;
                            shamir_digit_g <= digit_i;
                            shamir_digit_pk <= digit_pk_i;
                            shamir_digit_g_neg <= digit_neg_i;
                            shamir_digit_pk_neg <= digit_pk_neg_i;
                            if (digit_i & digit_pk_i & (digit_neg_i == digit_pk_neg_i)) begin
                                shamir_add_pk_pending <= 1'b0;
                                shamir_add_pk_pending_neg <= 1'b0;
                                shamir_addend_neg <= digit_neg_i;
                                prog_cntr <= VER_LOAD_GPK_S;
                            end
                            else if (digit_i & digit_pk_i) begin
                                shamir_add_pk_pending <= 1'b0;
                                shamir_add_pk_pending_neg <= 1'b0;
                                shamir_addend_neg <= digit_neg_i;
                                prog_cntr <= VER_LOAD_GMK_S;
                            end
                            else if (digit_i) begin
                                shamir_add_pk_pending <= digit_pk_i;
                                shamir_add_pk_pending_neg <= digit_pk_neg_i;
                                shamir_addend_neg <= digit_neg_i;
                                prog_cntr <= VER_LOAD_G_S;
                            end
                            else if (digit_pk_i) begin
                                shamir_add_pk_pending <= 1'b0;
                                shamir_add_pk_pending_neg <= 1'b0;
                                shamir_addend_neg <= digit_pk_neg_i;
                                prog_cntr <= VER_LOAD_PK_S;
                            end
                            else if (mont_cntr == 0) begin
                                shamir_add_pk_pending <= 1'b0;
                                shamir_add_pk_pending_neg <= 1'b0;
                                shamir_addend_neg <= 1'b0;
                                prog_cntr <= CONV_X_S;
                            end
                            else begin
                                shamir_add_pk_pending <= 1'b0;
                                shamir_add_pk_pending_neg <= 1'b0;
                                shamir_addend_neg <= 1'b0;
                                mont_cntr <= mont_cntr - 1;
                                req_digit_o <= 1;
                                prog_cntr <= PD_S;
                            end
                        end
                        else if (mont_cntr == 0) begin // Montgomery ladder is done
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
                        unique case (ecc_cmd_reg)
                            VER_PART2_CMD : prog_cntr <= CONV_X_S;
                            default       : prog_cntr <= CONV_S;
                        endcase
                    end
                    
                    CONV_E : begin // End of conversion from projective Mont (X,Y,Z) to affine normanl (x,y)
                        unique case (ecc_cmd_reg)
                            SIGN_CMD : prog_cntr <= SIGN0_S;
                            default  : prog_cntr <= NOP;
                        endcase
                    end

                    CONV_X_E : begin
                        prog_cntr <= NOP;
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
                        if (ecc_cmd_reg == VER_PART2_CMD) begin
                            if (shamir_precompute_active & !shamir_precompute_pk_done) begin
                                shamir_precompute_pk_done <= 1'b1;
                                shamir_digit_g <= 1'b0;
                                shamir_digit_pk <= 1'b1;
                                shamir_digit_g_neg <= 1'b0;
                                shamir_digit_pk_neg <= 1'b0;
                                shamir_addend_neg <= shamir_precompute_gminus;
                                prog_cntr <= VER_LOAD_PK_S;
                            end
                            else if (shamir_precompute_active & !shamir_precompute_gminus) begin
                                shamir_addend_neg <= 1'b0;
                                prog_cntr <= VER_STORE_GPK_S;
                            end
                            else if (shamir_precompute_active) begin
                                shamir_addend_neg <= 1'b0;
                                prog_cntr <= VER_STORE_GMK_S;
                            end
                            else if (shamir_add_pk_pending) begin
                                shamir_add_pk_pending <= 1'b0;
                                shamir_addend_neg <= shamir_add_pk_pending_neg;
                                prog_cntr <= VER_LOAD_PK_S;
                            end
                            else if (mont_cntr == 0) begin
                                prog_cntr <= CONV_X_S;
                            end
                            else begin
                                mont_cntr <= mont_cntr - 1;
                                req_digit_o <= 1;
                                prog_cntr <= PD_S;
                            end
                        end
                        else begin
                            prog_cntr <= CONV_X_S;
                        end
                    end

                    VER_LOAD_G_E,
                    VER_LOAD_PK_E,
                    VER_LOAD_GPK_E,
                    VER_LOAD_GMK_E : begin
                        prog_cntr <= shamir_addend_neg ? VER_NEG_P1_S : VER2_PA_S;
                    end

                    VER_NEG_P1_E : begin
                        shamir_addend_neg <= 1'b0;
                        prog_cntr <= VER2_PA_S;
                    end

                    VER_STORE_GPK_E : begin
                        shamir_precompute_gminus <= 1'b1;
                        shamir_precompute_pk_done <= 1'b0;
                        prog_cntr <= PM_INIT_S;
                    end

                    VER_STORE_GMK_E : begin
                        shamir_precompute_active <= 1'b0;
                        shamir_precompute_pk_done <= 1'b0;
                        shamir_precompute_gminus <= 1'b0;
                        prog_cntr <= PM_INIT_S;
                    end

                    PM_INIT_G_S,
                    PM_INIT_PK_S,
                    PM_INIT_S,
                    INV_S,
                    INVq_S,
                    CONV_S,
                    CONV_X_S,
                    SIGN0_S,
                    SIGN1_S,
                    VER0_P0_S,
                    VER0_P1_S,
                    VER1_ST_S,
                    VER2_PA_S,
                    VER_LOAD_G_S,
                    VER_LOAD_PK_S,
                    VER_LOAD_GPK_S,
                    VER_LOAD_GMK_S,
                    VER_NEG_P1_S,
                    VER_STORE_GPK_S,
                    VER_STORE_GMK_S,
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
        if (!reset_n) begin
            prog_instr_pipe1 <= '{UOP_NOP, '0, '0};
            prog_instr_pipe1_addr <= '0;
        end
        else if (zeroize) begin
            prog_instr_pipe1 <= '{UOP_NOP, '0, '0};
            prog_instr_pipe1_addr <= '0;
        end
        else begin
            if (stalled_pipe1 || pipeline_wait)
                prog_instr_pipe1 <= prog_instr_pipe1;
            else begin
                prog_instr_pipe1 <= prog_instr;
                prog_instr_pipe1_addr <= prog_instr_addr;
            end
        end
    end // sequencer_pipeline1

    always_ff @(posedge clk or negedge reset_n) 
    begin : sequencer_pipeline2
        if (!reset_n) begin
            prog_instr_pipe2 <= '{UOP_NOP, '0, '0};
            prog_instr_pipe2_addr <= '0;
        end
        else if (zeroize) begin
            prog_instr_pipe2 <= '{UOP_NOP, '0, '0};
            prog_instr_pipe2_addr <= '0;
        end
        else begin
            // A retired MUL store can drain pipe2 despite a held fetch-stall phase.
            // Real backpressure and the once-only issue guard remain authoritative.
            if (pipeline_wait || (stalled_pipe1 && !mult_store_issue))
                prog_instr_pipe2 <= prog_instr_pipe2;
            else begin
                prog_instr_pipe2 <= prog_instr_pipe1;
                prog_instr_pipe2_addr <= prog_instr_pipe1_addr;
            end
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

    // A frozen pipeline may present one ROM instruction for many cycles.
    assign instruction_consumed = issued_valid & (issued_addr == prog_instr_pipe2_addr);
    assign pipeline_wait = add_pipe_store_wait | mult_pipe_store_wait | mult_issue_wait;
    assign instruction_issue = !instruction_consumed & !pipeline_wait;
    assign mult_issue_wait = prog_instr_pipe2.opcode.mult_en & !instruction_consumed &
                             ((mult_busy & !mult_ready_i) | mult_pending);
    always_comb add_issue = prog_instr_pipe2.opcode.add_en & instruction_issue;
    always_comb mult_issue = prog_instr_pipe2.opcode.mult_en & instruction_issue;
    assign mult_store_issue = prog_instr_pipe2.opcode.mult_we & instruction_issue;
    always_comb add_store_ready = (add_retire_cntr == '0);
    // Only actual completion permits a store. Busy retains completion after
    // the ready pulse; launch qualification excludes a previous result.
    always_comb mult_pipe_store_ready = mult_pending & !mult_launch_pending &
                                       (!mult_busy | mult_ready_i);
    always_comb add_store_wait = prog_instr.opcode.add_we & !add_store_ready;
    always_comb add_pipe_store_wait = prog_instr_pipe2.opcode.add_we & !instruction_consumed & !add_store_ready;
    always_comb mult_pipe_store_wait = prog_instr_pipe2.opcode.mult_we & !instruction_consumed & !mult_pipe_store_ready;
    always_comb stall_flag = (prog_instr.opcode.add_en || prog_instr.opcode.mult_en || add_store_wait);
     

    //Instruction out to arithmetic units and memory
    always_ff @(posedge clk or negedge reset_n) 
    begin : instruction_out
        if (!reset_n) begin
            instr_o <= '{UOP_NOP, '0, '0};
        end
        else if (zeroize) begin
            instr_o <= '{UOP_NOP, '0, '0};
        end
        else if (!instruction_issue) begin
            // Preserve operands and modulus through RAM/FAU input capture.
            instr_o.opcode.add_en <= 1'b0;
            instr_o.opcode.mult_en <= 1'b0;
            instr_o.opcode.add_we <= 1'b0;
            instr_o.opcode.mult_we <= 1'b0;
        end
        else begin
            instr_o.opcode <= prog_instr_pipe2.opcode;
            
            if (mont_ladder) begin
                // constant-time conditional swaps depending on the value of the currently processed bit of secret key

                //Addr A for ADD/SUB result
                if (prog_instr_pipe2.opa_addr[3 +: OPR_ADDR_WIDTH-3] == 3'b001)
                    instr_o.opa_addr  <= {prog_instr_pipe2.opa_addr[3 +: OPR_ADDR_WIDTH-3], digit_i ^ prog_instr_pipe2.opa_addr[2], prog_instr_pipe2.opa_addr[1 : 0]};
                else
                    instr_o.opa_addr  <= map_shamir_addr(prog_instr_pipe2.opa_addr, shamir_digit_g, shamir_digit_pk);
                //Addr B for MULT result  
                if (prog_instr_pipe2.opb_addr[3 +: OPR_ADDR_WIDTH-3] == 3'b001)
                    instr_o.opb_addr  <= {prog_instr_pipe2.opb_addr[3 +: OPR_ADDR_WIDTH-3], digit_i ^ prog_instr_pipe2.opb_addr[2], prog_instr_pipe2.opb_addr[1 : 0]};
                else
                    instr_o.opb_addr  <= map_shamir_addr(prog_instr_pipe2.opb_addr, shamir_digit_g, shamir_digit_pk);
            end
            else begin
                instr_o.opa_addr  <= map_shamir_addr(prog_instr_pipe2.opa_addr, shamir_digit_g, shamir_digit_pk);
                instr_o.opb_addr  <= map_shamir_addr(prog_instr_pipe2.opb_addr, shamir_digit_g, shamir_digit_pk);
            end 
        end
    end // instruction_out

    assign busy_o = ~(prog_cntr == NOP);

endmodule
