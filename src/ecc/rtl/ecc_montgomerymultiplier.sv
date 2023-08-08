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
//  Module:
//      ecc_montgomerymultiplier.sv
//
// Montgomery Multiplier based on 
// Optimized Algorithms and Architectures for Montgomery Multiplication
// for Post-quantum Cryptography by Rami Elkhatib et. al.
//
// Description:
//      The module produces a Montgomery product of input operands with the following contraints:
//          Input operands must be less than n_i, i.e. opa_i < n_i and opb_i < n_i.
//          RADIX > 2
//          R = 2^((ceil($bits(n_i) / RADIX) + 1) * RADIX)
//          R > n_i.
//      (1) T = opa_i * opb_i < n_i * n_i = n_i^2
//      (2) p_internal = (T + (T*n_prime mod R) * n_i) / R
//      (3) p_subtracted_internal = p_internal - n_i       
//      (4) p_o = (p_internal >= ni)? p_subtracted_internal : p_internal
//      From (1) and (2) given R > n_i, and opa_i, opb_i < n_i:
//          p_internal < (n_i^2 + R * n_i) / R = n_i + n_i^2 / R < n_i + n_i^2 / n_i = n_i + n_i = 2*n_i
//      From (3) and (4):
//          p_subtracted_internal < 2*n_i - n_i = n_i
//          p_o < n_i
//======================================================================

module ecc_montgomerymultiplier #(
    parameter REG_SIZE  = 384,
    parameter RADIX     = 32
)
(
    // Clock and reset.
    input  wire                  clk,
    input  wire                  reset_n,
    input  wire                  zeroize,

    // DATA PORT
    input  wire                  start_i,
    input  wire [REG_SIZE-1:0]   opa_i,
    input  wire [REG_SIZE-1:0]   opb_i,
    input  wire [REG_SIZE-1:0]   n_i,
    input  wire [RADIX-1:0]      n_prime_i, // only need the last few bits
    output logic [REG_SIZE-1:0]  p_o,
    output logic                 ready_o
);
    //----------------------------------------------------------------
    // Local Parameters
    //----------------------------------------------------------------
    
    // Equivalent to $ceil(real'(REG_SIZE) / RADIX) + 1;
    localparam  int unsigned S_NUM =  ((REG_SIZE + RADIX - 1) / RADIX) + 1; 
    localparam  int unsigned FULL_REG_SIZE = S_NUM * RADIX;
    // Each PE performs two iterations out of S_NUM - 1
    // See section 4.2 of Elkhatib_2019 paper.
    // PE_UNITS does not include the last PE.
    // The last PE is instantiated separately.
    localparam  PE_UNITS = ((S_NUM - 1) / 2) - 1;
    localparam [(FULL_REG_SIZE-REG_SIZE)-1 : 0]       zero_pad        = '0;

    //----------------------------------------------------------------
    // Registers
    //----------------------------------------------------------------
    logic [RADIX-1 : 0] a_array[0:PE_UNITS+1];
    logic [RADIX-1 : 0] b_array[0:PE_UNITS+1];
    logic [RADIX-1 : 0] p_array[0:PE_UNITS+1];
    logic [RADIX-1 : 0] m_array[0:PE_UNITS];
    logic [RADIX   : 0] c_array[0:PE_UNITS+1];
    logic [RADIX-1 : 0] s_array[0:PE_UNITS+1];
    
    logic [RADIX-1 : 0] p_neg_array[0:2*(PE_UNITS+1)];
    logic [RADIX-1 : 0] t_reg[0:2*(PE_UNITS+1)];
    logic [RADIX-1 : 0] t_subtracted_reg[0:2*(PE_UNITS+1)];
    logic [RADIX   : 0] sub_res[0:2*(PE_UNITS+1)];

    logic               sub_b_i[0:2*(PE_UNITS+1)];
    logic               sub_b_o[0:2*(PE_UNITS+1)];
    
    logic   [FULL_REG_SIZE-1 : 0]     a_reg;  //extended with zero
    logic   [FULL_REG_SIZE-1 : 0]     b_reg;  //extended with zero
    logic   [FULL_REG_SIZE-1 : 0]     p_reg;  //extended with zero
    logic   [FULL_REG_SIZE-1 : 0]     p_neg_reg; //extended with one
    logic   [RADIX-1:0]               n_prime_reg;
    logic   [(3*S_NUM)-1 : 0]         push_reg;
    logic                             push_reg_eq_zero;
    logic                             push_reg_eq_zero_ff;
    logic                             odd;
    logic   [RADIX-1 : 0]             last_s_reg;
    logic   [FULL_REG_SIZE-1:0]       p_internal;
    logic   [FULL_REG_SIZE-1:0]       p_subtracted_internal;
    logic                             last_reduction;

    //----------------------------------------------------------------
    // Processing elements (PEs)
    //----------------------------------------------------------------    
    ecc_pe_first #(
        .RADIX(RADIX)
        )
        first_box
        (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .start_in(start_i),
        .a_in(a_array[0]),
        .b_in(b_array[0]),
        .p_in(p_array[0]),
        .s_in(s_array[0]),
        .n_prime_in(n_prime_reg),
        .odd(odd),

        .a_out(a_array[1]),
        .m_out(m_array[0]),
        .c_out(c_array[0])
        );

    genvar i0;
    generate 
        for (i0=0; i0 < PE_UNITS; i0++) begin : gen_PE //PE general boxes
            ecc_pe #(
                .RADIX(RADIX)
                )
                box_i
                (
                .clk(clk),
                .reset_n(reset_n),
                .zeroize(zeroize),
                .start_in(start_i),
                .a_in(a_array[i0+1]),
                .b_in(b_array[i0+1]),
                .p_in(p_array[i0+1]),
                .m_in(m_array[i0]),
                .s_in(s_array[i0+1]),
                .c_in(c_array[i0]),
                .odd(odd),

                .a_out(a_array[i0+2]),
                .m_out(m_array[i0+1]),
                .s_out(s_array[i0]),
                .c_out(c_array[i0+1])
                );
        end
    endgenerate

    ecc_pe_final #(
        .RADIX(RADIX)
        )
        final_box
        (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .start_in(start_i),
        .a_in(a_array[PE_UNITS+1]),
        .b_in(b_array[PE_UNITS+1]),
        .p_in(p_array[PE_UNITS+1]),
        .m_in(m_array[PE_UNITS]),
        .s_in(s_array[PE_UNITS+1]),
        .c_in(c_array[PE_UNITS]),
        .odd(odd),

        .s_out(s_array[PE_UNITS]),
        .c_out(c_array[PE_UNITS+1])
        );
    
    // Determines the input s for the final PE
    assign s_array[PE_UNITS+1] = last_s_reg;
    always_ff @(posedge clk or negedge reset_n) 
    begin
        if (~reset_n)
            last_s_reg <= 'b0;
        else if (zeroize)
            last_s_reg <= 'b0;
        else if (start_i)
            last_s_reg <= 'b0;
        else
            last_s_reg <= c_array[PE_UNITS+1][RADIX-1:0];
    end

    // Set odd flag
    always_ff @(posedge clk or negedge reset_n) 
    begin
        if (~reset_n)
            odd <= 0;
        else if (zeroize)
            odd <= 0;
        else if (start_i)
            odd <= 1'b1;
        else
            odd <= ~odd;
    end

    always_ff @(posedge clk or negedge reset_n) 
    begin : input_reg
        if (~reset_n) begin
            a_reg <= 'b0;
            b_reg <= 'b0;
            p_reg <= 'b0;
            n_prime_reg <= 'b0;
        end
        else if (zeroize) begin
            a_reg <= 'b0;
            b_reg <= 'b0;
            p_reg <= 'b0;
            n_prime_reg <= 'b0;
        end
        else if (start_i) begin
            a_reg <= {zero_pad, opa_i};
            b_reg <= {zero_pad, opb_i};
            p_reg <= {zero_pad, n_i};
            n_prime_reg <= n_prime_i;
        end else begin
            if (odd) begin
                a_reg[(FULL_REG_SIZE-RADIX)-1 : 0] <= a_reg[FULL_REG_SIZE-1 : RADIX];
                a_reg[FULL_REG_SIZE-1 : FULL_REG_SIZE-RADIX] <= 'b0; //Shift 
            end 
        end
    end // input_reg

    assign a_array[0] = a_reg[RADIX-1 : 0];

    // Determines which b and p is pushed through the system
    assign b_array[0] = b_reg[RADIX-1 : 0];
    assign p_array[0] = p_reg[RADIX-1 : 0];
    genvar j0;
    generate 
        for (j0=1; j0 < (PE_UNITS+2); j0++) begin : gen_b_p_array
            assign b_array[j0] = odd ? b_reg[(((2*j0)+1)*RADIX)-1 : (2*j0)*RADIX] : b_reg[((2*j0)*RADIX)-1 : ((2*j0)-1)*RADIX];
            assign p_array[j0] = odd ? p_reg[(((2*j0)+1)*RADIX)-1 : (2*j0)*RADIX] : p_reg[((2*j0)*RADIX)-1 : ((2*j0)-1)*RADIX];
        end
    endgenerate


    assign p_neg_reg = ~p_reg;
    
    genvar i1;
    generate 
        for (i1=0; i1 < ((2*(PE_UNITS+1))+1); i1++) begin : gen_n_neg_array
            assign p_neg_array[i1] = p_neg_reg[i1*RADIX +: RADIX];
        end
    endgenerate

    // Storing the partial results from the system
    genvar t0;
    generate 
        for (t0=0; t0 < ((2*(PE_UNITS+1))+1); t0++) begin : gen_t_reg
            if ((t0 == 0) | (t0 == 1)) begin
                always_ff @(posedge clk or negedge reset_n) begin
                    if (~reset_n)
                        t_reg[t0] <= '0;
                    else if (zeroize)
                        t_reg[t0] <= '0;
                    else if (push_reg[(2*(PE_UNITS+1)) - t0])
                        t_reg[t0] <= s_array[0];
                    else
                        t_reg[t0] <= t_reg[t0];
                end
            end
            else begin
                localparam int t0_WIDTH  = $clog2((2*(PE_UNITS+1))+1);
                localparam bit [t0_WIDTH-1:0] t0_unsigned = t0[t0_WIDTH-1:0];
                always_ff @(posedge clk or negedge reset_n) begin
                    if (~reset_n)
                        t_reg[t0] <= '0;
                    else if (zeroize)
                        t_reg[t0] <= '0;
                    else if (push_reg[(2*(PE_UNITS+1)) - t0])
                        t_reg[t0] <= s_array[t0_unsigned >> 1];
                    else
                        t_reg[t0] <= t_reg[t0];
                end
            end
        end // gen_t_reg
    endgenerate

    genvar t1;
    generate 
        for (t1=0; t1 < ((2*(PE_UNITS+1))+1); t1++) begin : gen_sub_t
            if (t1 == 0)
                always_comb sub_b_i[t1] = 1;
            else
                always_comb sub_b_i[t1] = sub_b_o[t1 - 1];
            
            always_ff @(posedge clk or negedge reset_n) begin
                if (~reset_n)
                    sub_b_o[t1] <= '0;
                else if (zeroize)
                    sub_b_o[t1] <= '0;
                else
                    sub_b_o[t1] <= sub_res[t1][RADIX];
            end
        end
    endgenerate

    genvar t2;
    generate 
        for (t2=0; t2 < ((2*(PE_UNITS+1))+1); t2++) 
        begin : gen_sub_res_t
            //if (~reset_n)
            //    sub_res[t2] = 0;
            //else if (push_reg[2*(PE_UNITS+1) - t2])
            localparam int t2_WIDTH  = $clog2((2*(PE_UNITS+1))+1);
            localparam bit [t2_WIDTH-1:0] t2_unsigned = t2[t2_WIDTH-1:0];
            if ((t2 == 0) | (t2 == 1))
                always_comb sub_res[t2] = s_array[0] + p_neg_array[t2] + sub_b_i[t2];
            else
                always_comb sub_res[t2] = s_array[t2_unsigned >> 1] + p_neg_array[t2] + sub_b_i[t2];
        end // gen_sub_res_t
    endgenerate

    genvar t3;
    generate 
        for (t3=0; t3 < ((2*(PE_UNITS+1))+1); t3++) begin : gen_t_sub_reg
            always_ff @(posedge clk or negedge reset_n) begin
                if (~reset_n)
                    t_subtracted_reg[t3] <= '0;
                else if (zeroize)
                    t_subtracted_reg[t3] <= '0;
                else if (push_reg[(2*(PE_UNITS+1)) - t3])
                    t_subtracted_reg[t3] <= sub_res[t3][RADIX-1 : 0];
                else 
                    t_subtracted_reg[t3] <= t_subtracted_reg[t3];
            end
        end // gen_t_sub_reg
    endgenerate

    // Storing the final results from the system
    genvar k0;
    generate 
        for (k0=0; k0 < ((2*(PE_UNITS+1))+1); k0++) begin : gen_p_o
            assign p_internal[k0*RADIX +: RADIX] = t_reg[k0];
            assign p_subtracted_internal[k0*RADIX +: RADIX] = t_subtracted_reg[k0];
        end
    endgenerate

    always_comb last_reduction = (sub_b_o[2*(PE_UNITS+1)]);
    assign p_o = (last_reduction)? p_subtracted_internal[REG_SIZE-1:0] : p_internal[REG_SIZE-1:0];

    // Determines when results are ready based on S_NUM
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            push_reg <= 'b0;
        else if (zeroize)
            push_reg <= 'b0;
        else if (start_i)
            push_reg[(3*S_NUM)-1] <= 1'b1;
        else // one shift to right
            push_reg <= {1'b0, push_reg[(3*S_NUM)-1 : 1]};
    end
    
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            push_reg_eq_zero_ff <= '0;
        else if (zeroize)
            push_reg_eq_zero_ff <= '0;
        else
            push_reg_eq_zero_ff <= push_reg_eq_zero;
    end

    assign push_reg_eq_zero = push_reg == 'b0;
    assign ready_o = push_reg_eq_zero & ~push_reg_eq_zero_ff;

endmodule
