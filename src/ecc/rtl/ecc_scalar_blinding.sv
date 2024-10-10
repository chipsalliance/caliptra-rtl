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
// ecc_scalar_blinding.sv
// --------
// The scalar blinding is a SCA countermeasure described in
// "Resistance against Differential Power Analysis for Elliptic Curve 
// Cryptosystems" by Coron.
// Based on "Efficient Side-Channel Attacks on Scalar Blinding on Elliptic 
// Curves with Special Structure" by Schindler et. al., the random value size
// should be at least half of group order length. 
//
// This module takes the scalar and a random value (rnd) to randomize the scalar
// as follows:
//      randomized_scalar = scalar + rnd * group_order
// with the following contraint:
//      scalar < group_order
//
// From the contraint, the output has REG_SIZE+RND_SIZE bit length:
//      scalar + rnd*group_order < (rnd+1)*group_order < (2^RND_SIZE)*group_order
//
//======================================================================

module ecc_scalar_blinding #(
    parameter                   REG_SIZE     = 384,
    parameter                   RND_SIZE     = 192,
    parameter                   RADIX        = 32,
    parameter [REG_SIZE-1 : 0]  GROUP_ORDER  = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,
    input wire           zeroize,

    // DATA PORT
    input  wire                             en_i,
    input  wire [REG_SIZE-1 : 0]            data_i,
    input  wire [RND_SIZE-1 : 0]            rnd_i,
    output wire [(REG_SIZE+RND_SIZE)-1 : 0] data_o,
    output wire                             busy_o
    );

    //----------------------------------------------------------------
    // Local Parameters
    //----------------------------------------------------------------
    // Equivalent to $ceil(REG_SIZE/RADIX) + 1
    localparam  REG_DIG_NUM  = (((REG_SIZE + RADIX) - 1) / RADIX) + 1;  //13
    localparam  RND_DIG_NUM  = (((RND_SIZE + RADIX) - 1) / RADIX) + 1;  //7
    localparam  FULL_DIG_NUM = REG_DIG_NUM + RND_DIG_NUM - 1;  //19
    
    localparam  FULL_REG_SIZE   = REG_DIG_NUM * RADIX;
    localparam  FULL_RND_SIZE   = RND_DIG_NUM * RADIX;
    localparam  FULL_SIZE       = FULL_DIG_NUM * RADIX;

    localparam [(FULL_RND_SIZE-RND_SIZE)-1 : 0] zero_pad_rnd = '0;
    localparam [(FULL_REG_SIZE-REG_SIZE)-1 : 0] zero_pad_reg = '0;
    localparam [(FULL_SIZE-REG_SIZE)-1 : 0]     zero_pad_reg_full = '0;
    localparam [RADIX-1 : 0]                    zero_pad_radix = '0;

    localparam A_ARR_WIDTH      = $clog2(REG_DIG_NUM+1);   //4
    localparam B_ARR_WIDTH      = $clog2(RND_DIG_NUM+1);   //3
    localparam P_ARR_WIDTH      = $clog2(FULL_DIG_NUM+1);  //5

    //----------------------------------------------------------------
    // Registers
    //----------------------------------------------------------------
    logic [RADIX-1 : 0] a_array[0 : REG_DIG_NUM-1];
    logic [RADIX-1 : 0] b_array[0 : RND_DIG_NUM-1];
    logic [RADIX-1 : 0] p_array[0 : FULL_DIG_NUM-1];
    logic [RADIX-1 : 0] scalar_array[0 : FULL_DIG_NUM-1];

    logic [A_ARR_WIDTH-1 : 0]       a_idx;
    logic [B_ARR_WIDTH-1 : 0]       b_idx;

    logic [FULL_REG_SIZE-1 : 0]     a_reg;        //extended with zero
    logic [FULL_RND_SIZE-1 : 0]     b_reg;        //extended with zero
    logic [FULL_SIZE-1 : 0]         scalar_reg;   //extended with zero
    logic [FULL_SIZE-1 : 0]         p_internal;

    logic [RADIX-1      : 0]        mult_opa;
    logic [RADIX-1      : 0]        mult_opb;
    logic [(2*RADIX)-1  : 0]        mult_out;

    logic [(3*RADIX)-1  : 0]        add0_opa;
    logic [(3*RADIX)-1  : 0]        add0_opb;
    logic [(3*RADIX)-1  : 0]        add0_out;

    logic [RADIX-1 : 0]             add1_opa;
    logic [RADIX-1 : 0]             add1_opb;
    logic                           add1_cin;
    logic [RADIX-1 : 0]             add1_out;
    logic                           add1_cout;

    logic [(3*RADIX)-1 : 0]         accu_reg;
    logic                           accu_store;
    logic                           accu_shift;
    logic                           accu_done;

    logic                           shift_state;

    logic [P_ARR_WIDTH-1 : 0]            product_idx;
    logic [B_ARR_WIDTH-1 : 0]            operand_idx;
    logic [P_ARR_WIDTH-1 : 0]            product_idx_reg;
    logic [B_ARR_WIDTH-1 : 0]            operand_idx_reg;

    logic [P_ARR_WIDTH-B_ARR_WIDTH   : 0]   carry_garbage_bits0;
    logic                                   carry_garbage_bit1;
    //----------------------------------------------------------------
    // reg update
    //----------------------------------------------------------------

    always_ff @(posedge clk or negedge reset_n) 
    begin : input_reg
        if (!reset_n) begin
            a_reg <= '0;
            b_reg <= '0;
            scalar_reg <= '0;
        end
        else if (zeroize) begin
            a_reg <= '0;
            b_reg <= '0;
            scalar_reg <= '0;
        end
        else if (en_i) begin
            a_reg       <= {zero_pad_reg, GROUP_ORDER};
            b_reg       <= {zero_pad_rnd, rnd_i};
            scalar_reg  <= {zero_pad_reg_full, data_i};
        end 
    end // input_reg

    genvar i0;
    generate 
        for (i0=0; i0 < REG_DIG_NUM; i0++) begin : gen_a_array
            assign a_array[i0] = a_reg[i0*RADIX +: RADIX];
        end
    endgenerate // gen_a_array

    genvar j0;
    generate 
        for (j0=0; j0 < RND_DIG_NUM; j0++) begin : gen_b_array
            assign b_array[j0] = b_reg[j0*RADIX +: RADIX];
        end
    endgenerate // gen_b_array

    genvar k0;
    generate 
        for (k0=0; k0 < FULL_DIG_NUM; k0++) begin : gen_scalar_array
            assign scalar_array[k0] = scalar_reg[k0*RADIX +: RADIX];
        end
    endgenerate // gen_scalar_array


    //----------------------------------------------------------------
    // core instantiation
    //----------------------------------------------------------------

    ecc_mult_dsp #(
        .RADIX(RADIX)
        ) 
        ecc_mult_dsp_i (
        .A_i(mult_opa),
        .B_i(mult_opb),
        .P_o(mult_out)
    );

    ecc_adder #(
        .RADIX(3*RADIX)
        ) 
        ecc_adder_i0(
        .a_i(add0_opa),
        .b_i(add0_opb),
        .cin_i(1'b0),
        .s_o(add0_out),
        .cout_o(carry_garbage_bit1)
    );

    ecc_adder #(
        .RADIX(RADIX)
        ) 
        ecc_adder_i1(
        .a_i(add1_opa),
        .b_i(add1_opb),
        .cin_i(add1_cin),
        .s_o(add1_out),
        .cout_o(add1_cout)
    );


    //----------------------------------------------------------------
    // accumulator
    //----------------------------------------------------------------

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            accu_reg      <= '0;
        else if (zeroize)
            accu_reg      <= '0;
        else if (en_i)
            accu_reg      <= '0;
        else begin
            if (accu_store)
                accu_reg <= add0_out;
            else if (accu_shift)
                accu_reg <= {zero_pad_radix, accu_reg[(3*RADIX)-1 : RADIX]};
        end
    end

    //----------------------------------------------------------------
    // multiplier state logic
    //----------------------------------------------------------------
    
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            product_idx_reg <= FULL_DIG_NUM[P_ARR_WIDTH-1 : 0];
            operand_idx_reg <= '0;
            shift_state     <= 0;
            add1_cin        <= 0;
            carry_garbage_bits0 <= '0;
        end
        else if (zeroize) begin
            product_idx_reg <= FULL_DIG_NUM[P_ARR_WIDTH-1 : 0];
            operand_idx_reg <= '0;
            shift_state     <= 0;
            add1_cin        <= 0;
            carry_garbage_bits0 <= '0;
        end
        else if (en_i) begin
            product_idx_reg <= '0;
            operand_idx_reg <= '0;
            shift_state     <= 0;
            add1_cin        <= 0;
        end
        else begin
            if (product_idx < FULL_DIG_NUM) begin
                if (shift_state) begin
                    product_idx_reg <= product_idx + 1;
                    if (product_idx < (REG_DIG_NUM-1))
                        operand_idx_reg <= '0;
                    else
                        {carry_garbage_bits0, operand_idx_reg} <= (2'h2 + product_idx) - REG_DIG_NUM;
                    add1_cin <= add1_cout;
                    shift_state <= 0;
                end
                else begin
                    if (({2'b00, operand_idx} < product_idx) & (operand_idx < (RND_DIG_NUM-1))) begin
                        shift_state <= 0;
                        operand_idx_reg <= operand_idx + 1;
                    end
                    else
                        shift_state <= 1;
                end
            end
        end
    end

    assign product_idx = product_idx_reg;
    assign operand_idx = operand_idx_reg;

    assign accu_store = (accu_done)? 0 : (!shift_state);
    assign accu_shift = (accu_done)? 0 : shift_state;
    assign accu_done = (product_idx == FULL_DIG_NUM);

    // Determines which a and b is pushed through the multiplier
    always_comb begin
        a_idx = 4'(product_idx - operand_idx);
        //2,4 =  5- 3
        b_idx = operand_idx;
        mult_opa = a_array[a_idx];
        mult_opb = b_array[b_idx];
    end

    // Determines which a and b is pushed through the adders
    always_comb begin
        add0_opa = {zero_pad_radix, mult_out};
        add0_opb = accu_reg;

        add1_opa = accu_reg[RADIX-1 : 0];
        add1_opb = scalar_array[product_idx];
    end

    //----------------------------------------------------------------
    // Storing the results
    //----------------------------------------------------------------
    genvar t0;
    generate 
        for (t0=0; t0 < FULL_DIG_NUM; t0++) begin : gen_t_reg
            always_ff @(posedge clk or negedge reset_n) begin
                if (!reset_n)
                    p_array[t0] <= '0;
                else if (zeroize)
                    p_array[t0] <= '0;
                else if (accu_shift & (t0 == product_idx))
                    p_array[t0] <= add1_out;
            end
        end
    endgenerate

    genvar t1;
    generate 
        for (t1=0; t1 < FULL_DIG_NUM; t1++) begin : gen_p_o
            assign p_internal[t1*RADIX +: RADIX] = p_array[t1];
        end
    endgenerate

    
    assign data_o = p_internal[(REG_SIZE+RND_SIZE)-1   : 0];
    assign busy_o = ~accu_done;

endmodule