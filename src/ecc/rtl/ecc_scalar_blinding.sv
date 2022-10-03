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
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module ecc_scalar_blinding #(
    parameter REG_SIZE     = 384,
    parameter RND_SIZE     = 192,
    parameter RADIX        = 32,
    parameter GROUP_ORDER  = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // DATA PORT
    input  wire                             en_i,
    input  wire [REG_SIZE-1 : 0]            data_i,
    input  wire [RND_SIZE-1 : 0]            rnd_i,
    output wire [REG_SIZE+RND_SIZE-1 : 0]   data_o,
    output wire                             busy_o
    );

    //----------------------------------------------------------------
    // Local Parameters
    //----------------------------------------------------------------
    // Equivalent to $ceil(REG_SIZE/RADIX) + 1
    localparam  REG_DIG_NUM  = ((REG_SIZE + RADIX - 1) / RADIX) + 1;
    localparam  RND_DIG_NUM  = ((RND_SIZE + RADIX - 1) / RADIX) + 1;
    localparam  FULL_DIG_NUM = REG_DIG_NUM + RND_DIG_NUM;
    
    localparam  FULL_REG_SIZE   = REG_DIG_NUM * RADIX;
    localparam  FULL_RND_SIZE   = RND_DIG_NUM * RADIX;
    localparam  FULL_SIZE       = FULL_DIG_NUM * RADIX;

    //----------------------------------------------------------------
    // Registers
    //----------------------------------------------------------------
    logic [RADIX-1 : 0] a_array[0 : REG_DIG_NUM-1];
    logic [RADIX-1 : 0] b_array[0 : RND_DIG_NUM-1];
    logic [RADIX-1 : 0] p_array[0 : FULL_DIG_NUM-1];
    logic [RADIX-1 : 0] scalar_array[0 : FULL_DIG_NUM-1];

    logic [FULL_REG_SIZE-1 : 0]     a_reg;        //extended with zero
    logic [FULL_RND_SIZE-1 : 0]     b_reg;        //extended with zero
    logic [FULL_SIZE-1 : 0]         scalar_reg;   //extended with zero
    logic [FULL_SIZE-1 : 0]         p_internal;

    logic [RADIX-1   : 0]    mult_opa;
    logic [RADIX-1   : 0]    mult_opb;
    logic [2*RADIX-1 : 0]    mult_out;

    logic [3*RADIX-1 : 0]    add0_opa;
    logic [3*RADIX-1 : 0]    add0_opb;
    logic [3*RADIX-1 : 0]    add0_out;

    logic [RADIX-1 : 0]      add1_opa;
    logic [RADIX-1 : 0]      add1_opb;
    logic                    add1_cin;
    logic [RADIX-1 : 0]      add1_out;
    logic                    add1_cout;

    logic [3*RADIX-1 : 0]    accu_reg;
    logic                    accu_store;
    logic                    accu_shift;
    logic                    accu_done;

    logic                    shift_state;

    logic [7 : 0]            product_idx;
    logic [7 : 0]            operand_idx;

    //----------------------------------------------------------------
    // reg update
    //----------------------------------------------------------------

    always_ff @(posedge clk) 
    begin : input_reg
        if (~reset_n) begin
            a_reg <= 'b0;
            b_reg <= 'b0;
            scalar_reg <= 'b0;
        end
        else if (en_i) begin
            a_reg <= GROUP_ORDER;
            b_reg <= rnd_i;
            scalar_reg <= data_i;
        end 
    end // input_reg

    genvar i;
    generate 
        for (i=0; i < REG_DIG_NUM; i++) begin : gen_a_array
            assign a_array[i] = a_reg[i*RADIX +: RADIX];
        end
    endgenerate // gen_a_array

    genvar j;
    generate 
        for (j=0; j < RND_DIG_NUM; j++) begin : gen_b_array
            assign b_array[j] = b_reg[j*RADIX +: RADIX];
        end
    endgenerate // gen_b_array

    genvar k;
    generate 
        for (k=0; k < FULL_DIG_NUM; k++) begin : gen_scalar_array
            assign scalar_array[k] = scalar_reg[k*RADIX +: RADIX];
        end
    endgenerate // gen_scalar_array


    //----------------------------------------------------------------
    // core instantiation
    //----------------------------------------------------------------

    ecc_mult_dsp #(
        .RADIX(RADIX)
        ) 
        ecc_mult_dsp_i (
        .A(mult_opa),
        .B(mult_opb),
        .P(mult_out)
    );

    ecc_adder #(
        .N(3*RADIX)
        ) 
        ecc_adder_i0(
        .a(add0_opa),
        .b(add0_opb),
        .cin(1'b0),
        .s(add0_out),
        .cout()
    );

    ecc_adder #(
        .N(RADIX)
        ) 
        ecc_adder_i1(
        .a(add1_opa),
        .b(add1_opb),
        .cin(add1_cin),
        .s(add1_out),
        .cout(add1_cout)
    );


    //----------------------------------------------------------------
    // accumulator
    //----------------------------------------------------------------

    always_ff @(posedge clk) begin
        if (!reset_n)
            accu_reg      <= 0;
        else if (en_i)
            accu_reg      <= 0;
        else begin
            if (accu_store)
                accu_reg <= add0_out;
            else if (accu_shift)
                accu_reg <= accu_reg >> RADIX;
        end
    end

    //----------------------------------------------------------------
    // multiplier state logic
    //----------------------------------------------------------------
    
    always_ff @(posedge clk) begin
        if (!reset_n) begin
            product_idx     <= FULL_DIG_NUM-1;
            operand_idx     <= 0;
            shift_state     <= 0;
            add1_cin        <= 0;
        end
        else if (en_i) begin
            product_idx     <= 0;
            operand_idx     <= 0;
            shift_state     <= 0;
            add1_cin        <= 0;
        end
        else begin
            if (product_idx < FULL_DIG_NUM-1) begin
                if (shift_state) begin
                    product_idx <= product_idx + 1;
                    if (product_idx < REG_DIG_NUM-1)
                        operand_idx <= 0;
                    else
                        operand_idx <= 2 + product_idx - REG_DIG_NUM;
                    add1_cin <= add1_cout;
                    shift_state <= 0;
                end
                else begin
                    if ((operand_idx < product_idx) & (operand_idx < RND_DIG_NUM-1)) begin
                        shift_state <= 0;
                        operand_idx <= operand_idx + 1;
                    end
                    else
                        shift_state <= 1;
                end
            end
        end
    end

    assign accu_store = (accu_done)? 0 : (!shift_state);
    assign accu_shift = (accu_done)? 0 : shift_state;
    assign accu_done = (product_idx == FULL_DIG_NUM-1);

    // Determines which a and b is pushed through the multiplier
    always_comb begin
        mult_opa = a_array[product_idx - operand_idx];
        mult_opb = b_array[operand_idx];
    end

    // Determines which a and b is pushed through the adders
    always_comb begin
        add0_opa = mult_out;
        add0_opb = accu_reg;

        add1_opa = accu_reg[RADIX-1 : 0];
        add1_opb = scalar_array[product_idx];
    end

    //----------------------------------------------------------------
    // Storing the results
    //----------------------------------------------------------------
    genvar t;
    generate 
        for (t=0; t < FULL_DIG_NUM; t++) begin : gen_t_reg
            always_ff @(posedge clk) begin
                if (~reset_n) begin
                    p_array[t] <= 'b0;
                end
                else if (accu_shift & (t == product_idx)) begin
                    p_array[t] <= add1_out;
                end
            end
        end
    endgenerate

    genvar t0;
    generate 
        for (t0=0; t0 < FULL_DIG_NUM; t0++) begin : gen_p_o
            assign p_internal[t0*RADIX +: RADIX] = p_array[t0];
        end
    endgenerate

    
    assign data_o = p_internal[REG_SIZE+RND_SIZE-1   : 0];
    assign busy_o = ~accu_done;

endmodule