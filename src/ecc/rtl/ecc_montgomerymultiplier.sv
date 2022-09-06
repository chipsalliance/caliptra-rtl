//======================================================================
//  Module:
//      ecc_montgomerymultiplier.sv
//
// Montgomery Multiplier based on 
// Optimized Algorithms and Architectures for Montgomery Multiplication
// for Post-quantum Cryptography by Rami Elkhatib et. al.
//
// Authors:
//      Mojtaba Bisheh-Niasar
//      Zhipeng Zhao
//      Alexey Lavrov
//======================================================================

module ecc_montgomerymultiplier #(
    parameter REG_SIZE  = 384,
    parameter RADIX     = 32
)
(
    // Clock and reset.
    input  wire                  clk,
    input  wire                  reset_n,

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
    localparam  int unsigned S_NUM = $ceil(real'(REG_SIZE) / RADIX) + 1;
    localparam  int unsigned FULL_REG_SIZE = S_NUM * RADIX;
    // Each PE performs two iterations out of S_NUM - 1
    // See section 4.2 of Khatib_2019 paper.
    // PE_UNITS does not include the last PE.
    // The last PE is instantiated separately.
    localparam  PE_UNITS = (S_NUM - 1) / 2 - 1;


    //----------------------------------------------------------------
    // Registers
    //----------------------------------------------------------------
    logic [RADIX-1 : 0] a_array[0:PE_UNITS+1];
    logic [RADIX-1 : 0] b_array[0:PE_UNITS+1];
    logic [RADIX-1 : 0] p_array[0:PE_UNITS+1];
    logic [RADIX-1 : 0] m_array[0:PE_UNITS];
    logic [RADIX   : 0] c_array[0:PE_UNITS+1];
    logic [RADIX-1 : 0] s_array[0:PE_UNITS+1];
    
    logic   [RADIX-1 : 0] t_reg[0:2*PE_UNITS+1];
    
    logic   [FULL_REG_SIZE-1 : 0]          a_reg;
    logic   [FULL_REG_SIZE+RADIX-1 : 0]    b_reg;  //extended with zero
    logic   [FULL_REG_SIZE+RADIX-1 : 0]    p_reg;  //extended with zero
    logic   [RADIX-1:0]               n_prime_reg;
    logic   [3*S_NUM-1 : 0]           push_reg;
    logic                             push_reg_eq_zero;
    logic                             push_reg_eq_zero_prev;
    logic                             odd;
    logic   [RADIX-1 : 0]             last_s_reg;
    logic   [FULL_REG_SIZE-1:0]              p_internal;

    logic   [1 : 0]                   cnt;

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

    genvar i;
    generate 
        for (i=0; i < PE_UNITS; i++) begin : gen_PE //PE general boxes
            ecc_pe #(
                .RADIX(RADIX)
                )
                box_i
                (
                .clk(clk),
                .reset_n(reset_n),
                .start_in(start_i),
                .a_in(a_array[i+1]),
                .b_in(b_array[i+1]),
                .p_in(p_array[i+1]),
                .m_in(m_array[i]),
                .s_in(s_array[i+1]),
                .c_in(c_array[i]),
                .odd(odd),

                .a_out(a_array[i+2]),
                .m_out(m_array[i+1]),
                .s_out(s_array[i]),
                .c_out(c_array[i+1])
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
    always_ff @(posedge clk) begin
        if (~reset_n)
            last_s_reg <= 'b0;
        else if (start_i)
            last_s_reg <= 'b0;
        else
            last_s_reg <= c_array[PE_UNITS+1][RADIX-1:0];
    end

    // Set odd flag
    always_ff @(posedge clk) begin
        if (~reset_n)
            odd <= 0;
        else if (start_i)
            odd <= 1'b1;
        else
            odd <= ~odd;
    end

    always_ff @(posedge clk) 
    begin : input_reg
        if (start_i) begin
            a_reg <= opa_i;
            b_reg <= opb_i;
            p_reg <= n_i;
            n_prime_reg <= n_prime_i;
        end else begin
            if (odd) begin
                a_reg[FULL_REG_SIZE-RADIX-1 : 0] <= a_reg[FULL_REG_SIZE-1 : RADIX];
                a_reg[FULL_REG_SIZE-1 : FULL_REG_SIZE-RADIX] <= 'b0; //Shift 
            end 
        end

        if (~reset_n) begin
            a_reg <= 'b0;
            b_reg <= 'b0;
            p_reg <= 'b0;
            n_prime_reg <= 'b0;
        end
    end // input_reg

    assign a_array[0] = a_reg[RADIX-1 : 0];

    // Determines which b and p is pushed through the system
    assign b_array[0] = b_reg[RADIX-1 : 0];
    assign p_array[0] = p_reg[RADIX-1 : 0];
    genvar j;
    generate 
        for (j=1; j < PE_UNITS+2; j++) begin : gen_b_p_array
            assign b_array[j] = odd ? b_reg[(2*j+1)*RADIX-1 : (2*j)*RADIX] : b_reg[(2*j)*RADIX-1 : (2*j-1)*RADIX];
            assign p_array[j] = odd ? p_reg[(2*j+1)*RADIX-1 : (2*j)*RADIX] : p_reg[(2*j)*RADIX-1 : (2*j-1)*RADIX];
        end
    endgenerate

    // Storing the results from the system
    genvar t;
    generate 
        for (t=0; t < 2*(PE_UNITS+1); t++) begin : gen_t_reg
            always_ff @(posedge clk) begin
                if (~reset_n)
                    t_reg[t] <= 'b0;
                else if (push_reg[2*PE_UNITS+1 - t])
                    t_reg[t] <= s_array[t >> 1];
                else
                    t_reg[t] <= t_reg[t];
            end
        end
    endgenerate
    
    genvar k;
    generate 
        for (k=0; k < 2*(PE_UNITS+1); k++) begin : gen_p_o
            assign p_internal[(k+1)*RADIX-1 : k*RADIX] = t_reg[k];
        end
    endgenerate

    assign p_o = p_internal[REG_SIZE-1:0];

    // Determines when results are ready based on S_NUM
    always_ff @(posedge clk) begin
        if (!reset_n)
            push_reg <= 'b0;
        else if (start_i)
            push_reg[3*S_NUM-2] <= 1'b1;
        else
            push_reg <= push_reg >> 1;
    end
    
    always_ff @(posedge clk) begin
        push_reg_eq_zero_prev <= push_reg_eq_zero;
    end

    assign push_reg_eq_zero = push_reg == 'b0;
    assign ready_o = push_reg_eq_zero & ~push_reg_eq_zero_prev;

endmodule