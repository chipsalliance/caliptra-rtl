//======================================================================
//
// PE_first.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module ecc_PE_first #(
    parameter RADIX = 32
)
(
    // Clock and reset.
    input  wire              clk,
    input  wire              reset_n,

    input  wire              start_in,
    // DATA PORT
    input  wire [RADIX-1:0]  a_in,
    input  wire [RADIX-1:0]  b_in,
    input  wire [RADIX-1:0]  p_in,
    input  wire [RADIX-1:0]  s_in,
    input  wire [RADIX-1:0]  n_prime_in,
    input  wire              odd,

    output logic [RADIX-1:0] a_out,
    output logic [RADIX-1:0] m_out,
    output logic [RADIX  :0] c_out
);


    //----------------------------------------------------------------
    // ecc_PE_first
    //----------------------------------------------------------------
    logic  [RADIX-1:0]        s_reg;
    logic  [RADIX-1:0]        s;
    logic  [RADIX-1:0]        a_reg;
    logic  [RADIX-1:0]        a;

    logic  [2*RADIX-1 : 0]    mult_out_0;
    logic  [RADIX-1 : 0]      mult_out_0_MSW;
    logic  [RADIX-1 : 0]      mult_out_0_LSW;

    logic  [RADIX   : 0]      res_0;
    logic  [RADIX-1 : 0]      sum_0;
    logic                     carry_0;
    logic  [RADIX-1 : 0]      sum_0_reg;
    logic                     carry_0_reg;

    logic  [RADIX   : 0]      res_1;
    logic  [RADIX-1 : 0]      sum_1;
    logic                     carry_1;

    logic  [RADIX   : 0]      c_0;
    logic  [RADIX   : 0]      c_0_reg;
    logic  [RADIX   : 0]      c_1;

    logic  [2*RADIX-1 : 0]    mult_out_1;
    logic  [RADIX-1 : 0]      m_temp;
    logic  [RADIX-1 : 0]      m_temp_reg;

    logic  [2*RADIX-1 : 0]    mult_out_2;
    logic  [RADIX-1 : 0]      mult_out_2_MSW;
    logic  [RADIX-1 : 0]      mult_out_2_LSW;

    logic [RADIX-1:0] a_out_reg;
    logic [RADIX-1:0] m_out_reg;
    logic [RADIX  :0] c_out_reg;

    ecc_mult_dsp #(
        .RADIX(RADIX)
    ) MULT0 (
        .A(a),
        .B(b_in),
        .P(mult_out_0)
    );

    ecc_mult_dsp #(
        .RADIX(RADIX)
    ) MULT1 (
        .A(n_prime_in),
        .B(sum_0),
        .P(mult_out_1)
    );

    ecc_mult_dsp #(
        .RADIX(RADIX)
    ) MULT2 (
        .A(m_temp_reg),
        .B(p_in),
        .P(mult_out_2)
    );

    assign m_temp = mult_out_1[RADIX-1:0];

    assign mult_out_0_MSW = mult_out_0[2*RADIX-1 : RADIX];
    assign mult_out_0_LSW = mult_out_0[RADIX-1 : 0];
    assign mult_out_2_MSW = mult_out_2[2*RADIX-1 : RADIX];
    assign mult_out_2_LSW = mult_out_2[RADIX-1 : 0];

    assign s = odd ? s_in : s_reg;
    assign a = odd ? a_in : a_reg;

    always_comb begin
        res_0 = {1'b0, s} + {1'b0, mult_out_0_LSW};
        sum_0 = res_0[RADIX-1 : 0];
        carry_0 = res_0[RADIX];
    end

    always_comb begin
        res_1 = {1'b0, sum_0_reg} + {1'b0, mult_out_2_LSW};
        carry_1 = res_1[RADIX];
    end

    always_comb begin
        c_0 = {1'b0, mult_out_0_MSW} + carry_0;
    end

    always_comb begin
        c_1 = {1'b0, mult_out_2_MSW} + carry_1;
    end

    always_ff @(posedge clk) begin
        if (start_in) begin
            c_0_reg <= 'b0;
            sum_0_reg <= 'b0;
            m_temp_reg <= 'b0;
            s_reg <= 'b0;
            a_reg <= 'b0;
        end else begin
            s_reg <= s_in;
            a_reg <= a_in;
            m_temp_reg <= m_temp;
            c_0_reg <= c_0;
            sum_0_reg <= sum_0;
        end

        if(~reset_n) begin
            c_0_reg <= 'b0;
            sum_0_reg <= 'b0;
            m_temp_reg <= 'b0;
            s_reg <= 'b0;
            a_reg <= 'b0;
        end
    end

    assign c_out = c_0_reg + c_1;

    always_ff @(posedge clk) begin
        if (start_in) begin
            a_out <= 'b0;
        end else begin
            a_out <= a;
        end

        if (~reset_n) begin
            a_out <= 'b0;
        end
    end

    always_ff @(posedge clk) begin
        if (start_in) begin
            m_out <= 'b0;
        end else begin
            m_out <= m_temp;
        end

        if (~reset_n) begin
            m_out <= 'b0;
        end
    end

endmodule