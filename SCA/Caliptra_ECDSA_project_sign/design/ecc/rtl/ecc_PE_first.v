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

    output reg [RADIX-1:0] a_out,
    output reg [RADIX-1:0] m_out,
    output wire [RADIX  :0] c_out
);


    //----------------------------------------------------------------
    // ecc_PE_first
    //----------------------------------------------------------------
    reg  [RADIX-1:0]        s_reg;
    wire  [RADIX-1:0]        s;
    reg  [RADIX-1:0]        a_reg;
    wire  [RADIX-1:0]        a;

    wire  [2*RADIX-1 : 0]    mult_out_0;
    wire  [RADIX-1 : 0]      mult_out_0_MSW;
    wire  [RADIX-1 : 0]      mult_out_0_LSW;

    reg  [RADIX   : 0]      res_0;
    reg  [RADIX-1 : 0]      sum_0;
    reg                     carry_0;
    reg  [RADIX-1 : 0]      sum_0_reg;
    reg                     carry_0_reg;

    reg  [RADIX   : 0]      res_1;
    reg                     carry_1;

    reg  [RADIX   : 0]      c_0;
    reg  [RADIX   : 0]      c_0_reg;
    reg  [RADIX   : 0]      c_1;

    wire  [2*RADIX-1 : 0]    mult_out_1;
    wire  [RADIX-1 : 0]      m_temp;
    reg  [RADIX-1 : 0]      m_temp_reg;

    wire  [2*RADIX-1 : 0]    mult_out_2;
    wire  [RADIX-1 : 0]      mult_out_2_MSW;
    wire  [RADIX-1 : 0]      mult_out_2_LSW;

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

    always @* begin
        res_0 = {1'b0, s} + {1'b0, mult_out_0_LSW};
        sum_0 = res_0[RADIX-1 : 0];
        carry_0 = res_0[RADIX];
    end

    always @* begin
        res_1 = {1'b0, sum_0_reg} + {1'b0, mult_out_2_LSW};
        carry_1 = res_1[RADIX];
    end

    always @* begin
        c_0 = {1'b0, mult_out_0_MSW} + carry_0;
    end

    always @* begin
        c_1 = {1'b0, mult_out_2_MSW} + carry_1;
    end

    always @(posedge clk) begin
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

    always @(posedge clk) begin
        if (start_in) begin
            a_out <= 'b0;
        end else begin
            a_out <= a;
        end

        if (~reset_n) begin
            a_out <= 'b0;
        end
    end

    always @(posedge clk) begin
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