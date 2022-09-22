//======================================================================
//
// PE.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module PE_final #(
    parameter RADIX = 32
)
(
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // DATA PORT
    input  wire [RADIX-1:0] a_in,
    input  wire [RADIX-1:0] b_in,
    input  wire [RADIX-1:0] p_in,
    input  wire [RADIX-1:0] m_in,
    input  wire [RADIX-1:0] s_in,
    input  wire [RADIX  :0] c_in,
    input  wire             odd,

    output reg [RADIX-1:0] s_out,
    output reg [RADIX  :0] c_out
);


    //----------------------------------------------------------------
    // PE
    //----------------------------------------------------------------
    wire  [2*RADIX-1 : 0]    mult0_out;
    wire  [2*RADIX-1 : 0]    mult1_out;

    wire  [RADIX   : 0]      c_mux;
    wire  [RADIX-1 : 0]      s_mux;

    reg  [2*RADIX   : 0]    res;
    wire  [RADIX-1 : 0]      res_LSW;
    wire  [RADIX   : 0]      res_MSW;

    mult_dsp MULT1(
        .A(a_in),
        .B(b_in),
        .P(mult0_out)
    );

    mult_dsp MULT2(
        .A(p_in),
        .B(m_in),
        .P(mult1_out)
    );

    assign c_mux = odd ? c_out : c_in;
    assign s_mux = odd ? s_in : s_out;

    assign res_MSW = res[2*RADIX : RADIX];
    assign res_LSW = res[RADIX-1 : 0];

    always @* begin
        res = {1'b0, mult0_out} + {1'b0, mult1_out} + c_mux + s_mux;
    end

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            c_out <= 0;
        else
            c_out <= res_MSW;
    end

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            s_out <= 0;
        else
            s_out <= res_LSW;
    end

endmodule