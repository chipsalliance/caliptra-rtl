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
    input  logic [RADIX-1:0] a_in,
    input  logic [RADIX-1:0] b_in,
    input  logic [RADIX-1:0] p_in,
    input  logic [RADIX-1:0] m_in,
    input  logic [RADIX-1:0] s_in,
    input  logic [RADIX  :0] c_in,
    input  logic             odd,

    output logic [RADIX-1:0] s_out,
    output logic [RADIX  :0] c_out
);


    //----------------------------------------------------------------
    // PE
    //----------------------------------------------------------------
    logic  [2*RADIX-1 : 0]    mult0_out;
    logic  [2*RADIX-1 : 0]    mult1_out;

    logic  [RADIX   : 0]      c_mux;
    logic  [RADIX-1 : 0]      s_mux;

    logic  [2*RADIX   : 0]    res;
    logic  [RADIX-1 : 0]      res_LSW;
    logic  [RADIX   : 0]      res_MSW;

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

    always_comb begin
        res = {1'b0, mult0_out} + {1'b0, mult1_out} + c_mux + s_mux;
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            c_out <= 0;
        else
            c_out <= res_MSW;
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            s_out <= 0;
        else
            s_out <= res_LSW;
    end

endmodule