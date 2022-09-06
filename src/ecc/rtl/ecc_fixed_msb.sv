//======================================================================
//
// ecc_fixed_msb.sv
// --------
// The Montgomery Ladder algorithm inherently depends on the MSB of the
// scalar. In order to avoid leaking this MSB and fall into HNP (Hidden Number
// Problem) issues, we use the trick described in https://eprint.iacr.org/2011/232.pdf
// to have the MSB always set.
//
// This module takes the scalar and compute (scalar+q) and (scalar+2q)
// output = (scalar+2q) if log(scalar+q)==log(q), otherwise (scalar+q)
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module ecc_fixed_msb #(
    parameter REG_SIZE     = 384,
    parameter GROUP_ORDER  = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // DATA PORT
    input  wire                  en_i,
    input  wire [REG_SIZE-1 : 0] data_i,
    output wire [REG_SIZE   : 0] data_o
    );

    logic [REG_SIZE   : 0]  data_q;
    logic [REG_SIZE   : 0]  data_q_reg;
    logic [REG_SIZE+1 : 0]  data_2q;
    logic [REG_SIZE+1 : 0]  data_2q_reg;

    always_ff @(posedge clk) 
    begin : register_results
        if (!reset_n) begin
            data_q_reg  <= '0;
            data_2q_reg <= '0;
        end
        else if (en_i == 1) begin
            data_q_reg  <= data_q;
            data_2q_reg <= data_2q;
        end
    end //register_results

    // adder to compute scalar + q
    ecc_adder #(
        .N(REG_SIZE)
        ) 
        adder_inst_0(
        .a(data_i),
        .b(GROUP_ORDER),
        .cin(1'b0),
        .s(data_q[REG_SIZE-1 : 0]),
        .cout(data_q[REG_SIZE])
    );

    // adder to compute scalar + 2q
    ecc_adder #(
        .N(REG_SIZE+1)
        ) 
        adder_inst_1(
        .a({1'b0,data_q_reg}),
        .b({2'b0,GROUP_ORDER}),
        .cin(1'b0),
        .s(data_2q[REG_SIZE : 0]),
        .cout(data_2q[REG_SIZE+1])
    );
    
    assign data_o = (data_q_reg[REG_SIZE] == 1'b1)? data_q_reg[REG_SIZE   : 0] : data_2q_reg[REG_SIZE   : 0];

endmodule