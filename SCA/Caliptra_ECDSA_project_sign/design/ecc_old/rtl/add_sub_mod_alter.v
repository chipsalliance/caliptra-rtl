//======================================================================
//
// add_sub_mod_alter.sv
// --------
//
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module add_sub_mod_alter #(
    parameter REG_SIZE      = 384,
    parameter PRIME         = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff,
    parameter NUM_ADDS      = 1,
    parameter BASE_SZ       = 384
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // DATA PORT
    input  wire                 sub_i,
    input  wire                 red_i,
    input  wire  [REG_SIZE-1:0] opa_i,
    input  wire  [REG_SIZE-1:0] opb_i,
    output wire [REG_SIZE-1:0] res_o,
    output wire                 ready_o
);
  
    wire [REG_SIZE-1 : 0] opb0;
    wire [REG_SIZE-1 : 0] opb1;
    wire [REG_SIZE   : 0] result;
    wire [REG_SIZE   : 0] c;
    wire [REG_SIZE-1 : 0] r0;
    wire [REG_SIZE-1 : 0] r1;
    wire                  add_nsub;
    wire                  carry0;
    wire                  carry1;


    assign opb0 = sub_i ? ~opb_i : opb_i;
    assign opb1 = sub_i ? PRIME : ~PRIME;

    adder #(
        .N(REG_SIZE)
        ) 
        adder_inst_0(
        .a(opa_i),
        .b(opb0),
        .cin(sub_i),
        .s(r0),
        .cout(carry0)
    );

    adder #(
        .N(REG_SIZE)
        ) 
        adder_inst_1(
        .a(r0),
        .b(opb1),
        .cin(~sub_i),
        .s(r1),
        .cout(carry1)
    );

    assign res_o = (~sub_i ^ carry0)? r0 : r1;
    
endmodule