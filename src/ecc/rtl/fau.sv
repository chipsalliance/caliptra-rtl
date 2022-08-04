//======================================================================
//
// fau.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module fau #(
    parameter REG_SIZE      = 384,
    parameter PRIME         = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff,
    parameter ADD_NUM_ADDS  = 1,
    parameter ADD_BASE_SZ   = 384
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // DATA PORT
    input  wire                 sub_i,
    input  wire                 red_i,
    input  wire                 mult_start_i,
    input  wire [REG_SIZE-1:0]  opa_i,
    input  wire [REG_SIZE-1:0]  opb_i,
    output wire [REG_SIZE-1:0]  add_res_o,
    output wire [REG_SIZE-1:0]  mult_res_o,
    output wire                 ready_o
    );

    logic [REG_SIZE-1 : 0]  mult_res_s;
    logic [REG_SIZE-1 : 0]  mult_opa;
    logic [REG_SIZE-1 : 0]  mult_opb;
    logic                   mult_ready;
    logic [REG_SIZE-1 : 0]  add_res_s;
    logic                   add_ready;
    
    reg                     mult_start;
    reg                     mult_start_dly;
    wire                    mult_start_edge;
    reg                     sub;
    reg                     red;

    assign mult_opa = opa_i;
    assign mult_opb = opb_i;

    
    //----------------------------------------------------------------
    // MULTIPILER
    //----------------------------------------------------------------
    mm #(
        .REG_SIZE(REG_SIZE),
        .PE_UNITS(5),
        .S_NUM(13),
        .RADIX(32)
        )
        i_MULTIPLIER (
        .clk(clk),
        .reset_n(reset_n),

        .start_i(mult_start_edge),
        .opa_i(mult_opa),
        .opb_i(mult_opb),
        .p_o(mult_res_s),
        .ready_o(mult_ready)
        );


    //----------------------------------------------------------------
    // ADDER/SUBTRACTOR
    //----------------------------------------------------------------
    add_sub_mod_alter #(
        .REG_SIZE(REG_SIZE),
        .PRIME(PRIME),
        .NUM_ADDS(ADD_NUM_ADDS),
        .BASE_SZ(ADD_BASE_SZ)
        )
        i_ADDER_SUBTRACTOR (
        .clk(clk),
        .reset_n(reset_n),

        .red_i(red),
        .sub_i(sub),
        .opa_i(opa_i),
        .opb_i(opb_i),
        .res_o(add_res_s),
        .ready_o(add_ready)
        );


    always_ff @(posedge clk or negedge reset_n) begin
            mult_start <= mult_start_i;
            mult_start_dly <= mult_start;
            sub <= sub_i;
            red <= red_i;
    end
    
    assign mult_start_edge = mult_start & ~mult_start_dly;
    assign mult_res_o = mult_res_s;
    assign add_res_o  = add_res_s;
    assign ready = add_ready & mult_ready;

endmodule