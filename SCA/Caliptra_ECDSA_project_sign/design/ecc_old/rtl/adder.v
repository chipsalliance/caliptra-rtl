//======================================================================
//
// add_sub_mod.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module adder #(
    parameter N      = 8
)
(
    // DATA PORT
    input  wire [N-1:0]  a,
    input  wire [N-1:0]  b,
    input  wire          cin,
    output wire [N-1:0]  s,
    output wire          cout
);

    reg [N : 0]   s_full;

    always @* begin
        s_full = {1'b0, a} + {1'b0, b} + cin;
    end
        
    assign s = s_full[N-1 : 0];
    assign cout = s_full[N];

endmodule