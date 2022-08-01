//======================================================================
//
// compact.sv
// --------
// from VHDL-SIKE: a speed optimized hardware implementation of the 
//      Supersingular Isogeny Key Encapsulation scheme
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module compact (
    // DATA PORT
    input  wire     a1,
    input  wire     b1,
    input  wire     a2,
    input  wire     b2,
    output wire     A_out,
    output wire     B_out
);

    logic   g2;
    logic   p2;

    assign g2 = a2 & b2;
    assign p2 = a2 ^ b2;
    
    assign A_out = g2 | (p2 & a1);
    assign B_out = g2 | (p2 & b1);

endmodule