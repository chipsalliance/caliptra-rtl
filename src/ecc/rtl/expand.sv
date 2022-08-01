//======================================================================
//
// expand.sv
// --------
// from VHDL-SIKE: a speed optimized hardware implementation of the 
//      Supersingular Isogeny Key Encapsulation scheme
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module expand (
    // DATA PORT
    input  wire     a1,
    input  wire     b1,
    input  wire     a2,
    input  wire     b2,
    input  wire     S_in,
    output wire     s1,
    output wire     s2
);

    logic p1;
    logic p2;  
    logic P_all;
    logic c1;
    logic c2;
    logic g1;

    assign p1 = a1 ^ b1;
    assign p2 = a2 ^ b2;
    assign P_all = p1 & p2;
    assign c1 = S_in ^ P_all;
    assign g1 = a1 & b1;
    assign c2 = g1 | (p1 & c1);
    
    assign s1 = p1 ^ c1;
    assign s2 = p2 ^ c2;

endmodule