`timescale 1ns / 1ps

//======================================================================
//
// xorshift.v
// --------
// This is XorShift
//
//
// Author: Emre Karabulut
//======================================================================


module xorshift #(
    parameter RADIX = 64
)
(
    // DATA PORT
    input  wire [RADIX-1:0]   x,
    output reg   [RADIX-1:0] random_number
);

    reg [RADIX-1:0]   y,z,q;

    always @* begin
        random_number = 0;
        y = #1 x << 21;
        y = #1 x ^ y;        
        z = #1 y >> 35;
        z = #1 y ^ z;                
        q = #1 z << 4;
        q = #1 z ^ q;
        random_number = #1 q;
    end

endmodule