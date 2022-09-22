`timescale 1ns / 1ps
//======================================================================
//
// reduction.v
// --------
// This is function will do modulus over 8191 = 2^13 -1 = 0x1FFF
//
//
// Author: Emre Karabulut
//======================================================================

module reduction
(
    // DATA PORT
    input  wire [25:0]   naive,
    output reg   [12:0]  reducted
);

    reg [13:0]   x,y;

    always @* begin
        reducted =0;
        x =  naive[25:13]+naive[12:0];
        y =  x[13]+x[12:0];
        if (y==13'h1FFF)
            reducted =  13'h0;
        else
            reducted =  y;
    end

endmodule
