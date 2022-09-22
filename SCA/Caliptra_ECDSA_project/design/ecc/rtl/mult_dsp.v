//======================================================================
//
// mult_dsp.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module mult_dsp #(
    parameter RADIX = 32
)
(
    // DATA PORT
    input   [RADIX-1:0]   A,
    input   [RADIX-1:0]   B,

    output reg [2*RADIX-1:0] P
);

    always @* begin
        P = A * B;
    end

endmodule
