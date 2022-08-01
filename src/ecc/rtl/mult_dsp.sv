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
    input  logic [RADIX-1:0]   A,
    input  logic [RADIX-1:0]   B,

    output logic [2*RADIX-1:0] P
);

    always_comb begin
        P = A * B;
    end

endmodule
