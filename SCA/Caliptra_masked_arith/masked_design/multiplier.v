module multiplier #(
    parameter RADIX = 13
)
(
    input  wire [RADIX-1:0]   A,
    input  wire [RADIX-1:0]   B,

    output reg [2*RADIX-1:0] P
);

    always @* begin
        P = A * B;
    end

endmodule