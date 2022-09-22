

module adder #(
    parameter RADIX = 13
)
(
    // DATA PORT
    input  wire [RADIX-1:0]   A,
    input  wire [RADIX-1:0]   B,

    output reg [RADIX:0] P
);

    always @* begin
        P = A + B;
    end

endmodule