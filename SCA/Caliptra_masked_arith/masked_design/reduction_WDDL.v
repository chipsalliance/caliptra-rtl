`timescale 1ns / 1ps

`define SYNTH
//======================================================================
//
// reduction.v
// --------
// This is function will do modulus over 8191 = 2^13 -1 = 0x1FFF
//
//
// Author: Emre Karabulut
//======================================================================
(*KEEP_HIERARCHY="true"*)
module reduction_WDDL
(
    // DATA PORT
    input  wire [25:0]   naive,
    output reg   [12:0]  reducted,
`ifdef SYNTH
    output reg   [12:0]  reducted_n
`else
    (* S="true" *) output reg   [12:0]  reducted_n
`endif
);

    wire [13:0]   x,y;
`ifdef SYNTH
    (* S="true" *) wire [13:0]   x_n,y_n;
`else
    wire [13:0]   x_n,y_n;
`endif
    

    always @* begin
        reducted =0;
        reducted_n =13'h1FFF;
        if (y==13'h1FFF)
            reducted =  13'h0;
        else
            reducted =  y;

        if (y==13'h1FFF)
            reducted_n =  13'h1FFF;
        else
            reducted_n =  y_n;

`ifndef SYNTH
    if ((reducted_n) != (~reducted))
        $display("error reduction reducted= %d and reducted_n= %d", reducted, reducted_n);
`endif
    end

    adder_13_bit_WDDL add1
  (.A(naive[12:0]),
   .B(naive[25:13]),
   .C(x),
   .C_n(x_n)
   );

   adder_13_bit_WDDL add2
  (.A(x[12:0]),
   .B({12'h000,x[13]}),
   .C(y),
   .C_n(y_n)
   );

`ifndef SYNTH
always @*
begin
    if ((y) != (~y_n))
        $display("error reduction y= %d and y_n= %d", y, y_n);

    if ((x) != (~x_n))
        $display("error reduction x= %d and x_n= %d", x, x_n);

end
`endif

endmodule
