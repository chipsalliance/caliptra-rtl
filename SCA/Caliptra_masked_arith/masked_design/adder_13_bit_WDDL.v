`define SYNTH

(*KEEP_HIERARCHY="true"*)
module adder_13_bit_WDDL 
  (
   input  [12:0] A,
   input  [12:0] B,
   output [13:0] C,
`ifdef SYNTH
   (* S="true" *) 
   output [13:0] C_n
`else
    output [13:0] C_n
`endif
   );
 
  
    wire [12:0] carry;
`ifdef SYNTH
    (* S="true" *) wire [12:0] carry_n;
`else
    wire [12:0] carry_n;
`endif


    full_adder_WDDL u1  (A[0], B[0],1'b0,1'b1,C[0],carry[0],C_n[0],carry_n[0]);
    genvar i;
    generate 
        for(i=1;i<13;i=i+1) begin: generate_N_bit_Adder
            full_adder_WDDL u2  (A[i], B[i],carry[i-1],carry_n[i-1],C[i],carry[i],C_n[i],carry_n[i]);
        end  
        assign C[13] = carry[12];
        assign C_n[13] = carry_n[12];
   endgenerate

`ifndef SYNTH
always @*
begin
    if ((carry_n) != (~carry))
        $display("error adder_13 carry= %d and carry_n= %d", carry, carry_n);

    if ((C) != (~C_n))
        $display("error adder_13 carry= %d and carry_n= %d", C, C_n);
end
`endif
 
 
   
endmodule // adder_13_bit_WDDL