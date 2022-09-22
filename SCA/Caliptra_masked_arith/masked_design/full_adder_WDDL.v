`define SYNTH



`ifdef SYNTH
(*KEEP_HIERARCHY="true"*)
`endif
module full_adder_WDDL 
  (
   i_bit1,
     i_bit2,
     i_carry,
     i_carry_n,
    o_sum,
    o_carry,
    o_sum_n,
    o_carry_n 
   );

`ifdef SYNTH
   (* S = "true" *)
   output reg o_sum_n;
   (* S = "true" *)
   output reg o_carry_n;
   (* S = "true" *) input  i_bit1;
   (* S = "true" *) input  i_bit2;
   (* S = "true" *) input  i_carry;
   (* S = "true" *) input  i_carry_n;
   (* S = "true" *) output reg o_sum;
   (* S = "true" *) output reg o_carry;
`else
   output reg o_sum_n;
   output reg o_carry_n;
   input  i_bit1;
   input  i_bit2;
   input  i_carry;
   input  i_carry_n;
   output reg o_sum;
   output reg o_carry;
`endif 
 
  
 
  wire   w_WIRE_1;
  wire   w_WIRE_2;
  wire   w_WIRE_3;
       
  assign w_WIRE_1 = i_bit1 ^ i_bit2;
  assign w_WIRE_2 = w_WIRE_1 & i_carry;
  assign w_WIRE_3 = i_bit1 & i_bit2;
 
  always @* begin
    o_sum   = w_WIRE_1 ^ i_carry;
    o_carry = w_WIRE_2 | w_WIRE_3;
  end

  
`ifdef SYNTH
   (* S = "true" *) wire  i_bit1_n, i_bit2_n, i_carry_n;
   (* S = "true" *) wire   w_WIRE_1_n, w_WIRE_2_n, w_WIRE_3_n;
`else
   wire  i_bit1_n, i_bit2_n, i_carry_n;
   wire   w_WIRE_1_n, w_WIRE_2_n, w_WIRE_3_n;
`endif


  assign i_bit1_n = ~i_bit1;
  assign i_bit2_n = ~i_bit2;

  

  xnor(w_WIRE_1_n,i_bit1_n, i_bit2_n);
  assign w_WIRE_2_n = w_WIRE_1_n | i_carry_n;
  assign w_WIRE_3_n = i_bit1_n | i_bit2_n;

  wire xnor_wire;
  xnor(xnor_wire, w_WIRE_1_n, i_carry_n);


  always @* begin
    o_sum_n   = xnor_wire;
    o_carry_n = w_WIRE_2_n & w_WIRE_3_n;
  end
 
 
   
endmodule // full_adder_WDDL