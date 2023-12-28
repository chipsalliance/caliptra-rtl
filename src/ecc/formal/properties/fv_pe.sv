// -------------------------------------------------
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
module fv_pe #(
    parameter RADIX = 32
)
(
    // Clock and reset.
    input  logic              clk,
    input  logic              rst_n,
   
    input  logic              start_in,
    input  logic [RADIX-1:0]  a_in,
    input  logic [RADIX-1:0]  b_in,
    input  logic [RADIX-1:0]  p_in,
    input  logic [RADIX-1:0]  m_in,
    input  logic [RADIX-1:0]  s_in,
    input  logic [RADIX  :0]  c_in,
    input  logic              odd,

    input logic [RADIX-1:0] a_out,
    input logic [RADIX-1:0] m_out,
    input logic [RADIX-1:0] s_out,
    input logic [RADIX  :0] c_out
);



function logic [2*RADIX :0] add_func( input  logic [RADIX-1:0]  a_in,
    input  logic [RADIX-1:0]  b_in,
    input  logic [RADIX-1:0]  p_in,
    input  logic [RADIX-1:0]  m_in,
    input  logic [RADIX  :0]  c_in,
    input  logic [RADIX-1:0]  s_in
   );

   return((a_in*b_in)+(p_in*m_in)+c_in+s_in);
endfunction



default clocking default_clk @(posedge clk); endclocking

////////////////////////////////////////////////////
// reset or start_in                              //
////////////////////////////////////////////////////

sequence reset_sequence;
  !rst_n || start_in  ##1 rst_n;
endsequence


property reset_p;
$past(!rst_n || start_in)
|->
m_out == 0 &&
a_out == 0 &&
s_out == 0 &&
c_out == 0;
endproperty

reset_a : assert property(reset_p);


////////////////////////////////////////////////////
// aout when odd takes the previous value of ain  //
////////////////////////////////////////////////////

property aout_p;
    odd &&
    !start_in
    |=>
    a_out == $past(a_in);
endproperty

aout_a : assert property(disable iff(!rst_n)aout_p);


////////////////////////////////////////////////////
// mout when odd takes the previous value of min  //
////////////////////////////////////////////////////

property mout_p;
    odd &&
    !start_in
    |=>
    m_out == $past(m_in);
endproperty

mout_a : assert property(disable iff(!rst_n) mout_p);



////////////////////////////////////////////////////////
// aout when even takes the previous value of itself  //
////////////////////////////////////////////////////////
property aout_even_p;
    !odd &&
    !start_in
    |=>
    a_out == $past(a_out);
endproperty

aout_even_a : assert property(disable iff(!rst_n)aout_even_p);



////////////////////////////////////////////////////////
// mout when even takes the previous value of itself  //
////////////////////////////////////////////////////////
property mout_even_p;
    !odd &&
    !start_in
    |=>
    m_out == $past(m_out);
endproperty

mout_even_a : assert property(disable iff(!rst_n) mout_even_p);



////////////////////////////////////////////////////////////
// sout when odd LSB (a_in*b_in)+(p_in*m_in)+c_out+s_in   //
////////////////////////////////////////////////////////////
property sout_odd_p;
logic [2*RADIX :0] temp;
    odd &&
    !start_in
    ##0 (1'b1, temp = add_func(a_in,b_in,p_in,m_in,c_out,s_in))
    |=>
    s_out == temp[RADIX-1:0];
endproperty

sout_odd_a : assert property(disable iff(!rst_n) sout_odd_p);



///////////////////////////////////////////////////////////
// sout when even LSB a_in*b_in)+(p_in*m_in)+c_in+s_out  //
///////////////////////////////////////////////////////////
property sout_even_p;
logic [2*RADIX :0] temp;
    !odd &&
    !start_in
    ##0 (1'b1, temp = add_func(a_in,b_in,p_in,m_in,c_in,s_out))
    |=>
    s_out == temp[RADIX-1:0];
endproperty

sout_even_a : assert property(disable iff(!rst_n) sout_even_p);


////////////////////////////////////////////////////////////
// cout when odd MSB (a_in*b_in)+(p_in*m_in)+c_out+s_in   //
////////////////////////////////////////////////////////////
property cout_odd_p;
logic [2*RADIX :0] temp;
    odd &&
    !start_in
    ##0 (1'b1, temp = add_func(a_in,b_in,p_in,m_in,c_out,s_in))
    |=>
    c_out == temp[2*RADIX:RADIX];
endproperty

cout_odd_a : assert property(disable iff(!rst_n) cout_odd_p);



///////////////////////////////////////////////////////////
// cout when even MSB a_in*b_in)+(p_in*m_in)+c_in+s_out  //
///////////////////////////////////////////////////////////
property cout_even_p;
logic [2*RADIX :0] temp;
    !odd &&
    !start_in
    ##0 (1'b1, temp = add_func(a_in,b_in,p_in,m_in,c_in,s_out))
    |=>
    c_out == temp[2*RADIX:RADIX];
endproperty

cout_even_a : assert property(disable iff(!rst_n) cout_even_p);



endmodule

bind ecc_pe fv_pe #(.RADIX(RADIX))fv_pe_inst(
    .clk(clk),
        .rst_n(reset_n && !zeroize),
        
        .start_in(start_in),
        .a_in(a_in),
        .b_in(b_in),
        .p_in(p_in),
        .m_in(m_in),
        .s_in(s_in),
        .c_in(c_in),
        .odd(odd),
        .a_out(a_out),
        .m_out(m_out),
        .s_out(s_out),
        .c_out(c_out)
        );