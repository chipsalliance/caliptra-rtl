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
module fv_pe_first #(
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
    input  logic [RADIX-1:0]  s_in,
    input  wire [RADIX-1:0]  n_prime_in,
    input  logic              odd,

    input logic [RADIX-1:0] a_out,
    input logic [RADIX-1:0] m_out,
    input logic [RADIX  :0] c_out
);



default clocking default_clk @(posedge clk); endclocking


//////////////////////////////////////////
// m_out_func where it depends on       //
// (s_in+(a_in*b_in)_lsw)*n_prme_in     //
//////////////////////////////////////////

function logic[RADIX-1:0] m_out_func (input logic [RADIX-1:0] a,input logic [RADIX-1:0] b,
input logic [RADIX-1:0] c,input logic [RADIX-1:0] d);
    logic [RADIX-1:0] mult_lsw;
    mult_lsw = b*c;
    mult_lsw = (a+mult_lsw)*d;
    return (mult_lsw);
endfunction


/////////////////////////////////////////////
// c_out_func where it depends on          //
// previous sum(s0), carry(c0) multiplied  //
// with p_in and added(res=m_temp*pin_lsw  //
// carry = msw + res[maxbit] + previous(c0)//
/////////////////////////////////////////////

function logic[RADIX:0] c_out_func (input logic [RADIX-1:0] a,input logic [RADIX-1:0] b,
input logic [RADIX:0] c, input logic [RADIX-1:0] d);

    logic[(2*RADIX)-1:0] mult;
    logic [RADIX:0] res;
    logic [RADIX:0] c1;
    mult = a * b;
    res = d + mult[RADIX-1:0];
    c1 = mult[(2*RADIX)-1:RADIX] + res[RADIX];

return(c1+c);

endfunction

///////////////////////////////////////////////
// c_0 func used for calculating the previous//
// carry used in c_out computation           //
///////////////////////////////////////////////

function logic[RADIX:0] c_0 (input logic [RADIX-1:0] a,input logic [RADIX-1:0] b,
input logic [RADIX-1:0] c);  
    logic[(2*RADIX)-1:0] mult_0;
    logic [RADIX:0] res_0;
    mult_0 = b*c;
    res_0  = a + mult_0[RADIX-1:0];
    return (mult_0[(2*RADIX)-1:RADIX]+res_0[RADIX]);
endfunction


///////////////////////////////////////////////
// m_temp_reg func used for calculating the  //
// previous m_out  in c_out computation      //
///////////////////////////////////////////////

function logic[RADIX-1:0] m_temp_reg (input logic [RADIX-1:0] a,input logic [RADIX-1:0] b,
input logic [RADIX-1:0] c,input logic [RADIX-1:0] d);
    logic [RADIX:0] res_0;

    res_0  = s_0(a,b,c);
    return ((res_0[RADIX-1:0])*d);
endfunction



///////////////////////////////////////////////
// s_0 func used for calculating the previous//
// sum  used in c_out computation           //
///////////////////////////////////////////////
function logic[RADIX-1:0] s_0 (input logic [RADIX-1:0] a,input logic [RADIX-1:0] b,
input logic [RADIX-1:0] c );  
    logic[(2*RADIX)-1:0] mult_0;
    logic [RADIX:0] res_0;
    mult_0 = b*c;
    res_0  = a + mult_0[RADIX-1:0];
    return ((res_0[RADIX-1:0]));
endfunction



sequence reset_sequence;
  !rst_n || start_in ##1 rst_n;
endsequence

//////////////////////////////////////////
//   When in reset carry and the sum,   //
//     array a are zero                 //
//////////////////////////////////////////

property reset_p;
$past(!rst_n || start_in) 
|->
m_out == 0 &&
a_out == 0 &&
c_out == 0;
endproperty

reset_a : assert property(reset_p);



//////////////////////////////////////////
//   When its odd and no start then     //
//  a out takes the previous a_in value //
//////////////////////////////////////////
property aout_p;
    odd &&
    !start_in
    |=>
    a_out == $past(a_in);
endproperty

aout_a : assert property(disable iff(!rst_n)aout_p);


//////////////////////////////////////////
//   When its odd and no start then     //
//  m out takes the computed value      //
//////////////////////////////////////////

property mout_p;
    odd &&
    !start_in
    |=>
    m_out == $past(m_out_func(s_in,a_in,b_in,n_prime_in));
endproperty

mout_a : assert property(disable iff(!rst_n) mout_p);


////////////////////////////////////////////////
//   When its even and no start then          //
//  a out takes the 2cyc previous a_in value  //
////////////////////////////////////////////////
property aout_even_p;
    !start_in
##1
    !odd &&
    !start_in
    |=>
    a_out == $past(a_in,2);
endproperty

aout_even_a : assert property(disable iff(!rst_n)aout_even_p);


//////////////////////////////////////////
//   When its even and no start then     //
//  mout takes the previous mout  value //
//////////////////////////////////////////
property mout_even_p;
    !start_in
 ##1
    !odd &&
    !start_in
    |=>
    m_out == $past(m_out_func($past(s_in),$past(a_in),b_in,n_prime_in),1);
endproperty

mout_even_a : assert property(disable iff(!rst_n) mout_even_p);



//////////////////////////////////////////
//   When its odd and no start then     //
//  cout takes the computed value       //
//  from previous carry sum and computed m //
//////////////////////////////////////////
property cout_odd_p;
logic [RADIX :0] c0;
logic [RADIX-1:0] m_temp;
logic [RADIX-1:0] s0;

    odd &&
    !start_in
    ##0 (1'b1, c0 = c_0(s_in,a_in,b_in))
    ##0 (1'b1, s0 = s_0(s_in,a_in,b_in))
    ##0 (1'b1, m_temp = m_temp_reg(s_in,a_in,b_in,n_prime_in))
    |=>
    c_out == c_out_func(m_temp,p_in,c0,s0);
endproperty

cout_odd_a : assert property(disable iff(!rst_n) cout_odd_p);




/////////////////////////////////////////////
//   When its even and no start then       //
//  cout takes the computed value          //
//  from previous carry sum and computed m //
/////////////////////////////////////////////
property cout_even_p;
logic [RADIX :0] c0;
logic [RADIX-1:0] m_temp;
logic [RADIX-1:0] s0;
    !start_in
    ##1 
    !odd &&
    !start_in
    ##0 (1'b1, c0 = c_0($past(s_in),$past(a_in),b_in))
    ##0 (1'b1, s0 = s_0($past(s_in),$past(a_in),b_in))
    ##0 (1'b1, m_temp = m_temp_reg($past(s_in),$past(a_in),b_in,n_prime_in))
    |=>
    c_out == c_out_func(m_temp,p_in,c0,s0);

endproperty

cout_even_a : assert property(disable iff(!rst_n) cout_even_p);



endmodule

bind ecc_pe_first fv_pe_first #(.RADIX(RADIX)) fv_pe_inst(
    .clk(clk),
        .rst_n(reset_n && !zeroize),
        
        .start_in(start_in),
        .a_in(a_in),
        .b_in(b_in),
        .p_in(p_in),
        .s_in(s_in),
        .n_prime_in(n_prime_in),

        .odd(odd),
        .a_out(a_out),
        .m_out(m_out),

        .c_out(c_out)
        );