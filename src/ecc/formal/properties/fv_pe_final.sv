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
module fv_pe_final #(
    parameter RADIX = 32
) (
    input  logic              clk,
    input  logic              rst_n,

    input  logic              start_in,
    // DATA PORT
    input  logic [RADIX-1:0]  a_in,
    input  logic [RADIX-1:0]  b_in,
    input  logic [RADIX-1:0]  p_in,
    input  logic [RADIX-1:0]  m_in,
    input  logic [RADIX-1:0]  s_in,
    input  logic [RADIX  :0]  c_in,
    input  logic              odd,

    input logic [RADIX-1:0] s_out,
    input logic [RADIX  :0] c_out
);

default clocking default_clk @(posedge clk); endclocking


sequence reset_sequence;
  !rst_n || start_in ##1 rst_n;
endsequence

property reset_p;
$past(!rst_n || start_in)
|->
s_out == 0 &&
c_out == 0;
endproperty

reset_a : assert property (reset_p);



property s_out_odd_p;
    odd &&
    !start_in
    |=>
    s_out == $past(32'(64'(a_in * b_in) + 64'(p_in * m_in)+ c_out + s_in));
endproperty

s_out_odd_a : assert property (disable iff(!rst_n) s_out_odd_p);




property s_out_noodd_p;

    !odd &&
    !start_in
    |=>
    s_out == $past(32'(64'(a_in * b_in) + 64'(p_in * m_in)+ c_in + s_out));
endproperty

s_out_noodd_a : assert property (disable iff(!rst_n) s_out_noodd_p);




property c_out_odd_p;
logic [2*RADIX : 0] temp;
    odd &&
    !start_in 
   ##0 (1'b1, temp = (64'(a_in * b_in) + 64'(p_in * m_in)+ c_out + s_in))
    |=>
    //c_out == $past(33'((64'(a_in * b_in) + 64'(p_in * m_in)+ c_out + s_in)>>32));
    c_out == temp[2*RADIX:RADIX];
endproperty

c_out_odd_a : assert property (disable iff(!rst_n) c_out_odd_p);




property c_out_noodd_p;
logic [2*RADIX : 0] temp;
    !odd &&
    !start_in
     ##0 (1'b1, temp = (64'(a_in * b_in) + 64'(p_in * m_in)+ c_in + s_out))
    |=>
    //c_out == $past(33'((64'(a_in * b_in) + 64'(p_in * m_in)+ c_in + s_out)>>32));
    c_out == temp[2*RADIX:RADIX];
endproperty

c_out_noodd_a : assert property (disable iff(!rst_n) c_out_noodd_p);

endmodule

bind ecc_pe_final fv_pe_final #(.RADIX(RADIX)) fv_pe_final_inst(
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

        .s_out(s_out),
        .c_out(c_out)
        );
