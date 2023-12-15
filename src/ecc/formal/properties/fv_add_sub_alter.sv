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
module fv_add_sub_alter_m(
  input bit rst_n,
  input bit clk,
  input bit unsigned [383:0] opa_i,
  input bit unsigned [383:0] opb_i,
  input bit unsigned [383:0] prime_i,
  input bit add_en_i,
  input bit sub_en_i,
  input bit unsigned [383:0] res_o,
  input bit ready_o
);

function logic[383:0] neg_mod (input logic[383:0] a,input logic[383:0] b,input logic[383:0] c);
logic[383:0] d;
  if(a<b) begin
      d = (a-b)+c;
  end
  else if(a==b)
    d = 0;
  else
    d = (a-b);
  return(d);
endfunction


default clocking default_clk @(posedge clk); endclocking

sequence reset_sequence;
  !rst_n  ##1 rst_n;
endsequence


reset_a: assert property (reset_p);
property reset_p;
  $past(!rst_n) |->
  res_o == 0 &&
  ready_o == 0;
endproperty




///////////////////////////////////////////////////////////
// Property to check (a-b)%c, where the case it holds is //
// when we have add_en pulse,sub_i for 3 cycles          //
///////////////////////////////////////////////////////////



sub_a: assert property (disable iff(!rst_n) sub_p);
property sub_p;
logic [383:0] fv_result;
  ##0 add_en_i && sub_en_i 
  ##0 (1'b1, fv_result = neg_mod(opa_i,opb_i,prime_i))
|->
  ##2
  (res_o== fv_result) && 
  (res_o < prime_i) &&
  ready_o  
  ;
endproperty


///////////////////////////////////////////////////////////
// Property to check (a+b)%c, where the case it holds is //
// when we have add_en pulse,no sub_en_i for 3 cycles    //
///////////////////////////////////////////////////////////




add_a: assert property (disable iff(!rst_n) add_p);
property add_p;
logic [383:0] fv_result; 
  ##0 add_en_i && !sub_en_i 
  ##0 (1'b1, fv_result = ((385'(opa_i + opb_i)%prime_i)))                            
|->
  ##2
  res_o== fv_result && 
  (res_o < prime_i) &&
  ready_o 
 ;
endproperty


///////////////////////////////////////////////////////////////
// Property to check the if there isn't any cmd for 2        //
// consecutive cycles then the res would have previous value //
// and ready should be deasserted
///////////////////////////////////////////////////////////////



no_cmd_a: assert property (disable iff(!rst_n) no_cmd_p);
property no_cmd_p;
  !(add_en_i || sub_en_i)
  ##1
  !(add_en_i || sub_en_i)
|=>
  //res_o== $past(res_o) &&
  ready_o == 0
;
endproperty


endmodule



bind ecc_add_sub_mod_alter fv_add_sub_alter_m fv_add_sub_alter(
  .rst_n(reset_n && !zeroize),
  .clk(clk),
  .opa_i(opa_i),
  .opb_i(opb_i),
  .prime_i(prime_i),
  .add_en_i(add_en_i),
  .sub_en_i(sub_i),
  .res_o(res_o),
  .ready_o(ready_o)
);
