
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
module fv_scalar_blind_m #(
  parameter REG_SIZE = 384,
  parameter RND_SIZE = 192,
  parameter RADIX    = 32
)(
  input bit rst_n,
  input bit clk,
  input bit unsigned [(RND_SIZE-1):0] rnd_i,
  input bit unsigned [(REG_SIZE+RND_SIZE-1):0] data_o,
  input bit unsigned [(REG_SIZE-1):0] data_i,
  input logic [REG_SIZE-1:0] group_order,
  input bit en_i,
  input bit busy_o,
  input bit input_read
);

localparam SCA_DLY = 110; // The delay for computing the result




//Helper function for computation
function bit unsigned [(REG_SIZE+RND_SIZE-1):0] randomize(bit unsigned [(REG_SIZE-1):0] scalar, bit unsigned [(RND_SIZE-1):0] random, bit unsigned [REG_SIZE-1:0] grp_order);
  return (REG_SIZE+RND_SIZE)'((scalar + (REG_SIZE+RND_SIZE)'(random * grp_order)));
endfunction

default clocking default_clk @(posedge clk); endclocking

sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence

//no enable until the busy stays deasserted
assume_enb: assume property (disable iff(!rst_n) 
  en_i
  |=>
  !en_i until_with (!busy_o) //check: no strong as it deasserts busy_o
  );

//Input data is always less than group order
assume_scalr_less_group_order: assume property (disable iff(!rst_n)
  data_i < group_order
);




//when reset busy_o and data_o is zero
reset_a: assert property (reset_p);
property reset_p;
  $past(!rst_n) |->
  input_read &&
  data_o == '0 &&
  busy_o == 0
;endproperty


//If not busy and en is set then the computation is carried out
input_read_to_input_read_a: assert property (disable iff(!rst_n) input_read_to_input_read_p);
property input_read_to_input_read_p;
  logic [(REG_SIZE-1):0] scalar_store;
  logic [(RND_SIZE-1):0] random_store;
  logic [(REG_SIZE+RND_SIZE-1):0] temp;
  
  input_read &&
  en_i 
  ##0 (1'b1, scalar_store = data_i) 
  ##0 (1'b1, random_store = rnd_i)
  ##0 (1'b1, temp = randomize(data_i,rnd_i,group_order))
|->
  ##1 busy_o[*SCA_DLY] 
  ##1  (input_read  &&
  data_o ==  temp &&
  busy_o == 0)
;endproperty



// If not busy and not enabled then it stays in not busy
input_read_wait_a: assert property (disable iff(!rst_n) input_read_wait_p);
property input_read_wait_p;
  input_read &&
  !en_i
|->
  ##1
  input_read &&
  busy_o == 0
;endproperty


//If not busy and enabled then busy is set
input_read_next_a: assert property (disable iff(!rst_n) input_read_next_p);
property input_read_next_p;
  input_read &&
  en_i
|->
  ##1
  !input_read &&
  busy_o == 1
;endproperty

endmodule



bind ecc_scalar_blinding fv_scalar_blind_m  #(
  .REG_SIZE(REG_SIZE),
  .RND_SIZE(RND_SIZE),
  .RADIX(RADIX)
  )fv_scalar_blind(
  .rst_n(ecc_scalar_blinding.reset_n && !ecc_scalar_blinding.zeroize),
  .clk(ecc_scalar_blinding.clk),
  .rnd_i(ecc_scalar_blinding.rnd_i),
  .data_o(ecc_scalar_blinding.data_o),
  .data_i(ecc_scalar_blinding.data_i),
  .en_i(ecc_scalar_blinding.en_i),
  .busy_o(ecc_scalar_blinding.busy_o),
  .input_read(!ecc_scalar_blinding.busy_o),
  .group_order(ecc_scalar_blinding.GROUP_ORDER)
  
);
