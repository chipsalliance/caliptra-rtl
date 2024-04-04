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
module fv_montmultiplier #(
    parameter REG_SIZE  = 384,
    parameter RADIX     = 32
)
(
    // Clock and reset.
    input  logic                  clk,
    input  logic                  rst_n,

    // DATA PORT
    input  logic                  start_i,
    input  logic [REG_SIZE-1:0]   opa_i,
    input  logic [REG_SIZE-1:0]   opb_i,
    input  logic [REG_SIZE-1:0]   n_i,
    input  logic [RADIX-1:0]      n_prime_i, // only need the last few bits
    input logic [REG_SIZE-1:0]  p_o,
    input logic                 ready_o
);

default clocking default_clk @(posedge clk); endclocking


//-------------------------------------------------------//
//R = 2^((ceil(bits(n_i)/RADIX)+1)*RADIX)
//R^(-1) = R invmod n_i;
//localparam R = 417'h100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
//localparam R_inv = 355'h0600000014000000140000000C00000002FFFFFFFCFFFFFFFAFFFFFFFBFFFFFFF7FFFFFFE5FFFFFFD8FFFFFFE7; 
//-------------------------------------------------------//


localparam MULT_DLY = 28; // Defines after start how many cycles ready would stay deasserted.


localparam  int unsigned S_NUM =  ((REG_SIZE + RADIX - 1) / RADIX) + 1; 
localparam  int unsigned FULL_REG_SIZE = S_NUM * RADIX;
   
localparam  PE_UNITS = ((S_NUM - 1) / 2) - 1;


function logic[ REG_SIZE-1:0] montmult (logic[ REG_SIZE-1:0] a, logic[ REG_SIZE-1:0] b, logic[ REG_SIZE-1:0] c, logic[ REG_SIZE-1:0] d);
    return ((1152'(768'(a*b)*c)%d));
endfunction



sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence

property reset_p;
     $past(!rst_n) 
    |->
    p_o == 0 &&
    ready_o == 1;
endproperty

reset_a: assert property(reset_p);


////////////////////////////////////////////
// start_i triggers only after multi done //
///////////////////////////////////////////
start_mult_as: assume property(disable iff(!rst_n)start_mult_as_p);

property start_mult_as_p;
    start_i
    |=>
    !start_i until (ready_o);
endproperty

mult_operands_less_than_prime: assume property(disable iff(!rst_n) mult_operands_less_than_prime_p);

property mult_operands_less_than_prime_p;
    start_i
    |->
    opa_i < n_i &&
    opb_i < n_i ;
endproperty



`ifndef FOR48


/////////////////////////////////////////////////
// Property for 16 bit to prove the computation//
////////////////////////////////////////////////

/********For inp value less than 4 bits ******/
property multi_0_p(prime_i, mu_i,r_inv);
    logic [REG_SIZE-1:0] temp; 
    n_i == prime_i &&
    n_prime_i == mu_i && 
    opa_i <= 4'hf &&
    opb_i <= 4'hf &&
    start_i
    ##0 (1'b1, temp = (48'(32'(opa_i*opb_i)*r_inv)%n_i)) 
    ##1 ready_o[->1]  
    |->
    
    p_o == temp; 
endproperty
   


/********For inp value less than 8 bits ******/
property multi_1_p(prime_i, mu_i,r_inv);
    logic [REG_SIZE-1:0] temp; 
    n_i == prime_i &&
    n_prime_i == mu_i && 
    opa_i <= 8'hff &&
    opb_i <= 8'hff &&
    opa_i > 4'hf &&
    opb_i > 4'hf &&
     start_i
    ##0 (1'b1, temp = (48'(32'(opa_i*opb_i)*r_inv)%n_i))  
     ##1 ready_o[->1]  
    |->
    
    p_o == temp; 
endproperty
    


/********For inp value less than 12 bits ******/
property multi_2_p(prime_i, mu_i,r_inv);
    logic [REG_SIZE-1:0] temp; 
    n_i == prime_i &&
    n_prime_i == mu_i && 
    opa_i <= 12'hfff &&
    opb_i <= 12'hfff &&
    opa_i > 8'hff &&
    opb_i > 8'hff &&
     start_i
    ##0 (1'b1, temp = (48'(32'(opa_i*opb_i)*r_inv)%n_i))  
    ##1 ready_o[->1]  
    |->
    
    p_o == temp; 
endproperty
/********For inp value all bits ******/
property multi_p(prime_i, mu_i,r_inv);
    logic [REG_SIZE-1:0] temp; 
    n_i == prime_i &&
    n_prime_i == mu_i &&
    start_i
    ##0 (1'b1, temp = (48'(32'(opa_i*opb_i)*r_inv)%n_i))  
    
    ##1 ready_o[->1]  
    |->
    
    p_o == temp; 
endproperty

logic [4:0][REG_SIZE-1:0] prime;
logic [4:0][RADIX-1:0] mu_word;
logic [4:0][REG_SIZE-1:0] rinv;
assign prime ={16'hfceb,16'hfcfb,16'hfd0d,16'hfd0f,16'hfd19};
assign mu_word = {2'd1,2'd1,2'd3,2'd1,2'd3};
assign rinv ={16'hce7,16'h92b3,16'h38e5,16'h6a48,16'h3b87};

genvar i;
for(i=0;i<5;i++) begin
    multi_a: assert property(disable iff (!rst_n) multi_p(prime[i], mu_word[i],rinv[i]));
    multi_2_a: assert property(disable iff (!rst_n) multi_2_p(prime[i], mu_word[i],rinv[i]));
    multi_1_a: assert property(disable iff (!rst_n) multi_1_p(prime[i], mu_word[i],rinv[i]));
    multi_0_a: assert property(disable iff (!rst_n) multi_0_p(prime[i], mu_word[i],rinv[i]));
end


/////////////////////////////////////////////////
// Property for ready deassert                 //
////////////////////////////////////////////////

property no_ready_p;
    start_i
    |=>
    !ready_o[*MULT_DLY-1];
endproperty

no_ready_a: assert property(disable iff(!rst_n)no_ready_p);


//-------------------------------------------------------------------------------------------------//
//                                  For 48 bit operands                                            //
//-------------------------------------------------------------------------------------------------//


`else


/********For inp value all bits ******/
property multi_p(prime_i, mu_i,r_inv);
    logic [REG_SIZE-1:0] temp; 
    n_i == prime_i &&
    n_prime_i == mu_i &&
    start_i
    ##0 (1'b1, temp = (144'(96'(opa_i*opb_i)*r_inv)%n_i))
    //##0 (1'b1, temp = ((1152'(768'(opa_i*opb_i)*r_inv)%n_i)))
    ##1 ready_o[->1]  
    |->
    
    p_o == temp; 
endproperty


logic [4:0][REG_SIZE-1:0] prime;
logic [4:0][RADIX-1:0] mu_word;
logic [4:0][REG_SIZE-1:0] rinv;
assign prime ={48'hffffffffff9f,48'hffffffffffb3,48'hffffffffffbf,48'hffffffffffc9,48'hffffffffffd5};
assign mu_word = {4'h1,4'h5,4'h1,4'h7,4'h3};
assign rinv ={48'h1fd5c5f02a2e,48'h3ce213f2b376,48'h1fc0fc0fc0f4,48'h686fb586fb42,48'h30be82fa0be0};


genvar i;
for(i=0;i<5;i++) begin
    multi_a: assert property(disable iff (!rst_n) multi_p(prime[i], mu_word[i],rinv[i]));
    end

/////////////////////////////////////////////////
// Property for ready deassert                 //
////////////////////////////////////////////////

property no_ready_p;
    start_i 
    |=>
    !ready_o[*(MULT_DLY-1)];
endproperty

no_ready_a: assert property(disable iff(!rst_n)no_ready_p);

`endif
endmodule

bind ecc_montgomerymultiplier fv_montmultiplier #(
        .REG_SIZE(REG_SIZE),
        .RADIX(RADIX)
        )
        fv_montmultiplier_inst (
        // Clock and reset.
        .clk(clk),
        .rst_n(reset_n && !zeroize),
    
        // DATA PORT
        .start_i(start_i),
        .opa_i(opa_i),
        .opb_i(opb_i),
        .n_i(n_i),
        .n_prime_i(n_prime_i), // only need the last few bits
        .p_o(p_o),
        .ready_o(ready_o)
    );