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
module fv_montmultiplier_glue #(
    parameter REG_SIZE  = 384,
    parameter RADIX     = 32
)
(
    // Clock and reset.
    input  wire                  clk,
    input  wire                  rst_n,
   

    // DATA PORT
    input  wire                  start_i,
    input  wire [REG_SIZE-1:0]   opa_i,
    input  wire [REG_SIZE-1:0]   opb_i,
    input  wire [REG_SIZE-1:0]   n_i,
    input  wire [RADIX-1:0]      n_prime_i, // only need the last few bits
    input logic [REG_SIZE-1:0]  p_o,
    input logic                 ready_o
);

localparam  int unsigned S_NUM =  ((REG_SIZE + RADIX - 1) / RADIX) + 1; 
localparam  int unsigned FULL_REG_SIZE = S_NUM * RADIX;

localparam  PE_UNITS = ((S_NUM - 1) / 2) - 1;

localparam [(FULL_REG_SIZE-REG_SIZE)-1 : 0]       fv_zero_pad        = '0;

localparam prime_p = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff;
localparam prime_q = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973;
localparam p_mu = 48'h100000001;
localparam q_mu = 48'h6089e88fdc45;
localparam MULT_DLY = 28;
localparam DLY_CONCAT = MULT_DLY - (2*(PE_UNITS+1))-1; //17


/////////////////////////////////////////////////
// Function for selecting o/p                  //
/////////////////////////////////////////////////
function logic[REG_SIZE-1:0] reduction_prime(input logic [FULL_REG_SIZE-1:0] a, input logic [REG_SIZE-1:0] b);
    if(a>=b)
        return(a-b);
    else
        return(a);    
endfunction


default clocking default_clk @(posedge clk); endclocking

// constraint that the multiplication is enable and doesn't trigger until the current computation done
property start_mult_as_p;
    start_i
    |=>
    !start_i until (ready_o);
endproperty
start_mult_as: assume property(disable iff(!rst_n)start_mult_as_p);


// Reset property
sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence

property reset_a;
    reset_sequence
    |->
    p_o == 0 &&
    ready_o == 1;
endproperty

reset_p: assert property(reset_a);



// Bit symbolics used for proof convergence, these define the bit to be checked in proof
logic [8:0] fv_bit_idx_p;
logic [8:0] fv_bit_idx_q;
idx_384_p_assump: assume property(disable iff(!rst_n) fv_bit_idx_p < 384);
idx_384_q_assump: assume property(disable iff(!rst_n) fv_bit_idx_q < 384);



//////////////////////////////////////////////////
// Once the start triggers then after a delay of 28 cycles i.e DLY_CONCAT because to push the whole 
// operand a sequentially would require 26 cycles and 2 extra cycles for valid computation to receive on first box
// from next cycle on as each block of PE works parallely on 2 RADIX elements, next computed value is again on first_box
// later the sequence continues until the last block i.e the carry bits are stored and then reduced by prime
//

property compare_p(prime,idx);
logic [REG_SIZE-1:0] fv_result;
logic [FULL_REG_SIZE-1:0] fv_reg;
    ##0 n_i == prime
    ##0 start_i
    ##DLY_CONCAT
    ##0 (1'b1, fv_reg[RADIX-1:0]    = (ecc_montgomerymultiplier.gen_PE[0].box_i.s_out))
    ##1 (1'b1, fv_reg[2*RADIX-1:RADIX]   = (ecc_montgomerymultiplier.gen_PE[0].box_i.s_out))
    ##1 (1'b1, fv_reg[3*RADIX-1:2*RADIX]   = (ecc_montgomerymultiplier.gen_PE[1].box_i.s_out))
    ##1 (1'b1, fv_reg[4*RADIX-1:3*RADIX]  = (ecc_montgomerymultiplier.gen_PE[1].box_i.s_out))
    ##1 (1'b1, fv_reg[5*RADIX-1:4*RADIX] = (ecc_montgomerymultiplier.gen_PE[2].box_i.s_out))
    ##1 (1'b1, fv_reg[6*RADIX-1:5*RADIX] = (ecc_montgomerymultiplier.gen_PE[2].box_i.s_out))
    ##1 (1'b1, fv_reg[7*RADIX-1:6*RADIX]= (ecc_montgomerymultiplier.final_box.s_out))
    ##1 (1'b1, fv_reg[8*RADIX-1:7*RADIX] = (ecc_montgomerymultiplier.final_box.s_out))
    ##0 (1'b1, fv_reg[9*RADIX-1:8*RADIX] = (ecc_montgomerymultiplier.final_box.c_out[RADIX-1:0]))
    ##0 (1'b1, fv_result = reduction_prime(fv_reg, prime))
    |=>
    ##1
    ready_o &&
    p_o[idx] == fv_result[idx];
endproperty
compare_concat_prime_p_a : assert property ( disable iff(!rst_n) compare_p(prime_p,fv_bit_idx_p));
compare_concat_prime_q_a : assert property ( disable iff(!rst_n) compare_p(prime_q,fv_bit_idx_q));



//a_reg shifts by RADIX, when odd and no start

property when_odd_a_array_shifts_p;
    ecc_montgomerymultiplier.odd &&
    !start_i
    |=>
    ecc_montgomerymultiplier.a_array[0] == RADIX'($past(ecc_montgomerymultiplier.a_reg)>>RADIX) &&
    ecc_montgomerymultiplier.a_reg == ($past(ecc_montgomerymultiplier.a_reg)>>RADIX);
endproperty
when_odd_a_array_shifts_a : assert property ( disable iff(!rst_n) when_odd_a_array_shifts_p);

// a_reg stable if no odd
property when_even_a_array_stable_p;
    !ecc_montgomerymultiplier.odd &&
    !start_i
    |=>
    ecc_montgomerymultiplier.a_array[0] == $past(ecc_montgomerymultiplier.a_array[0]) &&
    ecc_montgomerymultiplier.a_reg == $past(ecc_montgomerymultiplier.a_reg);
endproperty
when_even_a_array_stable_a : assert property ( disable iff(!rst_n) when_even_a_array_stable_p);



// reg's set once start is triggered

    property reg_set_start_p;
        start_i
        |=>
        ecc_montgomerymultiplier.a_reg == {fv_zero_pad, $past(opa_i)} &&
        ecc_montgomerymultiplier.b_reg == {fv_zero_pad, $past(opb_i)} &&
        ecc_montgomerymultiplier.p_reg == {fv_zero_pad, $past(n_i)} &&
        ecc_montgomerymultiplier.n_prime_reg == $past(n_prime_i);
    endproperty
    reg_set_start_a : assert property ( disable iff(!rst_n) reg_set_start_p);

// reg's stay stable if no start cmd
    property reg_no_start_p;
        !start_i
        |=>
        ecc_montgomerymultiplier.b_reg == $past(ecc_montgomerymultiplier.b_reg) &&
        ecc_montgomerymultiplier.p_reg == $past(ecc_montgomerymultiplier.p_reg)  &&
        ecc_montgomerymultiplier.n_prime_reg == $past(ecc_montgomerymultiplier.n_prime_reg);
    endproperty
    reg_no_start_a : assert property ( disable iff(!rst_n) reg_no_start_p);


//b_array and p_array in 64bit takes MSB 32 if odd if not LSB 32

    property when_odd_b_p_array_p(idx);
        ecc_montgomerymultiplier.odd
        |->
        ecc_montgomerymultiplier.b_array[idx] == ecc_montgomerymultiplier.b_reg[(((2*idx)+1)*RADIX)-1 : (2*idx)*RADIX] &&
        ecc_montgomerymultiplier.p_array[idx] == ecc_montgomerymultiplier.p_reg[(((2*idx)+1)*RADIX)-1 : (2*idx)*RADIX];
    endproperty
   
    //b_array and p_array are 64bits takes LSB 32 if even from b_reg and p_reg
    property when_even_b_p_array_p(idx);
        !ecc_montgomerymultiplier.odd
        |->
        ecc_montgomerymultiplier.b_array[idx] == ecc_montgomerymultiplier.b_reg[((2*idx)*RADIX)-1 : ((2*idx)-1)*RADIX] &&
        ecc_montgomerymultiplier.p_array[idx] == ecc_montgomerymultiplier.p_reg[((2*idx)*RADIX)-1 : ((2*idx)-1)*RADIX];
    endproperty

     for (genvar i=1; i < (PE_UNITS+2); i++) begin 
        when_odd_b_p_array_a : assert property ( disable iff(!rst_n) when_odd_b_p_array_p(i));
        when_even_b_p_array_a : assert property ( disable iff(!rst_n) when_even_b_p_array_p(i));
     end


    // connections for the s_in's of the pe blocks
     property s_in_routing_p;
        ecc_montgomerymultiplier.gen_PE[0].box_i.s_in == ecc_montgomerymultiplier.gen_PE[1].box_i.s_out;
    endproperty
    //for (genvar i=0; i < (PE_UNITS); i++) begin 
        s_in_routing_a: assert property (disable iff(!rst_n) s_in_routing_p);
    //end


    // connections for the a_in's of the pe blocks
    property a_in_routing_p;
        ecc_montgomerymultiplier.gen_PE[0].box_i.a_in == ecc_montgomerymultiplier.first_box.a_out;
    endproperty
   
        a_in_routing_a: assert property (disable iff(!rst_n) a_in_routing_p);
   

    // connections for the m_in's,c_in's of the pe blocks
    property m_c_in_routing_p;
        ecc_montgomerymultiplier.gen_PE[0].box_i.m_in == ecc_montgomerymultiplier.first_box.m_out &&
        ecc_montgomerymultiplier.gen_PE[0].box_i.c_in == ecc_montgomerymultiplier.first_box.c_out;
    
    endproperty
    m_c_in_routing_a: assert property (disable iff(!rst_n) m_c_in_routing_p);


endmodule

bind ecc_montgomerymultiplier fv_montmultiplier_glue #(
        .REG_SIZE(REG_SIZE),
        .RADIX(RADIX)
        )
        fv_montmultiplier_glue_inst (
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

