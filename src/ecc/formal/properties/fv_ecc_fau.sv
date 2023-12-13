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
module fv_ecc_fau_m #(
    parameter REG_SIZE      = 384,
    parameter RADIX         = 32
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           rst_n,
    // DATA PORT
    input  wire                 add_en_i,
    input  wire                 sub_i,
    input  wire                 mult_en_i,
    input  wire [REG_SIZE-1:0]  prime_i,
    input  wire [RADIX-1 : 0]   mult_mu_i,
    input  wire [REG_SIZE-1:0]  opa_i,
    input  wire [REG_SIZE-1:0]  opb_i,
    input wire [REG_SIZE-1:0]  add_res_o,
    input wire [REG_SIZE-1:0]  mult_res_o
    );


 default clocking default_clk @(posedge clk); endclocking

        sequence reset_sequence;
          (!rst_n) ##1 rst_n;
        endsequence 


    ///////////////////////////////////////////
    // reset property, when reset all the o/p //
    // are zero                               //
    ////////////////////////////////////////////

        property reset_p;
             $past(!rst_n)  
            |->
        `ifdef TOP
           add_res_o == '0 && //need to be defined on top as at block level open inputs and could take any value being comb
        `endif
           mult_res_o == '0 &&
           ecc_fau.mult_start_edge == '0 &&
           ecc_fau.sub == '0 &&
           ecc_fau.add_start_edge == '0 ;
        endproperty

        reset_a : assert property(reset_p);

    //When ever mult_en_i is triggered, it would just generate one pulse

        property mult_pulse_p;
            $rose(mult_en_i) 
            |=>
            ecc_fau.mult_start_edge 
            ##1
            !ecc_fau.mult_start_edge;
        endproperty

        mult_pulse_a: assert property(disable iff(!rst_n) mult_pulse_p);


    //Once edge triggered from next cycle on it stays out until there is an another mult cmd    
         property no_mult_edge_p;
            ecc_fau.mult_start_edge
            |=>
            !ecc_fau.mult_start_edge s_until_with mult_en_i;
        endproperty
        no_mult_edge_a: assert property(disable iff(!rst_n)no_mult_edge_p);


    //When ever add_en_i is triggered, it would just generate one pulse
         property add_pulse_p;
            $rose(add_en_i)
            |=>
            ecc_fau.add_start_edge 
            ##1
            !ecc_fau.add_start_edge;
        endproperty

        add_pulse_a: assert property(disable iff(!rst_n) add_pulse_p);


    //Once edge triggered from next cycle on it stays out until there is an another add cmd
        property no_add_edge_p;
            ecc_fau.add_start_edge
            |=>
            !ecc_fau.add_start_edge s_until_with add_en_i;
        endproperty
        no_add_edge_a: assert property(disable iff(!rst_n)no_add_edge_p);

     
     //Primary outputs connected to primary outputs of submodules
        property outputs_p;
            mult_res_o  == ecc_fau.mult_res_s &&
            add_res_o == ecc_fau.add_res_s;
        endproperty

        outputs_a: assert property(disable iff(!rst_n) outputs_p);


    //Primary inputs connected to primary inputs of submodules
         property inputs_p;
            ecc_fau.mult_opa  == opa_i &&
            ecc_fau.mult_opb  == opb_i;
        endproperty

        inputs_a: assert property(disable iff(!rst_n) inputs_p);


    //When add and mult ready
        property garbage_ready_p;
            ecc_fau.ready_garbage_bit == (ecc_fau.add_ready_o & ecc_fau.mult_ready_o);
        endproperty
        garbage_ready_a: assert property(disable iff(!rst_n) garbage_ready_p);


    // Always the results should be less than the prime
    `ifdef TOP
    property data_out_prime_p(ready,result);
        (ready)
        |->
        ((result < prime_i)) 
        ;endproperty
    data_out_add_sub_res_prime_a: assert property(disable iff(!rst_n) data_out_prime_p(ecc_fau.add_ready_o,add_res_o));
    data_out_mult_res_prime_a: assert property(disable iff(!rst_n) data_out_prime_p(ecc_fau.mult_ready_o,mult_res_o));
    `endif

endmodule
        bind ecc_fau fv_ecc_fau_m #(
        .REG_SIZE(REG_SIZE),
        .RADIX(RADIX)
        )
        ecc_fau_i
        (
        // Clock and reset.
        .clk(clk),
        .rst_n(reset_n && !zeroize),
       
        // DATA PORT
        .add_en_i(add_en_i),
        .sub_i(sub_i),
        .mult_en_i(mult_en_i),
        .prime_i(prime_i),
        .mult_mu_i(mult_mu_i),
        .opa_i(opa_i),
        .opb_i(opb_i),
        .add_res_o(add_res_o),
        .mult_res_o(mult_res_o)
    );

