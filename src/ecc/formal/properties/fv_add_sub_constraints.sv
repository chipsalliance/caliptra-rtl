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
module fv_add_sub_constraints (
    input logic clk,
    input logic rst_n,

    input logic add_en_i,
    input logic sub_i,
    input logic[383:0] prime_i,
    input logic[383:0] opa_i,
    input logic[383:0] opb_i

);

default clocking default_clk @(posedge clk); endclocking
//--------------------------------//
// Can be any of the 2 primes     //
//--------------------------------//

prime_as_p_q: assume property((prime_i==384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973) || (prime_i==384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff) );

//--------------------------------------//
// stable operands once cmd initiated   //
//--------------------------------------//

stable_operands: assume property(add_en_i |-> ((opa_i < prime_i) && (opb_i < prime_i) ##1($stable(opa_i) && $stable(opb_i) && $stable(prime_i))[*2]));


//----------------------------------------------//
// cmd sequence:                                //
// if add then no add and sub for next 2 cycles //
// if sub then no add but sub for next 2 cycles //
//----------------------------------------------//

if_add_then_cmd_is_pulse: assume property(add_en_i && !sub_i|=> (!add_en_i && !sub_i )[*2]);
if_sub_then_stays_for_2cycles: assume property(add_en_i && sub_i |=> (!add_en_i && sub_i )[*2]);


//---------------------------------------------//
// Inputs zero during reset                    //
//----------------------------------------------//

inputs_zero_during_reset: assume property($past(!rst_n) |-> opa_i==0 && opb_i==0 && !add_en_i && !sub_i);

endmodule
bind ecc_add_sub_mod_alter fv_add_sub_constraints fv_constraints_m (
    .clk(clk),
    .rst_n(reset_n && !zeroize),
    .add_en_i(add_en_i),
    .sub_i(sub_i),
    .prime_i(prime_i),
    .opa_i(opa_i),
    .opb_i(opb_i)
);