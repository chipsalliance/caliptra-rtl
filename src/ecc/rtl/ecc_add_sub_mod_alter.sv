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
//======================================================================
//
// ecc_add_sub_mod_alter.sv
// --------
// modular addtion/subtraction module to compute opa+-opb % prime
//
//
//======================================================================

module ecc_add_sub_mod_alter #(
    parameter REG_SIZE      = 384,
    parameter NUM_ADDS      = 1,
    parameter BASE_SZ       = 384
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // DATA PORT
    input  wire                 sub_i,
    input  wire  [REG_SIZE-1:0] opa_i,
    input  wire  [REG_SIZE-1:0] opb_i,
    input  wire  [REG_SIZE-1:0] prime_i,
    output logic [REG_SIZE-1:0] res_o,
    output wire                 ready_o
);
  
    logic [REG_SIZE-1 : 0] opb0;
    logic [REG_SIZE-1 : 0] opb1;
    logic [REG_SIZE   : 0] result;
    logic [REG_SIZE   : 0] c;
    logic [REG_SIZE-1 : 0] r0;
    logic [REG_SIZE-1 : 0] r1;
    logic                  add_nsub;
    logic                  carry0;

    assign opb0 = sub_i ? ~opb_i : opb_i;
    assign opb1 = sub_i ? prime_i : ~prime_i;

    ecc_adder #(
        .N(REG_SIZE)
        ) 
        adder_inst_0(
        .a(opa_i),
        .b(opb0),
        .cin(sub_i),
        .s(r0),
        .cout(carry0)
    );

    ecc_adder #(
        .N(REG_SIZE)
        ) 
        adder_inst_1(
        .a(r0),
        .b(opb1),
        .cin(~sub_i),
        .s(r1),
        .cout()
    );

    assign res_o = (~sub_i ^ carry0)? r0 : r1;
    
endmodule
