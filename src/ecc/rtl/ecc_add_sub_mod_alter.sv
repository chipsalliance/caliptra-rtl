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
    parameter REG_SIZE      = 384
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // DATA PORT
    input  wire                 add_en_i,
    input  wire                 sub_i,
    input  wire  [REG_SIZE-1:0] opa_i,
    input  wire  [REG_SIZE-1:0] opb_i,
    input  wire  [REG_SIZE-1:0] prime_i,
    output logic [REG_SIZE-1:0] res_o,
    output logic                ready_o
);
  
    logic [REG_SIZE-1 : 0] opb0;
    logic [REG_SIZE-1 : 0] opb1;
    logic [REG_SIZE-1 : 0] r0;
    logic [REG_SIZE-1 : 0] r1;
    logic                  carry0; 

    logic                  sub_n;
    logic [REG_SIZE-1 : 0] r0_reg;
    logic                  carry0_reg;

    logic                   carry_garbage_bit;

    ecc_adder #(
        .RADIX(REG_SIZE)
        ) 
        adder_inst_0(
        .a_i(opa_i),
        .b_i(opb0),
        .cin_i(sub_i),
        .s_o(r0),
        .cout_o(carry0)
    );

    ecc_adder #(
        .RADIX(REG_SIZE)
        ) 
        adder_inst_1(
        .a_i(r0_reg),
        .b_i(opb1),
        .cin_i(sub_n),
        .s_o(r1),
        .cout_o(carry_garbage_bit)
    );


    assign sub_n = !sub_i;
    assign opb0 = sub_i ? ~opb_i : opb_i;
    assign opb1 = sub_i ? prime_i : ~prime_i;

    always_ff @(posedge clk or negedge reset_n) 
    begin
        if(!reset_n) begin
            r0_reg <= '0;
            carry0_reg <= '0;
            ready_o <= 1'b0;
        end
        else if (add_en_i) begin 
            r0_reg <= r0;
            carry0_reg <= carry0;
            ready_o <= 1'b0;
        end
        else
            ready_o <= 1'b1;
    end

    assign res_o = (sub_n ^ carry0_reg)? r0 : r1;
    
endmodule
