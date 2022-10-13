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
// ecc_fixed_msb.sv
// --------
// The Montgomery Ladder algorithm inherently depends on the MSB of the
// scalar. In order to avoid leaking this MSB and fall into HNP (Hidden Number
// Problem) issues, we use the trick described in https://eprint.iacr.org/2011/232.pdf
// to have the MSB always set.
//
// This module takes the scalar and compute (scalar+q) and (scalar+2q)
// output = (scalar+2q) if log(scalar+q)==log(q), otherwise (scalar+q)
//
//
//======================================================================

module ecc_fixed_msb #(
    parameter REG_SIZE     = 384,
    parameter GROUP_ORDER  = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // DATA PORT
    input  wire                  en_i,
    input  wire [REG_SIZE-1 : 0] data_i,
    output wire [REG_SIZE   : 0] data_o
    );

    logic [REG_SIZE   : 0]  data_q;
    logic [REG_SIZE   : 0]  data_q_reg;
    logic [REG_SIZE+1 : 0]  data_2q;
    logic [REG_SIZE+1 : 0]  data_2q_reg;

    always_ff @(posedge clk or negedge reset_n) 
    begin : register_results
        if (!reset_n) begin
            data_q_reg  <= '0;
            data_2q_reg <= '0;
        end
        else if (en_i == 1) begin
            data_q_reg  <= data_q;
            data_2q_reg <= data_2q;
        end
    end //register_results

    // adder to compute scalar + q
    ecc_adder #(
        .N(REG_SIZE)
        ) 
        adder_inst_0(
        .a(data_i),
        .b(GROUP_ORDER),
        .cin(1'b0),
        .s(data_q[REG_SIZE-1 : 0]),
        .cout(data_q[REG_SIZE])
    );

    // adder to compute scalar + 2q
    ecc_adder #(
        .N(REG_SIZE+1)
        ) 
        adder_inst_1(
        .a(data_q_reg),
        .b({1'b0,GROUP_ORDER}),
        .cin(1'b0),
        .s(data_2q[REG_SIZE : 0]),
        .cout(data_2q[REG_SIZE+1])
    );
    
    assign data_o = {1'b0, data_i}; //(data_q_reg[REG_SIZE] == 1'b1)? data_q_reg[REG_SIZE   : 0] : data_2q_reg[REG_SIZE   : 0];

endmodule
