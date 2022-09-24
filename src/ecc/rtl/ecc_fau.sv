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
// ecc_fau.sv
// --------
// ECC Finite field Arithmetic Unit including Montgomery Multiplier and Adder
//
//
//======================================================================

module ecc_fau #(
    parameter REG_SIZE      = 384,
    parameter RADIX         = 32,
    parameter ADD_NUM_ADDS  = 1,
    parameter ADD_BASE_SZ   = 384
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // DATA PORT
    input  wire                 sub_i,
    input  wire                 red_i,
    input  wire                 mult_start_i,
    input  wire [REG_SIZE-1:0]  prime_i,
    input  wire [RADIX-1 : 0]   mult_mu_i,
    input  wire [REG_SIZE-1:0]  opa_i,
    input  wire [REG_SIZE-1:0]  opb_i,
    output wire [REG_SIZE-1:0]  add_res_o,
    output wire [REG_SIZE-1:0]  mult_res_o,
    output wire                 ready_o
    );

    logic [REG_SIZE-1 : 0]  mult_res_s;
    logic [REG_SIZE-1 : 0]  mult_opa;
    logic [REG_SIZE-1 : 0]  mult_opb;
    logic                   mult_ready;
    logic [REG_SIZE-1 : 0]  add_res_s;
    logic                   add_ready;
    
    reg                     mult_start;
    reg                     mult_start_dly;
    wire                    mult_start_edge;
    reg                     sub;
    reg                     red;

    assign mult_opa = opa_i;
    assign mult_opb = opb_i;

    //----------------------------------------------------------------
    // MULTIPILER
    //----------------------------------------------------------------
    ecc_montgomerymultiplier #(
        .REG_SIZE(REG_SIZE),
        .RADIX(RADIX)
        )
        i_MULTIPLIER (
        // Clock and reset.
        .clk(clk),
        .reset_n(reset_n),

        // DATA PORT
        .start_i(mult_start_edge),
        .opa_i(mult_opa),
        .opb_i(mult_opb),
        .n_i(prime_i),
        .n_prime_i(mult_mu_i), // only need the last few bits
        .p_o(mult_res_s),
        .ready_o(mult_ready)
    );


    //----------------------------------------------------------------
    // ADDER/SUBTRACTOR
    //----------------------------------------------------------------
    ecc_add_sub_mod_alter #(
        .REG_SIZE(REG_SIZE),
        .NUM_ADDS(ADD_NUM_ADDS),
        .BASE_SZ(ADD_BASE_SZ)
        )
        i_ADDER_SUBTRACTOR (
        .clk(clk),
        .reset_n(reset_n),

        .red_i(red),
        .sub_i(sub),
        .opa_i(opa_i),
        .opb_i(opb_i),
        .prime_i(prime_i),
        .res_o(add_res_s),
        .ready_o(add_ready)
        );


    always_ff @(posedge clk) begin
            mult_start <= mult_start_i;
            mult_start_dly <= mult_start;
            sub <= sub_i;
            red <= red_i;
    end
    
    assign mult_start_edge = mult_start & ~mult_start_dly;
    assign mult_res_o = mult_res_s;
    assign add_res_o  = add_res_s;

endmodule
