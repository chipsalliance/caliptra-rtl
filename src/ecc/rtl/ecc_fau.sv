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
    parameter RADIX         = 32
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,
    input wire           zeroize,

    // DATA PORT
    input  wire                 add_en_i,
    input  wire                 sub_i,
    input  wire                 mult_en_i,
    input  wire [REG_SIZE-1:0]  prime_i,
    input  wire [RADIX-1 : 0]   mult_mu_i,
    input  wire [REG_SIZE-1:0]  opa_i,
    input  wire [REG_SIZE-1:0]  opb_i,
    output wire [REG_SIZE-1:0]  add_res_o,
    output wire [REG_SIZE-1:0]  mult_res_o
    );

    logic [REG_SIZE-1 : 0]  mult_res_s;
    logic [REG_SIZE-1 : 0]  mult_opa;
    logic [REG_SIZE-1 : 0]  mult_opb;
    logic [REG_SIZE-1 : 0]  add_res_s;
    
    reg                     mult_start;
    reg                     mult_start_dly;
    wire                    mult_start_edge;
    logic                   add_start;
    logic                   add_start_dly;
    logic                   add_start_edge;   
    reg                     sub;

    logic                   add_ready_o;
    logic                   mult_ready_o;

    logic                   ready_garbage_bit;

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
        .zeroize(zeroize),

        // DATA PORT
        .start_i(mult_start_edge),
        .opa_i(mult_opa),
        .opb_i(mult_opb),
        .n_i(prime_i),
        .n_prime_i(mult_mu_i), // only need the last few bits
        .p_o(mult_res_s),
        .ready_o(mult_ready_o)
    );


    //----------------------------------------------------------------
    // ADDER/SUBTRACTOR
    //----------------------------------------------------------------
    ecc_add_sub_mod_alter #(
        .REG_SIZE(REG_SIZE)
        )
        i_ADDER_SUBTRACTOR (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),

        .add_en_i(add_start_edge),
        .sub_i(sub),
        .opa_i(opa_i),
        .opb_i(opb_i),
        .prime_i(prime_i),
        .res_o(add_res_s),
        .ready_o(add_ready_o)
        );


    //----------------------------------------------------------------
    // Registers including update enables.
    //----------------------------------------------------------------
    always_ff @(posedge clk or negedge reset_n) 
    begin
        if (!reset_n) begin
            mult_start <= '0;
            add_start <= '0;
            sub <= '0;
        end
        else if (zeroize) begin
            mult_start <= '0;
            add_start <= '0;
            sub <= '0;
        end
        else begin
            mult_start <= mult_en_i;
            add_start <= add_en_i;
            sub <= sub_i;
        end
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mult_start_dly <= '0;
            add_start_dly  <= '0;
        end
        else if (zeroize) begin
            mult_start_dly <= '0;
            add_start_dly  <= '0;
        end
        else begin
            mult_start_dly <= mult_start;
            add_start_dly  <= add_start;
        end
    end
    
    assign ready_garbage_bit = add_ready_o & mult_ready_o;
    
    // generate a pulse enable for mult
    assign mult_start_edge = mult_start & ~mult_start_dly;
    assign add_start_edge  = add_start  & ~add_start_dly;

    //----------------------------------------------------------------
    // Concurrent connectivity for ports etc.
    //----------------------------------------------------------------
    assign mult_res_o = mult_res_s;
    assign add_res_o  = add_res_s;

endmodule
