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
// ecc_pe_first.sv
// --------
// first processing element for Montgomery Multiplier based on 
// Optimized Algorithms and Architectures for Montgomery Multiplication
// for Post-quantum Cryptography by Rami Elkhatib et. al.
//
//======================================================================

module ecc_pe_first #(
    parameter RADIX = 32
)
(
    // Clock and reset.
    input  wire              clk,
    input  wire              reset_n,
    input  wire              zeroize,

    input  wire              start_in,
    // DATA PORT
    input  wire [RADIX-1:0]  a_in,
    input  wire [RADIX-1:0]  b_in,
    input  wire [RADIX-1:0]  p_in,
    input  wire [RADIX-1:0]  s_in,
    input  wire [RADIX-1:0]  n_prime_in,
    input  wire              odd,

    output logic [RADIX-1:0] a_out,
    output logic [RADIX-1:0] m_out,
    output logic [RADIX  :0] c_out
);


    //----------------------------------------------------------------
    // ecc_pe_first
    //----------------------------------------------------------------
    logic  [RADIX-1:0]        s_reg;
    logic  [RADIX-1:0]        s_val;
    logic  [RADIX-1:0]        a_reg;
    logic  [RADIX-1:0]        a_val;

    logic  [(2*RADIX)-1 : 0]  mult_out_0;
    logic  [RADIX-1 : 0]      mult_out_0_MSW;
    logic  [RADIX-1 : 0]      mult_out_0_LSW;

    logic  [RADIX   : 0]      res_0;
    logic  [RADIX-1 : 0]      sum_0;
    logic                     carry_0;
    logic  [RADIX-1 : 0]      sum_0_reg;

    logic  [RADIX   : 0]      res_1;
    logic                     carry_1;

    logic  [RADIX   : 0]      c_0;
    logic  [RADIX   : 0]      c_0_reg;
    logic  [RADIX   : 0]      c_1;

    logic  [(2*RADIX)-1 : 0]  mult_out_1;
    logic  [RADIX-1 : 0]      m_temp;
    logic  [RADIX-1 : 0]      m_temp_reg;

    logic  [(2*RADIX)-1 : 0]  mult_out_2;
    logic  [RADIX-1 : 0]      mult_out_2_MSW;
    logic  [RADIX-1 : 0]      mult_out_2_LSW;

    logic                     carry_garbage_bit;

    //----------------------------------------------------------------
    // Module instantiantions.
    //----------------------------------------------------------------
    ecc_mult_dsp #(
        .RADIX(RADIX)
    ) MULT0 (
        .A_i(a_val),
        .B_i(b_in),
        .P_o(mult_out_0)
    );

    ecc_mult_dsp #(
        .RADIX(RADIX)
    ) MULT1 (
        .A_i(n_prime_in),
        .B_i(sum_0),
        .P_o(mult_out_1)
    );

    ecc_mult_dsp #(
        .RADIX(RADIX)
    ) MULT2 (
        .A_i(m_temp_reg),
        .B_i(p_in),
        .P_o(mult_out_2)
    );

    //----------------------------------------------------------------
    // pe_logic
    //
    // The logic needed to update the multiplier inputs.
    //----------------------------------------------------------------
    assign m_temp = mult_out_1[RADIX-1:0];

    assign mult_out_0_MSW = mult_out_0[(2*RADIX)-1 : RADIX];
    assign mult_out_0_LSW = mult_out_0[RADIX-1 : 0];
    assign mult_out_2_MSW = mult_out_2[(2*RADIX)-1 : RADIX];
    assign mult_out_2_LSW = mult_out_2[RADIX-1 : 0];

    assign s_val = odd ? s_in : s_reg;
    assign a_val = odd ? a_in : a_reg;

    always_comb begin
        res_0 = s_val + mult_out_0_LSW;
        sum_0 = res_0[RADIX-1 : 0];
        carry_0 = res_0[RADIX];
    end

    always_comb begin
        res_1 = sum_0_reg + mult_out_2_LSW;
        carry_1 = res_1[RADIX];
    end

    always_comb c_0 = mult_out_0_MSW + carry_0;

    always_comb c_1 = mult_out_2_MSW + carry_1;

    assign {carry_garbage_bit, c_out} = c_0_reg + c_1;

    //----------------------------------------------------------------
    // register updates
    //
    //----------------------------------------------------------------
    always_ff @(posedge clk or negedge reset_n) begin
        if(~reset_n) begin
            c_0_reg <= 'b0;
            sum_0_reg <= 'b0;
            m_temp_reg <= 'b0;
            s_reg <= 'b0;
            a_reg <= 'b0;
        end
        else if (zeroize) begin
            c_0_reg <= 'b0;
            sum_0_reg <= 'b0;
            m_temp_reg <= 'b0;
            s_reg <= 'b0;
            a_reg <= 'b0;
        end
        else if (start_in) begin
            c_0_reg <= 'b0;
            sum_0_reg <= 'b0;
            m_temp_reg <= 'b0;
            s_reg <= 'b0;
            a_reg <= 'b0;
        end else begin
            s_reg <= s_in;
            a_reg <= a_in;
            m_temp_reg <= m_temp;
            c_0_reg <= c_0;
            sum_0_reg <= sum_0;
        end
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (~reset_n) begin
            a_out <= 'b0;
        end
        else if (zeroize) begin
            a_out <= 'b0;
        end
        else if (start_in) begin
            a_out <= 'b0;
        end else begin
            a_out <= a_val;
        end
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (~reset_n) begin
            m_out <= 'b0;
        end
        else if (zeroize) begin
            m_out <= 'b0;
        end
        else if (start_in) begin
            m_out <= 'b0;
        end else begin
            m_out <= m_temp;
        end
    end

endmodule
