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

module ecc_reduced_instantiations #(
    parameter REG_SIZE = 48,
    parameter RADIX = 4
)
(
    // Clock and reset.
    input  wire                  clk,
    input  wire                  reset_n,
    input  wire                  zeroize,

    // DATA PORT
    input  wire                  start_i,
    input  wire [REG_SIZE-1:0]   opa_i,
    input  wire [REG_SIZE-1:0]   opb_i,
    input  wire [REG_SIZE-1:0]   n_i,
    input  wire [RADIX-1:0]      n_prime_i, // only need the last few bits
    output logic [REG_SIZE-1:0]  p_o,
    output logic                 ready_o,

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

ecc_montgomerymultiplier #(
        .REG_SIZE(16),
        .RADIX(2)
        )
        ecc_montmult_reduced (
        // Clock and reset.
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
    
        // DATA PORT
        .start_i(start_i),
        .opa_i(opa_i),
        .opb_i(opb_i),
        .n_i(n_i),
        .n_prime_i(n_prime_i), 
        .p_o(p_o),
        .ready_o(ready_o)
    );

ecc_pe_first  #(.RADIX(4)) ecc_pe_first_reduced(
    .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        
        .start_in(start_in),
        .a_in(a_in),
        .b_in(b_in),
        .p_in(p_in),
        .s_in(s_in),
        .n_prime_in(n_prime_in),

        .odd(odd),
        .a_out(a_out),
        .m_out(m_out),

        .c_out(c_out)
        );

    ecc_scalar_blinding #(
        .REG_SIZE(24),
        .RND_SIZE(12),
        .RADIX(2)
    )
    ecc_scalar_blinding_reduced(
        .clk(clk),
        .zeroize(zeroize),
        .reset_n(reset_n),
        .en_i(/* open */),
        .data_i(/* open */),
        .rnd_i(/* open */),
        .data_o(/* open */),
        .busy_o(/* open */)
    );

endmodule


bind ecc_dsa_ctrl ecc_reduced_instantiations ecc_reduced_instantiation_inst (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(ecc_dsa_ctrl.zeroize_reg)
);


