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
// ecc_adder.sv
// --------
// Full adder module to compute a + b in RADIX bits and output add result
// with carry    
//
//
//======================================================================

module ecc_adder #(
    parameter RADIX          = 8
)
(
    // DATA PORT
    input  wire [RADIX-1:0]  a_i,
    input  wire [RADIX-1:0]  b_i,
    input  wire              cin_i,
    output wire [RADIX-1:0]  s_o,
    output wire              cout_o
);

    logic [RADIX : 0]   s_full;

    always_comb begin
        s_full = a_i + b_i + cin_i;
    end
        
    assign s_o = s_full[RADIX-1 : 0];
    assign cout_o = s_full[RADIX];

endmodule
