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
// 
//
//
//======================================================================

module ecc_adder #(
    parameter N      = 8
)
(
    // DATA PORT
    input  wire [N-1:0]  a,
    input  wire [N-1:0]  b,
    input  wire          cin,
    output wire [N-1:0]  s,
    output wire          cout
);

    logic [N : 0]   s_full;

    always_comb begin
        s_full = {1'b0, a} + {1'b0, b} + cin;
    end
        
    assign s = s_full[N-1 : 0];
    assign cout = s_full[N];

endmodule
