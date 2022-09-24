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
// ecc_mult_dsp.sv
// --------
// General multiplier.
//
//
//======================================================================

module ecc_mult_dsp #(
    parameter RADIX = 32
)
(
    // DATA PORT
    input  logic [RADIX-1:0]   A,
    input  logic [RADIX-1:0]   B,
    
    output logic [2*RADIX-1:0] P
);

    always_comb begin
        P = A * B;
    end

endmodule
