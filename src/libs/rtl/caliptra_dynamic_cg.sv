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


module caliptra_dynamic_cg (
    input logic clk_i,
    input logic clk_off_i,
    input logic dyn_cg_en_i,
    input logic rst_b_i,
    input logic active_i,

    input logic test_en_i,

    output logic clk_cg_o
);


    logic en;
  
    assign en = !rst_b_i ?  1'b1 :
                clk_off_i ? 1'b0 :
                dyn_cg_en_i ? active_i: 1'b1; 




    `CALIPTRA_ICG caliptra_icg (
        .clk(clk_i),
        .en,
        .clk_cg(clk_cg_o)

    );


endmodule
