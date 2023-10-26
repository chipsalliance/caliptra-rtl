
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

module fv_constraints( init, next, reset_n, clk, mode);
    input bit  init, next, reset_n, clk, mode;
    reg init_reg;

    default clocking default_clk @(posedge clk); endclocking
    remove_int_next_together_a: assume property (remove_int_next_together);
    property remove_int_next_together;
        !(init && next);
    endproperty

    int_next_order_a: assume property (int_next_order);
    property int_next_order;
        !init_reg |-> !next;
    endproperty



    always @ (posedge clk or negedge reset_n)
        begin : init_reg_order
            if (!reset_n)
                init_reg <= 1'b0;
            else if (init)
                init_reg <= 1'b1;
        end

endmodule

bind sha256_core fv_constraints inst2(
  .init(init_cmd),
  .next(next_cmd),
  .reset_n(reset_n),
  .clk(clk),
  .mode(mode)
);