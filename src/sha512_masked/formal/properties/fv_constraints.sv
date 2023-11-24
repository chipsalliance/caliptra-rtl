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

module fv_constraints_m(
    input logic            init_cmd, 
    input logic            next_cmd, 
    input logic            reset_n, 
    input logic            clk, 
    input logic            zeroize, 
    input logic            ready, 
    input logic            digest_valid,
    input logic [1023 : 0] block_msg,
    input logic [73   : 0] lfsr_seed,
    input logic [511  : 0] digest,
    input logic [1    : 0] mode
    );

    default clocking default_clk @(posedge clk); endclocking
    
    logic fv_init_reg;

    always @ (posedge clk or negedge reset_n)
    begin : init_reg_order
        if (!reset_n || zeroize)
            fv_init_reg <= 1'b0;
        else if (init_cmd)
            fv_init_reg <= 1'b1;
    end
    

    property mode_values;
        (sha512_masked_core.mode == 0) || 
        (sha512_masked_core.mode == 1) || 
        (sha512_masked_core.mode == 2) || 
        (sha512_masked_core.mode == 3);
    endproperty
    assume_mode_values: assume property (disable iff(!reset_n || zeroize) mode_values);

    property inputs_stay_stable;
        !(sha512_masked_core.ready) |-> $stable(block_msg) && $stable(sha512_masked_core.mode);
    endproperty
    assume_inputs_stay_stable: assume property (disable iff(!reset_n || zeroize) inputs_stay_stable);
    
    property remove_init_next_together;
        !(init_cmd && next_cmd);
    endproperty
    assume_remove_init_next_together: assume property (disable iff(!reset_n || zeroize) remove_init_next_together);

    property init_next_order;
        !fv_init_reg |-> !next_cmd;
    endproperty
    assume_init_next_order: assume property (disable iff(!reset_n || zeroize) init_next_order);


endmodule

bind sha512_masked_core fv_constraints_m fv_constraints(
  .init_cmd(init_cmd),
  .next_cmd(next_cmd),
  .reset_n(reset_n),
  .ready(ready),
  .digest_valid(digest_valid),
  .clk(clk),
  .mode(mode),
  .block_msg(block_msg),
  .zeroize(zeroize),
  .lfsr_seed(lfsr_seed),
  .digest(digest)
);
