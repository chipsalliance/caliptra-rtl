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

module fv_constraints_m
(
    input logic         clk,
    input logic         rst_n,
    input logic         zeroize,
    input logic         hmac_init,
    input logic         hmac_next,
    input logic [383:0] hmac_key
);

    logic fv_hmac_init_reg;

    default clocking default_clk @(posedge clk); endclocking

   
    always @ (posedge clk or negedge rst_n)
        begin
            if (!rst_n || zeroize)
                fv_hmac_init_reg <= 1'h0;
            else if (hmac_init)
                    fv_hmac_init_reg <= 1'h1;
    end
    

    //////////////////////////
    // Assumptions 1
    // hmac_init and hmac_next 
    // cannot be high at same 
    // time.
    /////
    property hmac_init_and_next_not_high_same;
        !(hmac_init && hmac_next);
    endproperty
    assume_hmac_init_and_next_not_high_same: assume property(disable iff(!rst_n)hmac_init_and_next_not_high_same);

    ///////////////////////////
    // Assumptions 2
    // hmac_init should be high 
    // first then next.
    //////
    property hmac_first_init_then_next;
        !fv_hmac_init_reg
    |->
        !hmac_next;
    endproperty
    assume_hmac_first_init_then_next : assume property(disable iff(!rst_n) hmac_first_init_then_next);

    ///////////////////////////
    // Assumptions 3
    // hmac_key must be stable 
    // from the receiving of the
    // key
    /////
    property hmac_key_stable;
    ##1 $stable(hmac_key) || hmac_init;
    endproperty
    assume_key_stable: assume property(disable iff(!rst_n)hmac_key_stable);

    ///////////////////////////
    // Assumptions 4
    // hmac_init must be high
    // unitl ready is high
    assume_init_not_ready: assume property (disable iff (!rst_n) 
        !hmac_core.ready 
    |-> 
        !hmac_init);

    endmodule

  bind hmac_core fv_constraints_m fv_constraints (
        .clk              (clk             ),
        .rst_n            (reset_n         ),
        .zeroize          (zeroize         ),
        .hmac_init        (init_cmd        ),
        .hmac_next        (next_cmd        ),
        .hmac_key         (key             )
    );


