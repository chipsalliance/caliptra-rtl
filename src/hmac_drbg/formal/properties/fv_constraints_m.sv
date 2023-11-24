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
#(
    parameter time_window = 3)
(
    input logic          clk,
    input logic          rst_n,
    input logic          zeroize,
    input logic          next,
    input logic          init,
    input logic          hmac_valid,
    input logic [383:0]  hmac_tag 
);

    logic fv_init_reg;

    default clocking default_clk @(posedge clk); endclocking

   
    always @ (posedge clk or negedge rst_n)
        begin
            if (!rst_n || zeroize)
                fv_init_reg <= 1'h0;
            else if (init)
                    fv_init_reg <= 1'h1;
    end
    
    ///////////////////////////
    /// constraints
    //////////////////////////
    
    
    ///////////////////////////
    // Assumptions 1
    // input nonce and entropy
    // remains stable until
    // valid is high
    /////
    assume_stable_entropy: assume property(disable iff(!rst_n || zeroize)
        ($stable(hmac_drbg.nonce) || hmac_drbg.valid)
    );


    assume_stable_nonce: assume property(disable iff(!rst_n || zeroize)
        ($stable(hmac_drbg.entropy) || hmac_drbg.valid)
    );

    ///////////////////////////
    // Assumptions 2
    // hmac_init and hmac_next 
    // cannot be high at same 
    // time
    /////
    property hmac_init_and_next_not_high_same;
        !(init && next);
    endproperty
    assume_hmac_init_and_next_not_high_same: assume property(disable iff(!rst_n)hmac_init_and_next_not_high_same);

    ///////////////////////////
    // Assumptions 3
    // hmac_init should be high 
    // first then next
    //////
    property hmac_first_init_then_next;
        !fv_init_reg
    |->
        !next;
    endproperty
    assume_hmac_first_init_then_next : assume property(disable iff(!rst_n) hmac_first_init_then_next);

    ///////////////////////////////////
    // Assumptions 4
    // tag remains stable as long 
    // valid is high
    /////
    property sha_digest_stable_when_valid(valid, tag);
        valid 
    |->
        $stable(tag);
    endproperty
    assume_hmac_digest_stable_when_valid : assume property(@(posedge clk) disable iff(!rst_n || zeroize) sha_digest_stable_when_valid(hmac_valid, hmac_tag));
 
    endmodule

  bind hmac_drbg fv_constraints_m fv_constraint (
        .clk              (clk                    ),
        .rst_n            (reset_n                ),
        .zeroize          (zeroize                ),
        .init             (init_cmd               ),
        .next             (next_cmd               ),
        .hmac_valid       (HMAC_tag_valid         ),
        .hmac_tag         (HMAC_tag               ) 
    );