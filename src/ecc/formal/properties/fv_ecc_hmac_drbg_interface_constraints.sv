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
module fv_ecc_hmac_drbg_interface_constraints_m #(
    parameter time_window = 3)(
    input logic clk,
    input logic rst_n,
    input logic hmac_drbg_ready,
    input logic hmac_drbg_init,
    input logic hmac_drbg_next,
    input logic hmac_drbg_valid,
    input logic [383:0] counter_nonce
);

default clocking default_clk @(posedge clk); endclocking



property hmac_drbg_ready_after_reset(hmac_drbg_ready);
            (!rst_n)
        |=> 
            hmac_drbg_ready;
    endproperty
assume_hmac_drbg_ready_after_reset : assume property(@(posedge clk) hmac_drbg_ready_after_reset(hmac_drbg_ready));

 sequence idletonext(hmac_drbg_ready, hmac_drbg_init, hmac_drbg_next);
        hmac_drbg_ready &&
        (hmac_drbg_init || hmac_drbg_next);
    endsequence
    
 property hmac_drbg_not_ready(hmac_drbg_ready, hmac_drbg_init, hmac_drbg_next,time_window); 
            idletonext(hmac_drbg_ready, hmac_drbg_init, hmac_drbg_next)
        |=> 
            !hmac_drbg_ready[*time_window] 
        ##1 
            hmac_drbg_ready;
    endproperty
    assume_hmac_drbg_not_ready : assume property(@(posedge clk)disable iff(!rst_n ) hmac_drbg_not_ready(hmac_drbg_ready, hmac_drbg_init, hmac_drbg_next,time_window));
    

    property hmac_drbg_result_then_ready(hmac_drbg_valid, hmac_drbg_ready);
            hmac_drbg_valid 
        |-> 
            hmac_drbg_ready;
    endproperty
    assume_hmac_drbg_result_then_ready : assume property(@(posedge clk) hmac_drbg_result_then_ready(hmac_drbg_valid, hmac_drbg_ready));
    

    property for_init(hmac_drbg_init, hmac_drbg_next, hmac_drbg_valid, time_window);
        hmac_drbg_init || hmac_drbg_next
    |->
        ##(time_window+1) 
        hmac_drbg_valid;
    endproperty
    assume_hmac_drbg_valid_after_init_next : assume property(@(posedge clk)disable iff(!rst_n ) for_init(hmac_drbg_init, hmac_drbg_next, hmac_drbg_valid, time_window));
    

    property for_valid(hmac_drbg_valid, hmac_drbg_init, hmac_drbg_next);    
        hmac_drbg_valid &&
        !(hmac_drbg_init || hmac_drbg_next)
    |=>
        hmac_drbg_valid;
    endproperty
    assume_hmac_drbg_valid_continous : assume property(@(posedge clk)disable iff(!rst_n ) for_valid(hmac_drbg_valid, hmac_drbg_init, hmac_drbg_next));
    
    property hmac_drbg_ready_until_init_next(hmac_drbg_ready, hmac_drbg_init, hmac_drbg_next);
	hmac_drbg_ready &&
	(hmac_drbg_init || hmac_drbg_next)
    |=>
	!hmac_drbg_ready
;endproperty 
    assume_hmac_drbg_ready_until_init_next : assume property ( @(posedge clk) disable iff(!rst_n ) hmac_drbg_ready_until_init_next(hmac_drbg_ready, hmac_drbg_init, hmac_drbg_next));
    

    property hmac_drbg_valid_zero_in_all_state(hmac_drbg_valid, hmac_drbg_init, hmac_drbg_next,time_window);  
        !hmac_drbg_valid && 
        (hmac_drbg_init || hmac_drbg_next) 
    |=> 
        !hmac_drbg_valid[*time_window] 
        ##1 
        hmac_drbg_valid;
    endproperty
    assume_hmac_drbg_valid_zero_in_all_states : assume property (@(posedge clk) disable iff(!rst_n ) hmac_drbg_valid_zero_in_all_state(hmac_drbg_valid, hmac_drbg_init, hmac_drbg_init, time_window));
    

    assume_cntr_nonce_only_64bit: assume property(@(posedge clk) disable iff(!rst_n ) counter_nonce <= 64'hffffffffffffffff);

endmodule

bind ecc_hmac_drbg_interface fv_ecc_hmac_drbg_interface_constraints_m fv_ecc_hmac_drbg_interface_constraints (
    .clk(clk),
    .rst_n(reset_n && !zeroize),
    .hmac_drbg_init(ecc_hmac_drbg_interface.hmac_drbg_init),
    .hmac_drbg_next(ecc_hmac_drbg_interface.hmac_drbg_next),
    .hmac_drbg_ready(ecc_hmac_drbg_interface.hmac_drbg_ready),
    .hmac_drbg_valid(ecc_hmac_drbg_interface.hmac_drbg_valid),
    .counter_nonce(ecc_hmac_drbg_interface.counter_nonce)
);