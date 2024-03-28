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


`define hiearchy ecc_hmac_drbg_interface 

module fv_ecc_hmac_drbg_interface_m#(
    parameter                  REG_SIZE       = 384,
    parameter [REG_SIZE-1 : 0] GROUP_ORDER    = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973,
    parameter [REG_SIZE-1 : 0]        LFSR_INIT_SEED = 384'hc48555929cd58779f4819c1e6570c2ef20bccd503284e2d366f3273a66e9719b07ac999c80740d6277af88ceb4c3029c   // a random value
    )
    (
    // Clock and reset.
    input wire                      clk,
    input wire                      rst_n,
    input wire                      keygen_sign,
    input wire                      en,
    input wire                     ready,

    //Inputs
    input wire   [REG_SIZE-1 : 0]   keygen_seed,
    input wire   [REG_SIZE-1 : 0]   keygen_nonce,
    input wire   [REG_SIZE-1 : 0]   privKey,
    input wire   [REG_SIZE-1 : 0]   hashed_msg,
    input wire   [REG_SIZE-1 : 0]   IV,

    //Outputs
    input wire  [REG_SIZE-1 : 0]   lambda,
    input wire  [REG_SIZE-1 : 0]   scalar_rnd,
    input wire  [REG_SIZE-1 : 0]   masking_rnd,
    input wire  [REG_SIZE-1 : 0]   drbg
    );

    localparam [3 : 0] IDLE_ST          = 4'd0; 
    localparam [3 : 0] LFSR_ST          = 4'd1;
    localparam [3 : 0] LAMBDA_ST        = 4'd2;
    localparam [3 : 0] SCALAR_RND_ST    = 4'd3;
    localparam [3 : 0] RND_DONE_ST      = 4'd4;
    localparam [3 : 0] MASKING_RND_ST   = 4'd5;
    localparam [3 : 0] KEYGEN_ST        = 4'd6;  
    localparam [3 : 0] SIGN_ST          = 4'd7;  
    localparam [3 : 0] DONE_ST          = 4'd8;  

 default clocking default_clk @(posedge clk); endclocking

        sequence reset_sequence;
          (!rst_n) ##1 rst_n;
        endsequence 

 ///////////////////////////////////////////
 // constraint on hashed msg
 ///////////////////////////////////////////
    hash_msg_less_than_grp_order: assume property(disable iff(!rst_n) hashed_msg < GROUP_ORDER);


 ///////////////////////////////////////////
 // Helper logic for lfsr_seed
 ///////////////////////////////////////////

            logic [383 : 0]         fv_lfsr_seed_reg; 
            logic [383:0]           fv_hmac_drbg_result_reg;
            logic                   fv_hmac_drbg_valid_reg;
        always_ff @(posedge clk, negedge rst_n) begin
            if(!rst_n )
                fv_lfsr_seed_reg <= LFSR_INIT_SEED;
            else begin

                fv_hmac_drbg_valid_reg <= `hiearchy.hmac_drbg_valid;
                fv_hmac_drbg_result_reg <= `hiearchy.hmac_drbg_result;
                 if(`hiearchy.state_reg == LFSR_ST && `hiearchy.hmac_drbg_valid && !fv_hmac_drbg_valid_reg) begin
                    fv_lfsr_seed_reg <= `hiearchy.hmac_drbg_result;
                end
            end
        end


    ///////////////////////////////////////////
    // reset property, when reset all the o/p //
    // are zero                               //
    ////////////////////////////////////////////

        property reset_p;
            $past(!rst_n)  
            |->
            `hiearchy.state_reg == IDLE_ST &&
            lambda      == '0 &&     
            scalar_rnd == '0 &&
            masking_rnd == '0 &&
            drbg == '0 &&
            ready == 1;
        endproperty

        reset_a : assert property(reset_p);


    //State transitioning from idle to lfsr if en and hmac_drbg_ready
        property idle_to_lfsr_p;
            `hiearchy.state_reg == IDLE_ST &&
            (en & `hiearchy.hmac_drbg_ready)
            |=>
            `hiearchy.state_reg == LFSR_ST &&
            `hiearchy.hmac_drbg_init == 1 &&
            `hiearchy.hmac_drbg_next == 0 &&
            `hiearchy.hmac_drbg_entropy == IV &&
            `hiearchy.hmac_lfsr_seed == (fv_lfsr_seed_reg) ^ `hiearchy.counter_nonce &&
            `hiearchy.hmac_drbg_nonce == $past(`hiearchy.counter_nonce) &&
             ready == 0 &&
            lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg);
            

        endproperty

        idle_to_lfsr_a: assert property(disable iff(!rst_n) idle_to_lfsr_p);


        // If en and hmac_drbg isn't ready then stays back in idle state
        property idle_wait_p;
            `hiearchy.state_reg == IDLE_ST &&
            !(en & `hiearchy.hmac_drbg_ready)
            |=>
            `hiearchy.state_reg == IDLE_ST &&
            ready == 1 &&
            `hiearchy.hmac_drbg_init == 0 &&
            `hiearchy.hmac_drbg_next == 0 &&
            `hiearchy.hmac_drbg_entropy == '0 &&
            `hiearchy.hmac_lfsr_seed == (fv_lfsr_seed_reg) ^ `hiearchy.counter_nonce &&
            `hiearchy.hmac_drbg_nonce == (`hiearchy.counter_nonce_reg) &&
            lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg);
        endproperty

        idle_wait_a: assert property(disable iff(!rst_n) idle_wait_p);


    // State transition from lfsr to lambda when hmac_drbg_valid is set
        property lfsr_to_lambda_p;   
            `hiearchy.state_reg== LFSR_ST &&
            $rose(`hiearchy.hmac_drbg_valid)
            |=>
            `hiearchy.state_reg == LAMBDA_ST &&
            `hiearchy.hmac_drbg_init == 0 && 
            `hiearchy.hmac_drbg_next == 1 &&
            `hiearchy.hmac_drbg_entropy == IV &&
            ready == 0 &&
            `hiearchy.hmac_drbg_nonce == `hiearchy.counter_nonce_reg &&
            `hiearchy.hmac_lfsr_seed == $past(`hiearchy.hmac_drbg_result) ^ `hiearchy.counter_nonce &&
            lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg);
        endproperty

         lfsr_to_lambda_a: assert property(disable iff(!rst_n) lfsr_to_lambda_p);


    // If hmac_drbg_valid isn't set then stays back in same state
        property lfsr_wait_p;
            `hiearchy.state_reg == LFSR_ST &&
            !(`hiearchy.hmac_drbg_valid)
            |=> 
            `hiearchy.state_reg == LFSR_ST &&
            `hiearchy.hmac_drbg_init == 0 && 
            `hiearchy.hmac_drbg_next == 0 &&
            `hiearchy.hmac_drbg_entropy == IV &&
            ready == 0 &&
            `hiearchy.hmac_drbg_nonce == `hiearchy.counter_nonce_reg &&
            `hiearchy.hmac_lfsr_seed == (fv_lfsr_seed_reg) ^ `hiearchy.counter_nonce &&
            lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg)
            ;
        endproperty
         lfsr_wait_a: assert property(disable iff(!rst_n) lfsr_wait_p);


    //State transition from lamda to scalar_rnd when hmac_drbg_valid is set
        property lambda_to_scalar_rnd_p;
            `hiearchy.state_reg == LAMBDA_ST &&
            $rose(`hiearchy.hmac_drbg_valid)
            |=>
            `hiearchy.state_reg == SCALAR_RND_ST &&
            `hiearchy.hmac_drbg_init == 0 &&
            `hiearchy.hmac_drbg_next == 1 &&
            `hiearchy.hmac_drbg_entropy == IV &&
            ready == 0 &&
            `hiearchy.hmac_drbg_nonce == `hiearchy.counter_nonce_reg &&
            `hiearchy.hmac_lfsr_seed == fv_lfsr_seed_reg ^ `hiearchy.counter_nonce &&
            lambda == $past(`hiearchy.hmac_drbg_result) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg);
        endproperty

         lambda_to_scalar_rnd_a: assert property(disable iff(!rst_n) lambda_to_scalar_rnd_p);


        //If hmac_drbg_valid isn't set then stays back in same state
        property lambda_wait_p;
            `hiearchy.state_reg == LAMBDA_ST &&
            !(`hiearchy.hmac_drbg_valid) 
            |=> 
            `hiearchy.state_reg == LAMBDA_ST &&
            `hiearchy.hmac_drbg_init == 0 && 
            `hiearchy.hmac_drbg_next == 0 &&
            `hiearchy.hmac_drbg_entropy == IV &&
            ready == 0 &&
            `hiearchy.hmac_drbg_nonce == `hiearchy.counter_nonce_reg &&
            `hiearchy.hmac_lfsr_seed == (fv_lfsr_seed_reg) ^ `hiearchy.counter_nonce &&
            lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg);
        endproperty
         lambda_wait_a: assert property(disable iff(!rst_n) lambda_wait_p);

        
        //State transition from scalar_rnd to rnd_done when hmac_drbg_valid is set
         property scalar_rnd_to_rnd_done_p;
            `hiearchy.state_reg == SCALAR_RND_ST &&
            $rose(`hiearchy.hmac_drbg_valid)
            |=>
            `hiearchy.state_reg == RND_DONE_ST && 
            `hiearchy.hmac_drbg_init == 0 && 
            `hiearchy.hmac_drbg_next == 0 &&
            `hiearchy.hmac_drbg_entropy == '0 &&
            ready == 0 &&
            `hiearchy.hmac_drbg_nonce == `hiearchy.counter_nonce_reg &&
            `hiearchy.hmac_lfsr_seed == (fv_lfsr_seed_reg) ^ `hiearchy.counter_nonce &&
            lambda == $past(lambda) &&
            scalar_rnd == $past(`hiearchy.hmac_drbg_result) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg);
         endproperty
         scalar_rnd_to_rnd_done_a: assert property(disable iff(!rst_n) scalar_rnd_to_rnd_done_p);


        //If hmac_drbg_valid isn't set then stays back in same state
        property scalar_rnd_wait_p;
            `hiearchy.state_reg == SCALAR_RND_ST &&
            !(`hiearchy.hmac_drbg_valid) 

            |=> 
            `hiearchy.state_reg == SCALAR_RND_ST &&
            `hiearchy.hmac_drbg_init == 0 && 
            `hiearchy.hmac_drbg_next == 0 &&
            `hiearchy.hmac_drbg_entropy == IV &&
            ready == 0 &&
            `hiearchy.hmac_drbg_nonce == `hiearchy.counter_nonce_reg &&
            `hiearchy.hmac_lfsr_seed == (fv_lfsr_seed_reg) ^ `hiearchy.counter_nonce &&
            lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg);
        endproperty
        scalar_rnd_wait_a: assert property(disable iff(!rst_n) scalar_rnd_wait_p);


        // if in rnd_done state then if keygen_sign is set then state changes to masking_rnd
        property rnd_done_to_masking_rnd_p;
            `hiearchy.state_reg == RND_DONE_ST &&
            keygen_sign
            |=>
            `hiearchy.state_reg == MASKING_RND_ST &&
            `hiearchy.hmac_drbg_init == 0 &&
            `hiearchy.hmac_drbg_next == 1 &&
            `hiearchy.hmac_drbg_entropy == IV &&
            ready == 0 &&
            `hiearchy.hmac_lfsr_seed == fv_lfsr_seed_reg ^ `hiearchy.counter_nonce &&
            `hiearchy.hmac_drbg_nonce == `hiearchy.counter_nonce_reg &&
             lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg);
        endproperty
         rnd_done_to_masking_rnd_a: assert property(disable iff(!rst_n) rnd_done_to_masking_rnd_p);

        
        // if in rnd_done state then if keygen_sign isn't set then state changes to keygen
         property rnd_done_to_keygen_p;
            `hiearchy.state_reg == RND_DONE_ST &&
            !keygen_sign
            |=>
            `hiearchy.state_reg == KEYGEN_ST &&
            `hiearchy.hmac_drbg_init == 1 &&
            `hiearchy.hmac_drbg_next == 0 &&
            ready == 0 &&
            `hiearchy.hmac_drbg_entropy == keygen_seed &&
            `hiearchy.hmac_lfsr_seed == fv_lfsr_seed_reg ^ `hiearchy.counter_nonce &&
            `hiearchy.hmac_drbg_nonce == keygen_nonce &&
             lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg);
        endproperty
         rnd_done_to_keygen_a: assert property(disable iff(!rst_n) rnd_done_to_keygen_p);


         //State transition from masking_rnd to sign when hmac_drbg_valid is set
        property masking_rnd_to_sign_p;
            `hiearchy.state_reg == MASKING_RND_ST &&
            $rose(`hiearchy.hmac_drbg_valid)
            |=>
            `hiearchy.state_reg == SIGN_ST &&
            `hiearchy.hmac_drbg_init == 1 &&
            `hiearchy.hmac_drbg_next == 0 &&
            `hiearchy.hmac_drbg_entropy == privKey  &&
            ready == 0 &&
            `hiearchy.hmac_drbg_nonce == hashed_msg &&
            `hiearchy.hmac_lfsr_seed == fv_lfsr_seed_reg ^ `hiearchy.counter_nonce &&
            masking_rnd == $past(`hiearchy.hmac_drbg_result) &&
             lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
    
            drbg == $past(drbg);
        endproperty
         masking_rnd_to_sign_a: assert property(disable iff(!rst_n) masking_rnd_to_sign_p);

        //If hmac_drbg_valid isn't set then stays back in same state
        property masking_rnd_wait_p;
             `hiearchy.state_reg == MASKING_RND_ST &&
            !(`hiearchy.hmac_drbg_valid)
            |=>
            `hiearchy.state_reg == MASKING_RND_ST &&
            `hiearchy.hmac_drbg_init == 0 && 
            `hiearchy.hmac_drbg_next == 0 &&
            `hiearchy.hmac_drbg_entropy == IV &&
            ready == 0 &&
            `hiearchy.hmac_drbg_nonce == `hiearchy.counter_nonce_reg &&
            `hiearchy.hmac_lfsr_seed == (fv_lfsr_seed_reg) ^ `hiearchy.counter_nonce &&
            lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg);
        endproperty
        masking_rnd_wait_a: assert property(disable iff(!rst_n) masking_rnd_wait_p);


         //State transition from keygen to done when hmac_drbg_valid is set
         property keygen_to_done_p;
            `hiearchy.state_reg == KEYGEN_ST &&
            $rose(`hiearchy.hmac_drbg_valid)
            |=>
            `hiearchy.state_reg == DONE_ST &&
            `hiearchy.hmac_drbg_init == 0 && 
            `hiearchy.hmac_drbg_next == 0 &&
            `hiearchy.hmac_drbg_entropy == '0 &&
            ready == 0 &&
            `hiearchy.hmac_drbg_nonce == `hiearchy.counter_nonce_reg &&
            `hiearchy.hmac_lfsr_seed == (fv_lfsr_seed_reg) ^ `hiearchy.counter_nonce &&
            lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(`hiearchy.hmac_drbg_result);
        endproperty
        keygen_to_done_a: assert property(disable iff(!rst_n) keygen_to_done_p);

        //If hmac_drbg_valid isn't set then stays back in same state
        property keygen_wait_p;
             `hiearchy.state_reg == KEYGEN_ST &&
            !(`hiearchy.hmac_drbg_valid)
            |=>
            `hiearchy.state_reg == KEYGEN_ST &&
            `hiearchy.hmac_drbg_init == 0 && 
            `hiearchy.hmac_drbg_next == 0 &&
            `hiearchy.hmac_drbg_entropy ==  keygen_seed &&
            ready == 0 &&
            `hiearchy.hmac_drbg_nonce == keygen_nonce &&
            `hiearchy.hmac_lfsr_seed == (fv_lfsr_seed_reg) ^ `hiearchy.counter_nonce &&
            lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg);
        endproperty
         keygen_wait_a: assert property(disable iff(!rst_n) keygen_wait_p);




         //State transition from sign to done when hmac_drbg_valid is set
         property sign_to_done_p;
            `hiearchy.state_reg == SIGN_ST &&
            $rose(`hiearchy.hmac_drbg_valid)
            |=>
            `hiearchy.state_reg == DONE_ST &&
             `hiearchy.hmac_drbg_init == 0 && 
            `hiearchy.hmac_drbg_next == 0 &&
            `hiearchy.hmac_drbg_entropy == '0 &&
            ready == 0 &&
            `hiearchy.hmac_drbg_nonce == `hiearchy.counter_nonce_reg &&
            `hiearchy.hmac_lfsr_seed == (fv_lfsr_seed_reg) ^ `hiearchy.counter_nonce &&
             lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(`hiearchy.hmac_drbg_result);
        endproperty
        sign_to_done_a: assert property(disable iff(!rst_n) sign_to_done_p);


        //If hmac_drbg_valid isn't set then stays back in same state
        property sign_wait_p;
             `hiearchy.state_reg == SIGN_ST &&
            !(`hiearchy.hmac_drbg_valid)
            |=>
            `hiearchy.state_reg == SIGN_ST &&
            `hiearchy.hmac_drbg_init == 0 && 
            `hiearchy.hmac_drbg_next == 0 &&
            `hiearchy.hmac_drbg_entropy == privKey &&
            ready == 0 &&
            `hiearchy.hmac_drbg_nonce == hashed_msg &&
            `hiearchy.hmac_lfsr_seed == (fv_lfsr_seed_reg) ^ `hiearchy.counter_nonce &&
            lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg);
        endproperty
        sign_wait_a: assert property(disable iff(!rst_n) sign_wait_p);



        property done_to_idle_p;
            `hiearchy.state_reg == DONE_ST
            |=>
            `hiearchy.state_reg == IDLE_ST &&
            `hiearchy.hmac_drbg_init == 0 && 
            `hiearchy.hmac_drbg_next == 0 &&
            `hiearchy.hmac_drbg_entropy == '0 &&
            ready == 1 &&
            `hiearchy.hmac_drbg_nonce == `hiearchy.counter_nonce_reg &&
            `hiearchy.hmac_lfsr_seed == (fv_lfsr_seed_reg) ^ `hiearchy.counter_nonce &&
            lambda == $past(lambda) &&
            scalar_rnd == $past(scalar_rnd) &&
            masking_rnd == $past(masking_rnd) &&
            drbg == $past(drbg);
        endproperty
        done_to_idle_a: assert property(disable iff(!rst_n) done_to_idle_p);




    //counter_reg is checked if it adds 1 after everycycle

    // Helper logic for reset reg to use in disable iff
    logic fv_rst_n_reg;
    always_ff @(posedge clk) begin
        fv_rst_n_reg <= rst_n;
    end

        property counter_reg_p;
            `hiearchy.counter_reg == $past(`hiearchy.counter_reg)+1;
        endproperty
        counter_reg_a: assert property(disable iff(!rst_n || !fv_rst_n_reg) counter_reg_p);



        //counter_nonce_reg has counter_nonce onece en is triggered.
        property counter_nonce_reg_p;
            en
            |=>
            `hiearchy.counter_nonce_reg == $past(`hiearchy.counter_nonce);
        endproperty
         counter_nonce_reg_a: assert property(disable iff(!rst_n) counter_nonce_reg_p);

        // counter_nonce_reg stable if no en
         property counter_nonce_reg_stable_p;
            !en
            |=>
            `hiearchy.counter_nonce_reg == $past(`hiearchy.counter_nonce_reg);
        endproperty
         counter_nonce_reg_stable_a: assert property(disable iff(!rst_n) counter_nonce_reg_stable_p);





    //done_edge is a pulse from the hmac_drbg_valid
      property done_pulse_p;
            $rose(`hiearchy.hmac_drbg_valid)
            |->
            `hiearchy.hmac_done_edge 
            ##1
            !`hiearchy.hmac_done_edge;
        endproperty

        done_pulse_a: assert property(disable iff(!rst_n) done_pulse_p);


    // eventually ready==1, once the fsm triggered
        property ready_liveliness_p;
                `hiearchy.state_reg == IDLE_ST &&
                (en & `hiearchy.hmac_drbg_ready)
                |->
                s_eventually(ready);
        endproperty
         ready_liveliness_a: assert property(disable iff(!rst_n) ready_liveliness_p);

endmodule

bind ecc_hmac_drbg_interface fv_ecc_hmac_drbg_interface_m#(
        .REG_SIZE(REG_SIZE),
        .GROUP_ORDER(GROUP_ORDER),
        .LFSR_INIT_SEED(LFSR_INIT_SEED)
        )    
        fv_ecc_hmac_drbg_interface (
        .clk(clk),
        .rst_n(reset_n && !zeroize),
        .keygen_sign(keygen_sign),
        .en(en),
        .ready(ready),
        .keygen_seed(keygen_seed),
        .keygen_nonce(keygen_nonce),
        .privKey(privKey),
        .hashed_msg(hashed_msg),
        .IV(IV),
        .lambda(lambda),
        .scalar_rnd(scalar_rnd),
        .masking_rnd(masking_rnd),
        .drbg(drbg)
        );








             