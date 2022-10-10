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
// ecc_hmac_drbg_interface.sv
// --------


module ecc_hmac_drbg_interface#(
    parameter                  REG_SIZE       = 384,
    parameter                  SEED_SIZE      = 384,
    parameter [REG_SIZE-1 : 0] GROUP_ORDER    = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
    )
    (
    // Clock and reset.
    input wire                      clk,
    input wire                      reset_n,
    input wire                      keygen_sign,
    input wire                      en,
    output wire                     ready,

    //Data
    input wire   [SEED_SIZE-1 : 0]  seed,
    input wire   [REG_SIZE-1 : 0]   privKey,
    input wire   [SEED_SIZE-1 : 0]  IV,
    input wire   [REG_SIZE-1 : 0]   hashed_msg,

    output wire  [REG_SIZE-1 : 0]   lambda,
    output wire  [REG_SIZE-1 : 0]   scalar_rnd,
    output wire  [REG_SIZE-1 : 0]   masking_rnd,
    output wire  [REG_SIZE-1 : 0]   nonce
    );

    //----------------------------------------------------------------
    // Registers including update variables and write enable.
    //----------------------------------------------------------------

    logic                   hmac_mode;
    logic                   hmac_init;
    logic                   hmac_next;
    logic                   hmac_ready;
    logic                   hmac_valid;
    logic [SEED_SIZE-1 : 0] hmac_seed;
    logic [REG_SIZE-1 : 0]  hmac_nonce;

    logic                   first_round;
    logic [REG_SIZE-1 : 0]  lambda_reg;
    logic [REG_SIZE-1 : 0]  scalar_rnd_reg;
    logic [REG_SIZE-1 : 0]  masking_rnd_reg;
    logic [REG_SIZE-1 : 0]  nonce_reg;
    logic                   ready_reg;
    logic                   hmac_valid_last;
    logic                   hmac_valid_edge;

    /*State register*/
    reg [2 : 0]  state_reg;
    reg [2 : 0]  state_next;
    reg [2 : 0]  state_reg_last;

    /*STATES*/
    localparam IDLE_ST          = 0; 
    localparam LAMBDA_ST        = 1;
    localparam SCALAR_RND_ST    = 2;
    localparam MASKING_RND_ST   = 3;
    localparam KEYGEN_ST        = 4;  
    localparam SIGN_ST          = 5;  
    localparam DONE_ST          = 6;  

    //----------------------------------------------------------------
    // Module instantiantions.
    //----------------------------------------------------------------

    hmac_drbg #(
        .REG_SIZE(REG_SIZE),
        .SEED_SIZE(SEED_SIZE),
        .HMAC_DRBG_PRIME(GROUP_ORDER)
        )    
        hmac_drbg_i (
        .clk(clk),
        .reset_n(reset_n),
        .mode(hmac_mode),
        .init_cmd(hmac_init),
        .next_cmd(hmac_next),
        .ready(hmac_ready),
        .valid(hmac_valid),
        .seed(hmac_seed),
        .privkey(privKey),
        .hashed_msg(hashed_msg),
        .nonce(hmac_nonce)
        );


    //----------------------------------------------------------------
    // FSM_flow
    //
    // This FSM starts with the init command and then generates a nonce.
    // Active low and async reset.
    //----------------------------------------------------------------

    always_comb
    begin
        first_round = (state_reg == state_reg_last)? 1'b0 : 1'b1;
        hmac_valid_edge = hmac_valid & (!hmac_valid_last);
    end

    always_ff @(posedge clk) 
    begin
        hmac_valid_last <= hmac_valid;
    end

    always_comb 
    begin : hmac_drbg_seed
        hmac_seed = '0;
        case(state_reg)
            LAMBDA_ST:      hmac_seed = IV;
            SCALAR_RND_ST:  hmac_seed = IV;
            MASKING_RND_ST: hmac_seed = IV;
            KEYGEN_ST:      hmac_seed = seed;
        endcase
    end // hmac_drbg_seed

    always_comb
    begin
        hmac_mode = (state_reg == SIGN_ST);
        hmac_init = 0;
        hmac_next = 0;
        if (first_round) begin
            case(state_reg)
                LAMBDA_ST:      hmac_init = 1;
                SCALAR_RND_ST:  hmac_next = 1;
                MASKING_RND_ST: hmac_next = 1;
                KEYGEN_ST:      hmac_init = 1;
                SIGN_ST:        hmac_init = 1;
            endcase
        end
    end

    always_comb
    begin
        if (!reset_n)
            ready_reg   = 0; 
        else
            ready_reg   = (state_reg == IDLE_ST);
    end

    always_ff @(posedge clk) 
    begin
        if (!reset_n) begin
            lambda_reg <= '0;
            scalar_rnd_reg <= '0;
            masking_rnd_reg <= '0;
            nonce_reg <= '0;
        end
        else
        if (hmac_valid_edge) begin
            case(state_reg)
                LAMBDA_ST:      lambda_reg <= hmac_nonce;
                SCALAR_RND_ST:  scalar_rnd_reg <= hmac_nonce;
                MASKING_RND_ST: masking_rnd_reg <= hmac_nonce;
                KEYGEN_ST:      nonce_reg <= hmac_nonce;
                SIGN_ST:        nonce_reg <= hmac_nonce;
            endcase
        end
    end

    always_ff @(posedge clk) 
    begin : state_reg_update
        if (!reset_n)
            state_reg       <= IDLE_ST;
        else
            state_reg       <= state_next;
    end // state_reg_update

    always_ff @(posedge clk) 
    begin : ff_state_reg
        if (!reset_n)
            state_reg_last  <= IDLE_ST;
        else 
            state_reg_last  <= state_reg;
    end // ff_state_reg

    always_comb 
    begin : interface_fsm
        if (!reset_n)
            state_next    = IDLE_ST;
        else
        begin
            state_next = IDLE_ST;
            case(state_reg)
                IDLE_ST: begin
                    if (en & hmac_ready) begin
                        state_next = LAMBDA_ST;
                    end
                end

                LAMBDA_ST: begin
                    if (hmac_valid_edge)
                        state_next    = SCALAR_RND_ST;
                    else
                        state_next    = LAMBDA_ST;
                end

                SCALAR_RND_ST: begin
                    if (hmac_valid_edge) begin
                        if (keygen_sign)
                            state_next    = MASKING_RND_ST;
                        else
                            state_next    = KEYGEN_ST;
                    end
                    else
                        state_next    = SCALAR_RND_ST;
                end

                MASKING_RND_ST: begin
                    if (hmac_valid_edge)
                        state_next    = SIGN_ST;
                    else
                        state_next    = MASKING_RND_ST;
                end

                KEYGEN_ST: begin
                    if (hmac_valid_edge)
                        state_next    = DONE_ST;
                    else
                        state_next    = KEYGEN_ST;
                end

                SIGN_ST: begin
                    if (hmac_valid_edge)
                        state_next    = DONE_ST;
                    else
                        state_next    = SIGN_ST;
                end

                DONE_ST: begin
                    state_next    = IDLE_ST;
                end
            endcase
        end
    end // interface_fsm

    assign lambda = lambda_reg;
    assign scalar_rnd = scalar_rnd_reg;
    assign masking_rnd = masking_rnd_reg;
    assign nonce = nonce_reg;
    assign ready = ready_reg;

endmodule