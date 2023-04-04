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
// interface with hmac_drbg component to generate the required values:
// 1) in keygen mode:
//      1.1. generate lambda from IV for point randomization SCA countermeasure
//      1.2. generate scalar_rnd from IV for scalar blinding SCA countermeasure
//      1.3. generate privkey from seed and nonce for key generation
// 2) in sign mode:
//      2.1. generate lambda from IV for point randomization SCA countermeasure
//      2.2. generate scalar_rnd from IV for scalar blinding SCA countermeasure
//      2.3. generate masking_rnd from IV for masking signature SCA countermeasure
//      2.4. generate k from privkey and hashed_msg for signing
//
// To generate random values using IV, the hmac_drbg is continued by trigging 
// next command (instead of init) which increases counter inside hmac_drbg component. 
// It means:
// lambda is generated from IV with counter equal to 0 and 1
// scalar_rnd is generated from IV with counter equal to 2 and 3
// masking_rnd is generated from IV with counter equal to 4 and 5
//
//======================================================================

module ecc_hmac_drbg_interface#(
    parameter                  REG_SIZE       = 384,
    parameter [REG_SIZE-1 : 0] GROUP_ORDER    = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973,
    parameter [147 : 0]        LFSR_INIT_SEED = 148'h6_04E7_A407_54F1_4487_A021_11AC_D0DF_8C55_57A0   // a random value
    )
    (
    // Clock and reset.
    input wire                      clk,
    input wire                      reset_n,
    input wire                      zeroize,
    input wire                      keygen_sign,
    input wire                      en,
    output wire                     ready,

    //Data
    input wire   [REG_SIZE-1 : 0]   keygen_seed,
    input wire   [REG_SIZE-1 : 0]   keygen_nonce,
    input wire   [REG_SIZE-1 : 0]   privKey,
    input wire   [REG_SIZE-1 : 0]   hashed_msg,
    input wire   [REG_SIZE-1 : 0]   IV,

    output wire  [REG_SIZE-1 : 0]   lambda,
    output wire  [REG_SIZE-1 : 0]   scalar_rnd,
    output wire  [REG_SIZE-1 : 0]   masking_rnd,
    output wire  [REG_SIZE-1 : 0]   drbg
    );

    //----------------------------------------------------------------
    // Registers including update variables and write enable.
    //----------------------------------------------------------------
    logic [147 : 0]         lfsr_seed_reg;
    logic [147 : 0]         hmac_lfsr_seed;

    logic                   hmac_mode;
    logic                   hmac_drbg_init;
    logic                   hmac_drbg_next;
    logic                   hmac_drbg_ready;
    logic                   hmac_drbg_valid;
    logic [REG_SIZE-1 : 0]  hmac_drbg_entropy;
    logic [REG_SIZE-1 : 0]  hmac_drbg_nonce;
    logic [REG_SIZE-1 : 0]  hmac_drbg_result;

    logic                   first_round;
    logic [REG_SIZE-1 : 0]  lambda_reg;
    logic [REG_SIZE-1 : 0]  scalar_rnd_reg;
    logic [REG_SIZE-1 : 0]  masking_rnd_reg;
    logic [REG_SIZE-1 : 0]  drbg_reg;
    logic                   hmac_drbg_valid_last;
    logic                   hmac_done_edge;

    logic [63 : 0]          counter_reg;
    logic [REG_SIZE-1 : 0]  counter_nonce;
    logic [REG_SIZE-1 : 0]  counter_nonce_reg;

    /*State register*/
    reg [3 : 0]  state_reg;
    reg [3 : 0]  state_next;
    reg [3 : 0]  state_reg_last;

    /*STATES*/
    localparam [3 : 0] IDLE_ST          = 4'd0; 
    localparam [3 : 0] LFSR_ST          = 4'd1;
    localparam [3 : 0] LAMBDA_ST        = 4'd2;
    localparam [3 : 0] SCALAR_RND_ST    = 4'd3;
    localparam [3 : 0] RND_DONE_ST      = 4'd4;
    localparam [3 : 0] MASKING_RND_ST   = 4'd5;
    localparam [3 : 0] KEYGEN_ST        = 4'd6;  
    localparam [3 : 0] SIGN_ST          = 4'd7;  
    localparam [3 : 0] DONE_ST          = 4'd8;  

    //----------------------------------------------------------------
    // Module instantiantions.
    //----------------------------------------------------------------

    hmac_drbg #(
        .REG_SIZE(REG_SIZE),
        .HMAC_DRBG_PRIME(GROUP_ORDER),
        .LFSR_INIT_SEED(LFSR_INIT_SEED)
        )    
        hmac_drbg_i (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .init_cmd(hmac_drbg_init),
        .next_cmd(hmac_drbg_next),
        .ready(hmac_drbg_ready),
        .valid(hmac_drbg_valid),
        .lfsr_seed(hmac_lfsr_seed),
        .entropy(hmac_drbg_entropy),
        .nonce(hmac_drbg_nonce),
        .drbg(hmac_drbg_result)
        );


    //----------------------------------------------------------------
    // hmac_drbg_interface_logic
    //
    // The logic needed to init as well as update the hmac_drbg commands.
    //----------------------------------------------------------------
    always_comb first_round = (state_reg == state_reg_last)? 1'b0 : 1'b1;
    always_comb hmac_done_edge = hmac_drbg_valid & (!hmac_drbg_valid_last);

    always_comb 
    begin : hmac_drbg_entropy_input
        unique casez (state_reg)
            LFSR_ST:        hmac_drbg_entropy = IV;
            LAMBDA_ST:      hmac_drbg_entropy = IV;
            SCALAR_RND_ST:  hmac_drbg_entropy = IV;
            MASKING_RND_ST: hmac_drbg_entropy = IV;
            KEYGEN_ST:      hmac_drbg_entropy = keygen_seed;
            SIGN_ST:        hmac_drbg_entropy = privKey;
            default:        hmac_drbg_entropy = '0;
        endcase
    end // hmac_drbg_entropy_input

    always_comb 
    begin : hmac_drbg_nonce_input
        unique casez (state_reg)
            LFSR_ST:        hmac_drbg_nonce = counter_nonce_reg;
            LAMBDA_ST:      hmac_drbg_nonce = counter_nonce_reg;
            SCALAR_RND_ST:  hmac_drbg_nonce = counter_nonce_reg;
            MASKING_RND_ST: hmac_drbg_nonce = counter_nonce_reg;
            KEYGEN_ST:      hmac_drbg_nonce = keygen_nonce;
            SIGN_ST:        hmac_drbg_nonce = hashed_msg;
            default:        hmac_drbg_nonce = counter_nonce_reg;
        endcase
    end // hmac_drbg_nonce_input


    always_comb
    begin :hmac_trigger
        hmac_mode = (state_reg == SIGN_ST);
        hmac_drbg_init = 0;
        hmac_drbg_next = 0;
        if (first_round) begin
            unique casez (state_reg)
                LFSR_ST:        hmac_drbg_init = 1;
                LAMBDA_ST:      hmac_drbg_next = 1;
                SCALAR_RND_ST:  hmac_drbg_next = 1;
                MASKING_RND_ST: hmac_drbg_next = 1;
                KEYGEN_ST:      hmac_drbg_init = 1;
                SIGN_ST:        hmac_drbg_init = 1;
                default: begin
                    hmac_drbg_init = 0;
                    hmac_drbg_next = 0;
                end
            endcase
        end
    end //hmac_trigger

    //----------------------------------------------------------------
    // register updates
    //
    // update the internal registers
    //----------------------------------------------------------------
    always_ff @(posedge clk or negedge reset_n) 
    begin //reg_update
        if (!reset_n) begin
            lambda_reg <= '0;
            scalar_rnd_reg <= '0;
            masking_rnd_reg <= '0;
            drbg_reg <= '0;
            lfsr_seed_reg <= LFSR_INIT_SEED;
        end
        else if (zeroize) begin
            lambda_reg <= '0;
            scalar_rnd_reg <= '0;
            masking_rnd_reg <= '0;
            drbg_reg <= '0;
            lfsr_seed_reg <= LFSR_INIT_SEED;
        end
        else
            if (hmac_done_edge) begin
                /* verilator lint_off CASEINCOMPLETE */
                unique case (state_reg) inside
                    LFSR_ST:        lfsr_seed_reg   <= hmac_drbg_result[147 : 0];
                    LAMBDA_ST:      lambda_reg      <= hmac_drbg_result;
                    SCALAR_RND_ST:  scalar_rnd_reg  <= hmac_drbg_result;
                    MASKING_RND_ST: masking_rnd_reg <= hmac_drbg_result;
                    KEYGEN_ST:      drbg_reg        <= hmac_drbg_result;
                    SIGN_ST:        drbg_reg        <= hmac_drbg_result;
                endcase
                /* verilator lint_on CASEINCOMPLETE */
            end
    end //reg_update

    always_ff @(posedge clk or negedge reset_n) 
    begin : state_reg_update
        if (!reset_n)
            state_reg       <= IDLE_ST;
        else if (zeroize)
            state_reg       <= IDLE_ST;
        else
            state_reg       <= state_next;
    end // state_reg_update

    always_ff @(posedge clk or negedge reset_n) 
    begin : ff_state_reg
        if (!reset_n)
            state_reg_last  <= IDLE_ST;
        else if (zeroize)
            state_reg_last  <= IDLE_ST;
        else 
            state_reg_last  <= state_reg;
    end // ff_state_reg

    always_ff @(posedge clk or negedge reset_n) 
    begin : ff_hamc_valid
        if (!reset_n)
            hmac_drbg_valid_last <= '0;
        else if (zeroize)
            hmac_drbg_valid_last <= '0;
        else
            hmac_drbg_valid_last <= hmac_drbg_valid;
    end //ff_hamc_valid

    always_ff @(posedge clk or negedge reset_n) 
    begin : counter_reg_update
        if (!reset_n)
            counter_reg       <= '0;
        else if (zeroize)
            counter_reg       <= '0;
        else
            counter_reg       <= counter_reg + 1;
    end // counter_reg_update

    always_ff @(posedge clk or negedge reset_n) 
    begin : counter_nonce_update
        if (!reset_n)
            counter_nonce_reg       <= '0;
        else if (zeroize)
            counter_nonce_reg       <= '0;
        else if (en) begin
            counter_nonce_reg       <= counter_nonce;
        end
    end // counter_nonce_update

    always_comb counter_nonce[REG_SIZE-1 : 64] = '0;
    always_comb counter_nonce[63 : 0] = counter_reg;
    always_comb hmac_lfsr_seed = lfsr_seed_reg ^ counter_nonce[147 : 0];

    //----------------------------------------------------------------
    // FSM_flow
    //
    // This FSM starts with the en command to perfrom HMAC-DRBG.
    // Active low and async reset.
    //----------------------------------------------------------------
    always_comb 
    begin : interface_fsm
        state_next = IDLE_ST;
        unique casez(state_reg)
            IDLE_ST:        state_next = (en & hmac_drbg_ready)? LFSR_ST : IDLE_ST;
            LFSR_ST:        state_next = (hmac_done_edge)? LAMBDA_ST : LFSR_ST;
            LAMBDA_ST:      state_next = (hmac_done_edge)? SCALAR_RND_ST : LAMBDA_ST;
            SCALAR_RND_ST:  state_next = (hmac_done_edge)? RND_DONE_ST : SCALAR_RND_ST;
            RND_DONE_ST:    state_next = (keygen_sign)? MASKING_RND_ST : KEYGEN_ST;
            MASKING_RND_ST: state_next = (hmac_done_edge)? SIGN_ST : MASKING_RND_ST;
            KEYGEN_ST:      state_next = (hmac_done_edge)? DONE_ST : KEYGEN_ST;
            SIGN_ST:        state_next = (hmac_done_edge)? DONE_ST: SIGN_ST;
            DONE_ST:        state_next = IDLE_ST;
            default:        state_next = IDLE_ST;
        endcase
    end // interface_fsm

    //----------------------------------------------------------------
    // Concurrent connectivity for ports etc.
    //----------------------------------------------------------------
    assign lambda = lambda_reg;
    assign scalar_rnd = scalar_rnd_reg;
    assign masking_rnd = masking_rnd_reg;
    assign drbg = drbg_reg;
    assign ready = (state_reg == IDLE_ST);

endmodule
