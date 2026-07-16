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
// ecc_hmac_drbg_p256_wrap.sv
// --------------------------
// P-256 HMAC-DRBG interface wrapper.
//
// This file is the P-256 counterpart of ecc_hmac_drbg_interface.sv
// (P-384). It exposes the identical port shape at REG_SIZE=256 width
// so that ecc_dsa_ctrl can instantiate the two curves symmetrically.
//
// Generates the four cryptographic randoms ECC needs:
//   - lambda      : projective point randomization
//   - scalar_rnd  : scalar-blinding randomness
//   - masking_rnd : signature masking (SIGN only)
//   - drbg        : private scalar (KEYGEN) / k (SIGN)
//
// FSM mirrors ecc_hmac_drbg_interface.sv exactly. The only structural
// difference is the underlying primitive: this wrapper drives
// `hmac_drbg_sha256` (HMAC-SHA-256, no lfsr_seed port) instead of
// `hmac_drbg` (HMAC-SHA-384, takes lfsr_seed).
//
//======================================================================

module ecc_hmac_drbg_p256_wrap #(
    parameter                  REG_SIZE     = 256,
    parameter [REG_SIZE-1 : 0] GROUP_ORDER  = 256'hFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
    )
    (
    input  wire                     clk,
    input  wire                     reset_n,
    input  wire                     zeroize,
    input  wire  [1 : 0]            hmac_mode,
    input  wire                     en,
    output wire                     ready,

    input  wire  [REG_SIZE-1 : 0]   keygen_seed,
    input  wire  [REG_SIZE-1 : 0]   keygen_nonce,
    input  wire  [REG_SIZE-1 : 0]   privKey,
    input  wire  [REG_SIZE-1 : 0]   hashed_msg,
    input  wire  [REG_SIZE-1 : 0]   IV,
    input  wire                     nondet,

    output wire  [REG_SIZE-1 : 0]   lambda,
    output wire  [REG_SIZE-1 : 0]   scalar_rnd,
    output wire  [REG_SIZE-1 : 0]   masking_rnd,
    output wire  [REG_SIZE-1 : 0]   drbg
    );

    //----------------------------------------------------------------
    // Local declarations.
    //----------------------------------------------------------------
    logic [REG_SIZE-1 : 0]  lfsr_seed_reg;
    logic [REG_SIZE-1 : 0]  hmac_lfsr_seed;

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
    logic [REG_SIZE-1 : 0]  sign_nonce_reg;
    logic                   hmac_drbg_valid_last;
    logic                   hmac_done_edge;

    logic [63 : 0]          counter_reg;
    logic [REG_SIZE-1 : 0]  counter_nonce;
    logic [REG_SIZE-1 : 0]  counter_nonce_reg;
    logic [REG_SIZE-1 : 0]  sca_entropy, sca_entropy_reg;

    localparam [1 : 0] KEYGEN_CMD    = 2'b00;
    localparam [1 : 0] SIGN_CMD      = 2'b01;
    localparam [1 : 0] DH_SHARED_CMD = 2'b10;

    reg [3 : 0]  state_reg;
    reg [3 : 0]  state_next;
    reg [3 : 0]  state_reg_last;

    localparam [3 : 0] IDLE_ST        = 4'd0;
    localparam [3 : 0] LFSR_ST        = 4'd1;
    localparam [3 : 0] LAMBDA_ST      = 4'd2;
    localparam [3 : 0] SCALAR_RND_ST  = 4'd3;
    localparam [3 : 0] RND_DONE_ST    = 4'd4;
    localparam [3 : 0] MASKING_RND_ST = 4'd5;
    localparam [3 : 0] KEYGEN_ST      = 4'd6;
    localparam [3 : 0] SIGN_ST        = 4'd7;
    localparam [3 : 0] DONE_ST        = 4'd8;
    localparam [3 : 0] SIGN_NONCE_ST  = 4'd9;

    //----------------------------------------------------------------
    // P-256 HMAC-DRBG primitive instantiation.
    //----------------------------------------------------------------
    hmac_drbg_sha256 #(
        .REG_SIZE(REG_SIZE),
        .HMAC_DRBG_PRIME(GROUP_ORDER)
        )
        u_drbg_sha256 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .init_cmd(hmac_drbg_init),
        .next_cmd(hmac_drbg_next),
        .ready(hmac_drbg_ready),
        .valid(hmac_drbg_valid),
        .entropy(hmac_drbg_entropy),
        .nonce(hmac_drbg_nonce),
        .drbg(hmac_drbg_result)
        );

    //----------------------------------------------------------------
    // LFSR-based SCA entropy whitening (same as P-384 interface).
    //----------------------------------------------------------------
    genvar i;
    generate
        for (i = 0; i < (REG_SIZE/32); i++) begin : gen_lfsr
            caliptra_prim_lfsr #(
                .LfsrType("FIB_XNOR"),
                .LfsrDw(32),
                .StateOutDw(32)
            ) caliptra_prim_lfsr_inst_i (
                .clk_i(clk),
                .rst_ni(reset_n),
                .seed_en_i(hmac_drbg_init),
                .seed_i(sca_entropy[i*32 +: 32]),
                .lfsr_en_i(1'b1),
                .entropy_i('0),
                .state_o(hmac_lfsr_seed[i*32 +: 32])
            );
        end
    endgenerate

    //----------------------------------------------------------------
    // hmac_drbg_interface_logic
    //----------------------------------------------------------------
    always_comb first_round = (state_reg == state_reg_last) ? 1'b0 : 1'b1;
    always_comb hmac_done_edge = hmac_drbg_valid & (!hmac_drbg_valid_last);

    always_comb begin : hmac_drbg_entropy_input
        unique case (state_reg)
            LFSR_ST:        hmac_drbg_entropy = sca_entropy_reg;
            LAMBDA_ST:      hmac_drbg_entropy = sca_entropy_reg;
            SCALAR_RND_ST:  hmac_drbg_entropy = sca_entropy_reg;
            MASKING_RND_ST: hmac_drbg_entropy = sca_entropy_reg;
            SIGN_NONCE_ST:  hmac_drbg_entropy = sca_entropy_reg;
            KEYGEN_ST:      hmac_drbg_entropy = keygen_seed;
            SIGN_ST:        hmac_drbg_entropy = nondet ? keygen_seed : privKey;
            default:        hmac_drbg_entropy = sca_entropy_reg;
        endcase
    end

    always_comb begin : hmac_drbg_nonce_input
        unique case (state_reg)
            LFSR_ST:        hmac_drbg_nonce = counter_nonce_reg;
            LAMBDA_ST:      hmac_drbg_nonce = counter_nonce_reg;
            SCALAR_RND_ST:  hmac_drbg_nonce = counter_nonce_reg;
            MASKING_RND_ST: hmac_drbg_nonce = counter_nonce_reg;
            SIGN_NONCE_ST:  hmac_drbg_nonce = counter_nonce_reg;
            KEYGEN_ST:      hmac_drbg_nonce = keygen_nonce;
            SIGN_ST:        hmac_drbg_nonce = nondet ? sign_nonce_reg : hashed_msg;
            default:        hmac_drbg_nonce = counter_nonce_reg;
        endcase
    end

    always_comb begin : hmac_trigger
        hmac_drbg_init = 1'b0;
        hmac_drbg_next = 1'b0;
        if (first_round) begin
            unique case (state_reg)
                LFSR_ST:        hmac_drbg_init = 1'b1;
                LAMBDA_ST:      hmac_drbg_next = 1'b1;
                SCALAR_RND_ST:  hmac_drbg_next = 1'b1;
                MASKING_RND_ST: hmac_drbg_next = 1'b1;
                SIGN_NONCE_ST:  hmac_drbg_next = 1'b1;
                KEYGEN_ST:      hmac_drbg_init = 1'b1;
                SIGN_ST:        hmac_drbg_init = 1'b1;
                default: begin
                    hmac_drbg_init = 1'b0;
                    hmac_drbg_next = 1'b0;
                end
            endcase
        end
    end

    //----------------------------------------------------------------
    // register updates
    //----------------------------------------------------------------
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            lambda_reg      <= '0;
            scalar_rnd_reg  <= '0;
            masking_rnd_reg <= '0;
            drbg_reg        <= '0;
            lfsr_seed_reg   <= '0;
            sign_nonce_reg  <= '0;
        end
        else if (zeroize) begin
            lambda_reg      <= '0;
            scalar_rnd_reg  <= '0;
            masking_rnd_reg <= '0;
            drbg_reg        <= '0;
            sign_nonce_reg  <= '0;
        end
        else if (hmac_done_edge) begin
            unique case (state_reg) inside
                LFSR_ST:        lfsr_seed_reg   <= hmac_drbg_result;
                LAMBDA_ST:      lambda_reg      <= hmac_drbg_result;
                SCALAR_RND_ST:  scalar_rnd_reg  <= hmac_drbg_result;
                MASKING_RND_ST: masking_rnd_reg <= hmac_drbg_result;
                SIGN_NONCE_ST:  sign_nonce_reg  <= hmac_drbg_result;
                KEYGEN_ST:      drbg_reg        <= hmac_drbg_result;
                SIGN_ST:        drbg_reg        <= hmac_drbg_result;
                default: begin
                    lambda_reg      <= '0;
                    scalar_rnd_reg  <= '0;
                    masking_rnd_reg <= '0;
                    drbg_reg        <= '0;
                end
            endcase
        end
    end

    always_ff @(posedge clk or negedge reset_n) begin : state_reg_update
        if (!reset_n)         state_reg <= IDLE_ST;
        else if (zeroize)     state_reg <= IDLE_ST;
        else                  state_reg <= state_next;
    end

    always_ff @(posedge clk or negedge reset_n) begin : ff_state_reg
        if (!reset_n)         state_reg_last <= IDLE_ST;
        else if (zeroize)     state_reg_last <= IDLE_ST;
        else                  state_reg_last <= state_reg;
    end

    always_ff @(posedge clk or negedge reset_n) begin : ff_hmac_valid
        if (!reset_n)         hmac_drbg_valid_last <= '0;
        else if (zeroize)     hmac_drbg_valid_last <= '0;
        else                  hmac_drbg_valid_last <= hmac_drbg_valid;
    end

    always_ff @(posedge clk or negedge reset_n) begin : counter_reg_update
        if (!reset_n) counter_reg <= '0;
        else          counter_reg <= counter_reg + 1;
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            counter_nonce_reg <= '0;
            sca_entropy_reg   <= '0;
        end else if (en && (state_reg == IDLE_ST)) begin
            counter_nonce_reg <= counter_nonce;
            sca_entropy_reg   <= sca_entropy;
        end
    end

    // counter_nonce: replicate counter_reg across REG_SIZE bits.
    // (P-384 wrapper packs 6 copies for 384b; P-256 packs 4 copies for 256b.)
    always_comb begin
        for (int j = 0; j < (REG_SIZE/64); j++)
            counter_nonce[j*64 +: 64] = counter_reg;
    end
    always_comb sca_entropy = IV ^ lfsr_seed_reg ^ counter_nonce;

    //----------------------------------------------------------------
    // FSM
    //----------------------------------------------------------------
    always_comb begin : interface_fsm
        state_next = IDLE_ST;
        unique case (state_reg)
            IDLE_ST:        state_next = (en & hmac_drbg_ready) ? LFSR_ST : IDLE_ST;
            LFSR_ST:        state_next = (hmac_done_edge) ? LAMBDA_ST : LFSR_ST;
            LAMBDA_ST:      state_next = (hmac_done_edge) ? SCALAR_RND_ST : LAMBDA_ST;
            SCALAR_RND_ST:  state_next = (hmac_done_edge) ? RND_DONE_ST : SCALAR_RND_ST;
            RND_DONE_ST:    state_next = (hmac_mode == SIGN_CMD)   ? MASKING_RND_ST :
                                         (hmac_mode == KEYGEN_CMD) ? KEYGEN_ST      : DONE_ST;
            MASKING_RND_ST: state_next = (hmac_done_edge) ? (nondet ? SIGN_NONCE_ST : SIGN_ST) : MASKING_RND_ST;
            SIGN_NONCE_ST:  state_next = (hmac_done_edge) ? SIGN_ST : SIGN_NONCE_ST;
            KEYGEN_ST:      state_next = (hmac_done_edge) ? DONE_ST : KEYGEN_ST;
            SIGN_ST:        state_next = (hmac_done_edge) ? DONE_ST : SIGN_ST;
            DONE_ST:        state_next = IDLE_ST;
            default:        state_next = IDLE_ST;
        endcase
    end

    //----------------------------------------------------------------
    // Outputs.
    //----------------------------------------------------------------
    assign lambda      = lambda_reg;
    assign scalar_rnd  = scalar_rnd_reg;
    assign masking_rnd = masking_rnd_reg;
    assign drbg        = drbg_reg;
    assign ready       = (state_reg == IDLE_ST);

endmodule
