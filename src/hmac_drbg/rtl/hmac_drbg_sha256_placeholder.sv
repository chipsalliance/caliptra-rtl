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
// hmac_drbg_sha256_placeholder.sv
// -------------------
// HMAC256-drbg top-level wrapper with 256-bit data access.
//
// Mirrors `hmac_drbg.sv` (which uses HMAC-SHA384) but drives a
// `hmac_sha256_core` (HMAC-SHA256) instead.  The control FSM is
// identical in shape -- only the message-block packing changes
// because SHA-256 operates on 512-bit blocks (vs 1024-bit blocks
// for SHA-512/384).
//
// Based on section 10.1.2. of NIST SP 800-90A, Rev 1:
// "Recommendation for Random Number Generation Using
// Deterministic Random Bit Generators", and
// section 3.1. RFC 6979.
//
// Parameters
//   - [SHA-256]
//   - [PredictionResistance = False]
//   - [EntropyInputLen      = 256]
//   - [NonceLen             = 256]
//   - [PersonalizationStringLen = 0]
//   - [AdditionalInputLen   = 0]
//   - [ReturnedBitsLen      = 256]
//
//   - INIT: Instantiate HMAC-DRBG with entropy + nonce and produce a
//           256-bit output in (0, prime).  Rejection sampling
//           (CHCK_ST -> K3_ST/V3_ST loop) handles the out-of-range
//           case.
//   - NEXT: Re-run HMAC_DRBG_Generate with the existing K/V state.
//======================================================================

module hmac_drbg_sha256_placeholder
#(
  parameter                  REG_SIZE        = 256,
  parameter [REG_SIZE-1 : 0] GROUP_ORDER_P256 = { {(REG_SIZE-256){1'b0}}, 256'hFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551 },
  parameter [REG_SIZE-1 : 0] HMAC_DRBG_PRIME  = GROUP_ORDER_P256
)
(
  // Clock and reset.
  input  wire                       clk,
  input  wire                       reset_n,
  input  wire                       zeroize,

  // Control.
  input  wire                       init_cmd,
  input  wire                       next_cmd,
  output wire                       ready,
  output wire                       valid,

  // Data.
  input  wire   [REG_SIZE-1 : 0]    entropy,
  input  wire   [REG_SIZE-1 : 0]    nonce,

  output wire  [REG_SIZE-1  : 0]    drbg
);

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  // V_init = 32 bytes of 0x01; K_init = 32 bytes of 0x00 per SP 800-90A.
  localparam [REG_SIZE-1 : 0] V_init = 256'h0101010101010101010101010101010101010101010101010101010101010101;
  localparam [REG_SIZE-1 : 0] K_init = 256'h0000000000000000000000000000000000000000000000000000000000000000;

  // SHA-256 length fields (bits) for the inner hash:
  //   K10/K20 inner = K^ipad(512) + V(256) + 0x00/01(8) + entropy(256) + nonce(256) = 1288 bits
  //   V/T   inner = K^ipad(512) + V(256)                                              = 768 bits
  //   K3    inner = K^ipad(512) + V(256) + 0x00(8)                                    = 776 bits
  localparam [63:0] LEN_K10 = 64'd1288;
  localparam [63:0] LEN_VT  = 64'd768;
  localparam [63:0] LEN_K3  = 64'd776;

  // SHA-256 padding constants (1-bit '1' + zero-fill + 64-bit length).
  //   - V/T  block payload   = V (256) + pad '1' (1) + 191 zeros + 64-bit length = 512
  //   - K3   block payload   = V (256) + 0x00 (8) + pad '1' (1) + 183 zeros + 64-bit length = 512
  //   - K11  block payload   = entropy[7:0] (8) + nonce (256) + pad '1' (1) + 183 zeros + 64-bit length = 512

  /*STATES*/
  localparam [4 : 0] IDLE_ST        = 5'd0;
  localparam [4 : 0] INIT_ST        = 5'd1;
  localparam [4 : 0] NEXT_ST        = 5'd2;
  localparam [4 : 0] K10_ST         = 5'd3;   // K = HMAC_K(V || 0x00 || entropy || nonce) - inner block #1
  localparam [4 : 0] K11_ST         = 5'd4;   // ... inner block #2 (with padding)
  localparam [4 : 0] V1_ST          = 5'd5;   // V = HMAC_K(V)
  localparam [4 : 0] K2_INIT_ST     = 5'd6;
  localparam [4 : 0] K20_ST         = 5'd7;   // K = HMAC_K(V || 0x01 || entropy || nonce) - inner block #1
  localparam [4 : 0] K21_ST         = 5'd8;   // ... inner block #2 (with padding)
  localparam [4 : 0] V2_ST          = 5'd9;   // V = HMAC_K(V)
  localparam [4 : 0] T_ST           = 5'd10;  // T = HMAC_K(V)
  localparam [4 : 0] CHCK_ST        = 5'd11;  // Return T if T in [1, prime-1], otherwise re-run K3/V3
  localparam [4 : 0] K3_ST          = 5'd12;  // K = HMAC_K(V || 0x00)
  localparam [4 : 0] V3_ST          = 5'd13;  // V = HMAC_K(V)
  localparam [4 : 0] DONE_ST        = 5'd14;

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  reg [4:0]  drbg_st_reg;
  reg [4:0]  drbg_next_st;
  reg [4:0]  drbg_st_reg_last;

  reg                   ready_reg;
  reg                   valid_reg;
  reg [REG_SIZE-1 : 0]  drbg_reg;
  reg                   first_round;
  reg                   HMAC_tag_valid_last;
  reg                   HMAC_tag_valid_edge;

  reg [REG_SIZE-1:0]    K_reg;
  reg [REG_SIZE-1:0]    V_reg;

  //----------------------------------------------------------------
  // Wires for HMAC-SHA256 module instantiation.
  //----------------------------------------------------------------
  reg                   HMAC_init;
  reg                   HMAC_next;
  reg  [511:0]          HMAC_block;
  reg  [REG_SIZE-1:0]   HMAC_key;

  wire                  HMAC_ready;
  wire                  HMAC_tag_valid;
  wire [REG_SIZE-1:0]   HMAC_tag;

  logic                 failure_check;

  //----------------------------------------------------------------
  // HMAC-SHA256 module instantiation.
  //----------------------------------------------------------------
  hmac_sha256_core
    HMAC_K
    (
    .clk      (clk),
    .reset_n  (reset_n),
    .zeroize  (zeroize),
    .init_cmd (HMAC_init),
    .next_cmd (HMAC_next),
    .key      (HMAC_key),
    .block_msg(HMAC_block),
    .ready    (HMAC_ready),
    .tag      (HMAC_tag),
    .tag_valid(HMAC_tag_valid)
    );

  //----------------------------------------------------------------
  // Edge detection helpers.
  //----------------------------------------------------------------
  always_comb
  begin : edge_detector
    first_round         = (drbg_st_reg == drbg_st_reg_last) ? 1'b0 : 1'b1;
    HMAC_tag_valid_edge = HMAC_tag_valid & (!HMAC_tag_valid_last);
  end // edge_detector

  always_ff @ (posedge clk or negedge reset_n)
  begin
    if (!reset_n)
      HMAC_tag_valid_last <= 1'b0;
    else if (zeroize)
      HMAC_tag_valid_last <= 1'b0;
    else
      HMAC_tag_valid_last <= HMAC_tag_valid;
  end

  //----------------------------------------------------------------
  // ready / valid / drbg_reg housekeeping.
  //----------------------------------------------------------------
  always_ff @ (posedge clk or negedge reset_n)
  begin : valid_drbg_regs_updates
    if (!reset_n) begin
      ready_reg <= 1'b0;
      valid_reg <= 1'b0;
      drbg_reg  <= '0;
    end
    else if (zeroize) begin
      ready_reg <= 1'b0;
      valid_reg <= 1'b0;
      drbg_reg  <= '0;
    end
    else begin
      unique case (drbg_st_reg)
        IDLE_ST: begin
          if (init_cmd | next_cmd) begin
            ready_reg <= 1'b0;
            valid_reg <= 1'b0;
          end
          else
            ready_reg <= 1'b1;
        end

        DONE_ST: begin
          drbg_reg  <= HMAC_tag;
          valid_reg <= HMAC_tag_valid;
          ready_reg <= HMAC_ready;
        end

        default: begin
          ready_reg <= 1'b0;
          valid_reg <= 1'b0;
          drbg_reg  <= '0;
        end
      endcase
    end
  end // valid_drbg_regs_updates

  //----------------------------------------------------------------
  // HMAC init/next pulse generation per state.
  // - "init" states feed K^ipad and one message block.
  // - "next" states feed one additional message block on the prior
  //   K^ipad chain (used for the second inner block of K10 / K20).
  //----------------------------------------------------------------
  always_ff @ (posedge clk or negedge reset_n)
  begin : hmac_command_update
    if (!reset_n) begin
      HMAC_init <= 1'b0;
      HMAC_next <= 1'b0;
    end
    else if (zeroize) begin
      HMAC_init <= 1'b0;
      HMAC_next <= 1'b0;
    end
    else begin
      HMAC_init <= 1'b0;
      HMAC_next <= 1'b0;
      if (first_round) begin
        unique case (drbg_st_reg)
          K10_ST: HMAC_init <= 1'b1;
          K11_ST: HMAC_next <= 1'b1;
          V1_ST : HMAC_init <= 1'b1;
          K20_ST: HMAC_init <= 1'b1;
          K21_ST: HMAC_next <= 1'b1;
          V2_ST : HMAC_init <= 1'b1;
          T_ST  : HMAC_init <= 1'b1;
          K3_ST : HMAC_init <= 1'b1;
          V3_ST : HMAC_init <= 1'b1;
          default: begin
            HMAC_init <= 1'b0;
            HMAC_next <= 1'b0;
          end
        endcase
      end
    end
  end // hmac_command_update

  //----------------------------------------------------------------
  // K / V state registers.  K is the HMAC key, V is the chain value.
  //----------------------------------------------------------------
  always_ff @ (posedge clk or negedge reset_n)
  begin : hmac_inputs_update
    if (!reset_n) begin
      K_reg <= '0;
      V_reg <= '0;
    end
    else if (zeroize) begin
      K_reg <= '0;
      V_reg <= '0;
    end
    else begin
      if (first_round) begin
        unique case (drbg_st_reg)
          INIT_ST: begin
            K_reg <= K_init;
            V_reg <= V_init;
          end
          V1_ST  : K_reg <= HMAC_tag;
          K20_ST : V_reg <= HMAC_tag;
          V2_ST  : K_reg <= HMAC_tag;
          T_ST   : V_reg <= HMAC_tag;
          V3_ST  : K_reg <= HMAC_tag;
          CHCK_ST: V_reg <= HMAC_tag;
          default: begin
            K_reg <= K_reg;
            V_reg <= V_reg;
          end
        endcase
      end
    end
  end // hmac_inputs_update

  //----------------------------------------------------------------
  // Message block packing per FSM state.
  // SHA-256 block = 512 bits.  Each entry below is exactly 512 bits.
  //----------------------------------------------------------------
  always_comb
  begin : hmac_block_update
    HMAC_key = K_reg;
    unique case (drbg_st_reg)
      // K10: inner_msg = V (256) || 0x00 (8) || entropy (256) || nonce (256) = 776 bits.
      //   block #1 = V || 0x00 || entropy[255:8]       (256 + 8 + 248 = 512)
      K10_ST: HMAC_block = {V_reg, 8'h00, entropy[255:8]};
      //   block #2 = entropy[7:0] || nonce || '1' || 0...0 || len  (8 + 256 + 1 + 183 + 64 = 512)
      K11_ST: HMAC_block = {entropy[7:0], nonce, 1'h1, 183'b0, LEN_K10};

      // V/T: inner_msg = V (256) = 256 bits.
      //   block = V || '1' || 0...0 || len  (256 + 1 + 191 + 64 = 512)
      V1_ST : HMAC_block = {V_reg, 1'h1, 191'b0, LEN_VT};

      // K20: inner_msg = V || 0x01 || entropy || nonce = 776 bits.  Same shape as K10.
      K20_ST: HMAC_block = {V_reg, 8'h01, entropy[255:8]};
      K21_ST: HMAC_block = {entropy[7:0], nonce, 1'h1, 183'b0, LEN_K10};

      V2_ST : HMAC_block = {V_reg, 1'h1, 191'b0, LEN_VT};
      T_ST  : HMAC_block = {V_reg, 1'h1, 191'b0, LEN_VT};

      // K3: inner_msg = V || 0x00 = 264 bits.
      //   block = V || 0x00 || '1' || 0...0 || len  (256 + 8 + 1 + 183 + 64 = 512)
      K3_ST : HMAC_block = {V_reg, 8'h00, 1'h1, 183'b0, LEN_K3};

      V3_ST : HMAC_block = {V_reg, 1'h1, 191'b0, LEN_VT};
      default: HMAC_block = '0;
    endcase
  end // hmac_block_update

  //----------------------------------------------------------------
  // State register updates.
  //----------------------------------------------------------------
  always_ff @ (posedge clk or negedge reset_n)
  begin : state_update
    if (!reset_n)
      drbg_st_reg <= IDLE_ST;
    else if (zeroize)
      drbg_st_reg <= IDLE_ST;
    else
      drbg_st_reg <= drbg_next_st;
  end // state_update

  always_ff @ (posedge clk or negedge reset_n)
  begin : ff_state_update
    if (!reset_n)
      drbg_st_reg_last <= IDLE_ST;
    else if (zeroize)
      drbg_st_reg_last <= IDLE_ST;
    else
      drbg_st_reg_last <= drbg_st_reg;
  end // ff_state_update

  //----------------------------------------------------------------
  // FSM next-state logic.
  //----------------------------------------------------------------
  always_comb
  begin : state_logic
    unique case (drbg_st_reg)
      IDLE_ST: begin
        if (HMAC_ready) begin
          unique case ({init_cmd, next_cmd})
            2'b10  : drbg_next_st = INIT_ST;
            2'b01  : drbg_next_st = NEXT_ST;
            default: drbg_next_st = IDLE_ST;
          endcase
        end
        else
          drbg_next_st = IDLE_ST;
      end

      INIT_ST   : drbg_next_st = K10_ST;
      NEXT_ST   : drbg_next_st = K3_ST;
      K10_ST    : drbg_next_st = (HMAC_tag_valid_edge) ? K11_ST     : K10_ST;
      K11_ST    : drbg_next_st = (HMAC_tag_valid_edge) ? V1_ST      : K11_ST;
      V1_ST     : drbg_next_st = (HMAC_tag_valid_edge) ? K2_INIT_ST : V1_ST;
      K2_INIT_ST: drbg_next_st = K20_ST;
      K20_ST    : drbg_next_st = (HMAC_tag_valid_edge) ? K21_ST     : K20_ST;
      K21_ST    : drbg_next_st = (HMAC_tag_valid_edge) ? V2_ST      : K21_ST;
      V2_ST     : drbg_next_st = (HMAC_tag_valid_edge) ? T_ST       : V2_ST;
      T_ST      : drbg_next_st = (HMAC_tag_valid_edge) ? CHCK_ST    : T_ST;

      CHCK_ST: begin
        if (failure_check)
          drbg_next_st = K3_ST;
        else
          drbg_next_st = DONE_ST;
      end

      K3_ST  : drbg_next_st = (HMAC_tag_valid_edge) ? V3_ST : K3_ST;
      V3_ST  : drbg_next_st = (HMAC_tag_valid_edge) ? T_ST  : V3_ST;
      DONE_ST: drbg_next_st = IDLE_ST;
      default: drbg_next_st = IDLE_ST;
    endcase
  end // state_logic

  always_comb failure_check = (HMAC_tag == 0) || (HMAC_tag >= HMAC_DRBG_PRIME);

  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign ready = ready_reg;
  assign valid = valid_reg;
  assign drbg  = drbg_reg;

endmodule // hmac_drbg_sha256_placeholder

//======================================================================
// EOF hmac_drbg_sha256_placeholder.sv
//======================================================================
