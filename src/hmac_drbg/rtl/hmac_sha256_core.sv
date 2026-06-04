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
// hmac_sha256_core.sv
// -------------------
// HMAC-SHA256 engine that mirrors the control style of
// `hmac_core.sv` (HMAC-SHA384/512) but uses two plain `sha256_core`
// instances to perform inner (H1) and outer (H2) hashing in parallel.
//
// Interface:
//   * key       : 256-bit secret key (zero-padded internally to the
//                 512-bit SHA-256 block boundary).
//   * block_msg : 512-bit pre-padded inner message block (caller is
//                 responsible for adding the SHA-256 padding on the
//                 final inner block).
//   * tag       : 256-bit HMAC result.
//
// Operation model (matches hmac_core for hmac_drbg-style reuse):
//   * `init_cmd` runs the full sequence:
//        H1: SHA256_init(K^ipad)       -> SHA256_next(block_msg)
//        H2: SHA256_init(K^opad)       (in parallel)
//        H2: SHA256_next(H1_digest || sha256_pad_for_768b)
//        -> produce tag.
//   * `next_cmd` skips the K^ipad step and continues feeding another
//     inner message block into the prior H1 state, then finalises with
//     a fresh outer hash:
//        H1: SHA256_next(block_msg)
//        H2: SHA256_init(K^opad)
//        H2: SHA256_next(H1_digest || sha256_pad_for_768b)
//     The intermediate tag produced by the prior `init_cmd` is not
//     meaningful in this multi-block-inner mode; only the tag produced
//     by the last block (the one that contains the SHA-256 padding) is
//     a valid HMAC-SHA256 output.
//
//======================================================================

module hmac_sha256_core
(
    // Clock and reset.
    input  logic           clk,
    input  logic           reset_n,
    input  logic           zeroize,

    // Control.
    input  logic           init_cmd,
    input  logic           next_cmd,
    output logic           ready,
    output logic           tag_valid,

    // Data ports.
    input  logic [255 : 0] key,
    input  logic [511 : 0] block_msg,
    output logic [255 : 0] tag
);

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  // SHA-256 block size = 512 bits.
  // ipad = 0x36 repeated 64 bytes (512 bits); opad = 0x5c repeated 64 bytes.
  localparam logic [511:0] IPAD512 = {64{8'h36}};
  localparam logic [511:0] OPAD512 = {64{8'h5c}};

  // Outer hash padding: the H2 second block is
  //   { H1_digest[255:0], 1'b1, 191'b0, 64'd768 }
  // where 768 = K^opad bits (512) + H1_digest bits (256).
  localparam logic [255:0] HMAC256_FINAL_PAD = {1'b1, 191'b0, 64'd768};

  localparam logic [2:0] CTRL_IDLE = 3'd0;
  localparam logic [2:0] CTRL_IPAD = 3'd1;
  localparam logic [2:0] CTRL_OPAD = 3'd2;
  localparam logic [2:0] CTRL_HMAC = 3'd3;
  localparam logic [2:0] CTRL_DONE = 3'd4;

  //----------------------------------------------------------------
  // Registers.
  //----------------------------------------------------------------
  logic [2:0] hmac_ctrl_reg;
  logic [2:0] hmac_ctrl_new;
  logic       hmac_ctrl_we;
  logic [2:0] hmac_ctrl_last;

  logic       ready_flag;
  logic       digest_valid_reg;
  logic       digest_valid_new;
  logic       digest_valid_we;

  // SHA-256 core wires (H1 inner, H2 outer).
  logic           H1_init;
  logic           H1_next;
  logic [511:0]   H1_block;
  logic           H1_ready;
  logic [255:0]   H1_digest;
  logic           H1_digest_valid;

  logic           H2_init;
  logic           H2_next;
  logic [511:0]   H2_block;
  logic           H2_ready;
  logic [255:0]   H2_digest;
  logic           H2_digest_valid;

  // Combinational helpers.
  logic [511:0]   key_ipadded;
  logic [511:0]   key_opadded;
  logic [511:0]   HMAC_padded;
  logic           first_round;
  logic           IPAD_ready;
  logic           OPAD_ready;
  logic           HMAC_ready;

  //----------------------------------------------------------------
  // Concurrent connectivity.
  //----------------------------------------------------------------
  assign ready     = ready_flag;
  assign tag       = digest_valid_reg ? H2_digest : 256'b0;
  assign tag_valid = digest_valid_reg;

  //----------------------------------------------------------------
  // SHA-256 core instantiations.
  // Mode hard-wired to '1' = SHA-256 (mode = '0' would be SHA-224).
  //----------------------------------------------------------------
  sha256_core u_sha256_core_h1
  (
      .clk         (clk),
      .reset_n     (reset_n),
      .zeroize     (zeroize),
      .init_cmd    (H1_init),
      .next_cmd    (H1_next),
      .mode        (1'b1),
      .block_msg   (H1_block),
      .ready       (H1_ready),
      .digest      (H1_digest),
      .digest_valid(H1_digest_valid)
  );

  sha256_core u_sha256_core_h2
  (
      .clk         (clk),
      .reset_n     (reset_n),
      .zeroize     (zeroize),
      .init_cmd    (H2_init),
      .next_cmd    (H2_next),
      .mode        (1'b1),
      .block_msg   (H2_block),
      .ready       (H2_ready),
      .digest      (H2_digest),
      .digest_valid(H2_digest_valid)
  );

  //----------------------------------------------------------------
  // Sequential register update.
  //----------------------------------------------------------------
  always_ff @(posedge clk or negedge reset_n) begin : reg_update
    if (!reset_n) begin
      digest_valid_reg <= 1'b0;
      hmac_ctrl_reg    <= CTRL_IDLE;
      hmac_ctrl_last   <= CTRL_IDLE;
    end
    else if (zeroize) begin
      digest_valid_reg <= 1'b0;
      hmac_ctrl_reg    <= CTRL_IDLE;
      hmac_ctrl_last   <= CTRL_IDLE;
    end
    else begin
      hmac_ctrl_last <= hmac_ctrl_reg;

      if (digest_valid_we)
        digest_valid_reg <= digest_valid_new;

      if (hmac_ctrl_we)
        hmac_ctrl_reg <= hmac_ctrl_new;
    end
  end

  //----------------------------------------------------------------
  // SHA-256 block routing & first-round edge detection.
  //----------------------------------------------------------------
  always_comb begin : state_fsm
    IPAD_ready = H1_ready;
    OPAD_ready = H1_ready & H2_ready;
    HMAC_ready = H2_ready;

    key_ipadded = {key, 256'b0} ^ IPAD512;
    key_opadded = {key, 256'b0} ^ OPAD512;
    HMAC_padded = {H1_digest, HMAC256_FINAL_PAD};

    // Defaults.
    H1_block = key_ipadded;
    H2_block = key_opadded;
    H1_init  = 1'b0;
    H1_next  = 1'b0;
    H2_init  = 1'b0;
    H2_next  = 1'b0;

    first_round = (hmac_ctrl_reg == hmac_ctrl_last) ? 1'b0 : 1'b1;

    unique case (hmac_ctrl_reg)
      CTRL_IPAD: begin
        if (first_round) begin
          // Kick off H1 with K^ipad and H2 with K^opad in parallel.
          H1_init    = 1'b1;
          H2_init    = 1'b1;
          IPAD_ready = 1'b0;
        end
      end

      CTRL_OPAD: begin
        if (first_round) begin
          // Feed the inner-message block into H1 (continuing the chain
          // from K^ipad).  Restart H2 with K^opad so that we always
          // get a fresh outer hash on each tag.
          H1_next    = 1'b1;
          H2_init    = 1'b1;
          OPAD_ready = 1'b0;
        end
        H1_block = block_msg;
      end

      CTRL_HMAC: begin
        if (first_round) begin
          // Finalise the outer hash with the inner digest + SHA-256 padding.
          H2_next    = 1'b1;
          HMAC_ready = 1'b0;
        end
        H2_block = HMAC_padded;
      end

      default: begin
        H1_init = 1'b0;
        H1_next = 1'b0;
        H2_init = 1'b0;
        H2_next = 1'b0;
      end
    endcase
  end

  //----------------------------------------------------------------
  // Control FSM.
  //----------------------------------------------------------------
  always_comb begin : hmac_ctrl_fsm
    ready_flag       = 1'b0;
    digest_valid_new = 1'b0;
    digest_valid_we  = 1'b0;
    hmac_ctrl_new    = CTRL_IDLE;
    hmac_ctrl_we     = 1'b0;

    unique case (hmac_ctrl_reg)
      CTRL_IDLE: begin
        ready_flag = 1'b1;

        if (init_cmd) begin
          digest_valid_new = 1'b0;
          digest_valid_we  = 1'b1;
          hmac_ctrl_new    = CTRL_IPAD;
          hmac_ctrl_we     = 1'b1;
        end

        if (next_cmd) begin
          digest_valid_new = 1'b0;
          digest_valid_we  = 1'b1;
          hmac_ctrl_new    = CTRL_OPAD;
          hmac_ctrl_we     = 1'b1;
        end
      end

      CTRL_IPAD: begin
        digest_valid_new = 1'b0;
        digest_valid_we  = 1'b1;
        if (IPAD_ready) begin
          hmac_ctrl_new = CTRL_OPAD;
          hmac_ctrl_we  = 1'b1;
        end
      end

      CTRL_OPAD: begin
        digest_valid_new = 1'b0;
        digest_valid_we  = 1'b1;
        if (OPAD_ready) begin
          hmac_ctrl_new = CTRL_HMAC;
          hmac_ctrl_we  = 1'b1;
        end
      end

      CTRL_HMAC: begin
        digest_valid_new = 1'b0;
        digest_valid_we  = 1'b1;
        if (HMAC_ready) begin
          hmac_ctrl_new = CTRL_DONE;
          hmac_ctrl_we  = 1'b1;
        end
      end

      CTRL_DONE: begin
        digest_valid_new = 1'b1;
        digest_valid_we  = 1'b1;
        hmac_ctrl_new    = CTRL_IDLE;
        hmac_ctrl_we     = 1'b1;
      end

      default: begin
        ready_flag       = 1'b0;
        digest_valid_new = 1'b0;
        digest_valid_we  = 1'b0;
        hmac_ctrl_new    = CTRL_IDLE;
        hmac_ctrl_we     = 1'b0;
      end
    endcase
  end

endmodule

//======================================================================
// EOF hmac_sha256_core.sv
//======================================================================
