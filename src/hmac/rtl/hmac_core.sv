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
// hmac_core.sv
// ------------
// HMAC-SHA-512/384 core with SCA countermeasures.
// Single SHA-512 masked core architecture for area optimization.
//
// Commands:
//   init_cmd  - SHA-init with (K xor ipad), then SHA-next with first
//               message block. If issued together with last_cmd,
//               continues directly to inner-digest capture, OPAD, and
//               HMAC finalization.
//   next_cmd  - SHA-next with one intermediate message block.
//   last_cmd  - SHA-next with the final message block, captures the
//               inner digest, then SHA-init with (K xor opad) and
//               SHA-next with {inner_digest, FINAL_PAD} to produce
//               the HMAC tag.
//
//======================================================================

module hmac_core
  import hmac_param_pkg::*;
(
      // Clock and reset.
      input logic            clk,
      input logic            reset_n,
      input logic            zeroize,

      // Control.
      input logic            init_cmd,
      input logic            next_cmd,
      input logic            last_cmd,
      input logic            mode_cmd,
      output logic           ready,
      output logic           tag_valid,

      // Data ports.
      input  logic [LFSR_SEED_SIZE-1 : 0] lfsr_seed,

      input  logic [KEY_SIZE-1   : 0] key,
      input  logic [BLOCK_SIZE-1 : 0] block_msg,
      output logic [TAG_SIZE-1   : 0] tag
    );


  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  // IPAD/OPAD and SHA-512 family final-padding constants come from
  // hmac_param_pkg so the same widths/values are used everywhere.

  localparam [2 : 0] CTRL_IDLE     = 3'd0;
  localparam [2 : 0] CTRL_ENTROPY  = 3'd1;
  localparam [2 : 0] CTRL_IPAD     = 3'd2;
  localparam [2 : 0] CTRL_MSG      = 3'd3;
  localparam [2 : 0] CTRL_OPAD     = 3'd4;
  localparam [2 : 0] CTRL_HMAC     = 3'd5;
  localparam [2 : 0] CTRL_DONE     = 3'd6;
  

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  logic [2 : 0] hmac_ctrl_reg;
  logic [2 : 0] hmac_ctrl_new;
  logic         hmac_ctrl_we;
  logic [2 : 0] hmac_ctrl_ff;

  logic         ready_flag;
  logic         digest_valid_reg;
  logic         digest_valid_new;
  logic         digest_valid_we;

  logic [BLOCK_SIZE-1:0] key_ipadded;
  logic [BLOCK_SIZE-1:0] key_opadded;
  logic [BLOCK_SIZE-1:0] HMAC_padded;

  logic         first_round;
  logic         IPAD_ready;
  logic         MSG_ready;
  logic         OPAD_ready;
  logic         HMAC_ready;
  logic         ENTROPY_ready;
  logic [1:0]   mode_reg;

  // Latched on entry to MSG flow: 1 if the current message block is the
  // final one (so MSG must capture inner_digest and continue to OPAD).
  logic         is_last_block;

  // Captured inner-hash digest at the final MSG -> OPAD transition; used
  // as data into the HMAC finalization block.
  logic [TAG_SIZE-1:0] inner_digest_reg;
  logic         inner_digest_we;

  logic             sha_init;
  logic             sha_next;
  logic [BLOCK_SIZE-1 : 0] sha_block;
  logic             sha_ready;
  logic [TAG_SIZE-1 : 0] sha_digest;
  logic             sha_digest_valid;

  // Entropy.
  logic [LFSR_SEED_SIZE-1 : 0] entropy;
  logic [LFSR_SEED_SIZE-1 : 0] lfsr_entropy;
  logic [LFSR_SEED_SIZE-1 : 0] entropy_digest;
  logic [63 : 0]               counter_reg;
  logic [BLOCK_SIZE-1 : 0]     entropy_block;
  logic                        set_entropy;

  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign ready     = ready_flag;

  assign tag       = digest_valid_reg ? sha_digest : {TAG_SIZE{1'b0}};
  assign tag_valid = digest_valid_reg;

  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  sha512_masked_core u_sha512_core_h1
                     (
                     .clk(clk),
                     .reset_n(reset_n),
                     .zeroize(zeroize),

                     .init_cmd(sha_init),
                     .next_cmd(sha_next),
                     .mode(mode_reg),

                     .entropy(entropy),

                     .block_msg(sha_block),

                     .ready(sha_ready),
                     .digest(sha_digest),
                     .digest_valid(sha_digest_valid)
                    );

  // One 32-bit LFSR per dword of entropy (LFSR_SEED_SIZE bits total).
  genvar i;
  generate
      for (i = 0; i < LFSR_SEED_SIZE/32; i++) begin : gen_lfsr
        caliptra_prim_lfsr
        #(
          .LfsrType("FIB_XNOR"),
          .LfsrDw(32),
          .StateOutDw(32)
        ) caliptra_prim_lfsr_inst_i
        (
          .clk_i(clk),
          .rst_ni(reset_n),
          .seed_en_i(init_cmd),
          .seed_i(lfsr_entropy[i*32 +: 32]),
          .lfsr_en_i(1'b1),
          .entropy_i('0),
          .state_o(entropy[i*32 +: 32])
        );
      end
  endgenerate

  //----------------------------------------------------------------
  // reg_update
  //
  // Update functionality for all registers in the core.
  // All registers are positive edge triggered with asynchronous
  // active low reset. All registers have write enable.
  //----------------------------------------------------------------
  always_ff @(posedge clk or negedge reset_n)
    begin : reg_update
      if (!reset_n)
        begin
          digest_valid_reg <= 1'b0;
          hmac_ctrl_reg    <= CTRL_IDLE;
          hmac_ctrl_ff     <= CTRL_IDLE;
          inner_digest_reg <= '0;
          is_last_block    <= 1'b0;
        end
      else if (zeroize)
        begin
          digest_valid_reg <= 1'b0;
          hmac_ctrl_reg    <= CTRL_IDLE;
          hmac_ctrl_ff     <= CTRL_IDLE;
          inner_digest_reg <= '0;
          is_last_block    <= 1'b0;
        end
      else
        begin
          hmac_ctrl_ff <= hmac_ctrl_reg;

          if (digest_valid_we)
            digest_valid_reg <= digest_valid_new;

          if (hmac_ctrl_we)
            hmac_ctrl_reg <= hmac_ctrl_new;

          if (inner_digest_we)
            inner_digest_reg <= sha_digest;

          // Sample at IDLE: LAST is a modifier on INIT or NEXT, so any
          // command kicked off at IDLE latches is_last_block from last_cmd.
           // This handles all firmware patterns: INIT, INIT|LAST, NEXT and NEXT|LAST. 
          if (hmac_ctrl_reg == CTRL_IDLE) begin
            if (init_cmd | next_cmd)
              is_last_block <= last_cmd;
          end
        end
    end // reg_update


  always_ff @(posedge clk or negedge reset_n)
    begin
      if (!reset_n)
        mode_reg <= '0;
      else if (zeroize)
        mode_reg <= '0;
      else begin
        if (hmac_ctrl_reg == CTRL_IDLE)
          mode_reg <= {1'b1, mode_cmd};  //hashing algorithm mode: 00 for SHA512/224, 01 for SHA512/256, 10 for SHA384, 11 for SHA512
      end
    end

  // without zeroize to make it more complex
 always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n)
      entropy_digest <= '0;
    else if (set_entropy)
      entropy_digest <= sha_digest[LFSR_SEED_SIZE-1 : 0];
  end

 
//without zeroize to make it more complex
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n)
      counter_reg <= '0;
    else
      counter_reg <= counter_reg + 1;
  end

  always_comb lfsr_entropy = entropy_digest ^ lfsr_seed;
  always_comb entropy_block = {entropy_digest, lfsr_seed, counter_reg, ENTROPY_PAD};

  //----------------------------------------------------------------
  // sha_block_fsm
  //
  // Logic to select the appropriate SHA input block based on the current state of the HMAC control FSM.
  //----------------------------------------------------------------
  always_comb
    begin : sha_block_fsm
      unique case (hmac_ctrl_reg)
        CTRL_ENTROPY: sha_block = entropy_block;
        CTRL_IPAD:    sha_block = key_ipadded;
        CTRL_MSG:     sha_block = block_msg;
        CTRL_OPAD:    sha_block = key_opadded;
        CTRL_HMAC:    sha_block = HMAC_padded;
        default:      sha_block = '0;
      endcase
    end

  //----------------------------------------------------------------
  // state_logic
  //
  // Mux and control for the single SHA core based on FSM state.
  //----------------------------------------------------------------
  always_comb
    begin : state_logic
      key_ipadded = {key, {(BLOCK_SIZE-KEY_SIZE){1'b0}}} ^ IPAD;
      key_opadded = {key, {(BLOCK_SIZE-KEY_SIZE){1'b0}}} ^ OPAD;
      HMAC_padded = mode_reg[0] ? {inner_digest_reg, HMAC512_FINAL_PAD}
                                : {inner_digest_reg[TAG_SIZE-1 : HMAC384_TAG_PAD], HMAC384_FINAL_PAD};

      // Defaults
      sha_init  = 1'b0;
      sha_next  = 1'b0;

      first_round = (hmac_ctrl_reg == hmac_ctrl_ff) ? 1'b0 : 1'b1;
      // IPAD/OPAD finish with sha_init only — digest is not yet meaningful,
      IPAD_ready    = sha_ready;
      MSG_ready     = sha_ready & sha_digest_valid;
      OPAD_ready    = sha_ready;
      HMAC_ready    = sha_ready & sha_digest_valid;
      ENTROPY_ready = sha_ready & sha_digest_valid;

      unique case (hmac_ctrl_reg)
        CTRL_ENTROPY:
          if (first_round)
            begin
              sha_init      = 1'b1;
              ENTROPY_ready = 1'b0;
            end

        CTRL_IPAD:
          if (first_round)
            begin
              sha_init   = 1'b1;
              IPAD_ready = 1'b0;
            end

        CTRL_MSG:
          if (first_round)
            begin
              sha_next  = 1'b1;
              MSG_ready = 1'b0;
            end

        CTRL_OPAD:
          if (first_round)
            begin
              sha_init   = 1'b1;
              OPAD_ready = 1'b0;
            end

        CTRL_HMAC:
          if (first_round)
            begin
              sha_next   = 1'b1;
              HMAC_ready = 1'b0;
            end

        default: begin
          sha_init = 1'b0;
          sha_next = 1'b0;
        end
      endcase
    end

  //----------------------------------------------------------------
  // hmac_ctrl_fsm
  //
  // Logic for the state machine controlling the core behaviour.
  //----------------------------------------------------------------
  always_comb
    begin : hmac_ctrl_fsm
      ready_flag       = 1'b0;
      digest_valid_new = 1'b0;
      digest_valid_we  = 1'b0;
      hmac_ctrl_new    = CTRL_IDLE;
      hmac_ctrl_we     = 1'b0;
      inner_digest_we  = 1'b0;
      set_entropy      = 1'b0;

      unique case (hmac_ctrl_reg)
        CTRL_IDLE:
          begin
            ready_flag = 1'b1;

            if (init_cmd)
              begin
                digest_valid_new = 1'b0;
                digest_valid_we  = 1'b1;
                hmac_ctrl_new    = CTRL_ENTROPY;
                hmac_ctrl_we     = 1'b1;
              end
            else if (next_cmd)
              begin
                digest_valid_new = 1'b0;
                digest_valid_we  = 1'b1;
                hmac_ctrl_new    = CTRL_MSG;
                hmac_ctrl_we     = 1'b1;
              end
          end

        CTRL_ENTROPY:
          if (ENTROPY_ready)
            begin
              set_entropy   = 1'b1;
              hmac_ctrl_new = CTRL_IPAD;
              hmac_ctrl_we  = 1'b1;
            end

        CTRL_IPAD:
          if (IPAD_ready)
            begin
              hmac_ctrl_new = CTRL_MSG;
              hmac_ctrl_we  = 1'b1;
            end

        CTRL_MSG:
          if (MSG_ready)
            begin
              if (is_last_block)
                begin
                  inner_digest_we = 1'b1;
                  hmac_ctrl_new   = CTRL_OPAD;
                end
              else
                begin
                  digest_valid_new = 1'b1;
                  digest_valid_we  = 1'b1;
                  hmac_ctrl_new    = CTRL_IDLE;
                end
              hmac_ctrl_we = 1'b1;
            end

        CTRL_OPAD:
          if (OPAD_ready)
            begin
              hmac_ctrl_new = CTRL_HMAC;
              hmac_ctrl_we  = 1'b1;
            end

        CTRL_HMAC:
          if (HMAC_ready)
            begin
              hmac_ctrl_new = CTRL_DONE;
              hmac_ctrl_we  = 1'b1;
            end

        CTRL_DONE:
          begin
            digest_valid_new = 1'b1;
            digest_valid_we  = 1'b1;
            hmac_ctrl_new    = CTRL_IDLE;
            hmac_ctrl_we     = 1'b1;
          end

        default:
          begin
            ready_flag       = 1'b0;
            digest_valid_new = 1'b0;
            digest_valid_we  = 1'b0;
            hmac_ctrl_new    = CTRL_IDLE;
            hmac_ctrl_we     = 1'b0;
          end

      endcase // case (hmac_ctrl_reg)
    end // hmac_ctrl_fsm

endmodule // hmac_core

//======================================================================
// EOF hmac_core.sv
//======================================================================
