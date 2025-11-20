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
// hmac_core.v
// --------
// working on HMAC-384 configuration
//
//
//======================================================================

module hmac_core
(
      // Clock and reset.
      input logic            clk,
      input logic            reset_n,
      input logic            zeroize,
      
      // Control.
      input logic            init_cmd,
      input logic            next_cmd,
      input logic            mode_cmd,
      output logic           ready,
      output logic           tag_valid,

      // Data ports.
      input logic [383 : 0]  lfsr_seed,

      input logic [511 : 0]  key,
      input logic [1023 : 0] block_msg,
      output logic [511 : 0] tag
    );


  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam bit [1023:0] IPAD       = 1024'h3636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636;
  localparam bit [1023:0] OPAD       = 1024'h5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c;
  localparam bit [639:0]  HMAC384_FINAL_PAD  = 640'h8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000580;
  localparam bit [511:0]  HMAC512_FINAL_PAD  = 512'h80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000600;
  localparam bit [191:0]  ENTROPY_PAD  = 192'h800000000000000000000000000000000000000000000340;

  localparam [2 : 0] CTRL_IDLE   = 3'd0;
  localparam [2 : 0] CTRL_IPAD   = 3'd1;
  localparam [2 : 0] CTRL_OPAD   = 3'd2;
  localparam [2 : 0] CTRL_HMAC   = 3'd3;
  localparam [2 : 0] CTRL_DONE   = 3'd4;

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------

  logic [2 : 0] hmac_ctrl_reg;
  logic [2 : 0] hmac_ctrl_new;
  logic         hmac_ctrl_we;
  logic [2 : 0] hmac_ctrl_last;

  logic         ready_flag;
  logic         digest_valid_reg; 
  logic         digest_valid_new;
  logic         digest_valid_we;

  logic [1023:0] key_opadded;
  logic [1023:0] key_ipadded;
  logic [1023:0] HMAC_padded;

  logic         first_round; 
  logic         IPAD_ready;
  logic         OPAD_ready;
  logic         HMAC_ready;
  logic [1:0]   mode_reg;

  logic             H1_init;
  logic             H1_next;
  logic  [1023 : 0] H1_block;
  logic             H1_ready;
  logic  [511 : 0]  H1_digest;
  logic             H1_digest_valid;

  logic             H2_init;
  logic             H2_next;
  logic  [1023 : 0] H2_block;
  logic             H2_ready;
  logic  [511 : 0]  H2_digest;
  logic             H2_digest_valid;

  logic             set_entropy;
  logic  [383 : 0]  entropy;
  logic  [1023: 0]  entropy_block;
  logic  [383 : 0]  entropy_digest;
  logic  [383 : 0]  lfsr_entropy;
  logic  [63 : 0]   counter_reg;

  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign ready      = ready_flag;
  assign tag        = digest_valid_reg? H2_digest : 512'b0;
  assign tag_valid  = digest_valid_reg;
  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  sha512_masked_core u_sha512_core_h1 
                     (
                     .clk(clk),
                     .reset_n(reset_n),
                     .zeroize(zeroize),

                     .init_cmd(H1_init),
                     .next_cmd(H1_next),
                     .mode(mode_reg),

                     .entropy(entropy[191 : 0]),

                     .block_msg(H1_block),

                     .ready(H1_ready),
                     .digest(H1_digest),
                     .digest_valid(H1_digest_valid)
                    );

  sha512_masked_core u_sha512_core_h2 
                     (
                     .clk(clk),
                     .reset_n(reset_n),
                     .zeroize(zeroize),

                     .init_cmd(H2_init),
                     .next_cmd(H2_next),
                     .mode(mode_reg),

                     .entropy(entropy[383 : 192]),

                     .block_msg(H2_block),

                     .ready(H2_ready),
                     .digest(H2_digest),
                     .digest_valid(H2_digest_valid)
                    );

  genvar i;
  generate 
      for (i=0; i < 12; i++) begin : gen_lfsr
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
          digest_valid_reg <= 0;
          hmac_ctrl_reg  <= CTRL_IDLE;
          hmac_ctrl_last <= CTRL_IDLE;
        end
      else if (zeroize)
        begin
          digest_valid_reg <= 0;
          hmac_ctrl_reg  <= CTRL_IDLE;
          hmac_ctrl_last <= CTRL_IDLE;
        end
      else
        begin
          hmac_ctrl_last <= hmac_ctrl_reg;

          if (digest_valid_we)
            digest_valid_reg <= digest_valid_new;

          if (hmac_ctrl_we)
            hmac_ctrl_reg <= hmac_ctrl_new;

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
    if (!reset_n) begin
      entropy_digest <= '0;
    end
    else if (set_entropy) begin
      entropy_digest <= H2_digest[383:0];
    end
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
  // state_logic
  //
  // The logic needed to init as well as update the state during
  // round processing.
  //----------------------------------------------------------------

 always_comb
    begin : state_fsm
      IPAD_ready = H1_ready;
      OPAD_ready = H1_ready & H2_ready;
      HMAC_ready = H2_ready;

      key_ipadded = {key, 512'b0} ^ IPAD;
      key_opadded = {key, 512'b0} ^ OPAD;
      HMAC_padded = mode_reg[0]? {H1_digest, HMAC512_FINAL_PAD}: 
                                 {H1_digest[511: 128], HMAC384_FINAL_PAD};
      
      H1_block = key_ipadded;
      H2_block = key_opadded;

      H1_init = 0;
      H1_next = 0;
      H2_init = 0;
      H2_next = 0;

      first_round = (hmac_ctrl_reg == hmac_ctrl_last)? 1'b0 : 1'b1;

      unique case (hmac_ctrl_reg)
        CTRL_IPAD:
          begin
            if (first_round)
              begin
                H1_init = 1;
                H1_next = 0;
                H2_init = 1;
                H2_next = 0;
                IPAD_ready = 0;
              end

            H2_block = entropy_block;
          end

        CTRL_OPAD:
          begin
            if (first_round)
              begin
                H1_init = 0;
                H1_next = 1;
                H2_init = 1;
                H2_next = 0;
                OPAD_ready = 0;
              end

            H1_block = block_msg;
          end

        CTRL_HMAC:
          begin
            if (first_round)
              begin
                H2_init = 0;
                H2_next = 1;  
                HMAC_ready = 0;  
              end
            
            H2_block = HMAC_padded;
          end

        default:
          begin
            H1_init = 0;
            H1_next = 0;
            H2_init = 0;
            H2_next = 0;
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
      ready_flag       = 0;
      digest_valid_new = 0;
      digest_valid_we  = 0;
      hmac_ctrl_new    = CTRL_IDLE;
      hmac_ctrl_we     = 0;

      set_entropy = 0;

      unique case (hmac_ctrl_reg)
        CTRL_IDLE:
          begin
            ready_flag = 1;

            if (init_cmd)
              begin
                digest_valid_new = 0;
                digest_valid_we  = 1;
                hmac_ctrl_new    = CTRL_IPAD;
                hmac_ctrl_we     = 1;
              end

            if (next_cmd)
              begin
                digest_valid_new = 0;
                digest_valid_we  = 1;
                hmac_ctrl_new    = CTRL_OPAD;
                hmac_ctrl_we     = 1;
              end
          end


        CTRL_IPAD:
          begin
            digest_valid_new = 0;
            digest_valid_we  = 1;
            if (IPAD_ready == 1)
              begin
                hmac_ctrl_new   = CTRL_OPAD;
                hmac_ctrl_we    = 1;
                set_entropy = 1;
              end
          end
        

        CTRL_OPAD:
          begin  
            digest_valid_new = 0;
            digest_valid_we  = 1;
            if (OPAD_ready == 1)
              begin
                hmac_ctrl_new   = CTRL_HMAC;
                hmac_ctrl_we    = 1;
              end
          end
        

        CTRL_HMAC:
          begin
            digest_valid_new = 0;
            digest_valid_we  = 1;
            if (HMAC_ready == 1)
              begin
                hmac_ctrl_new   = CTRL_DONE;
                hmac_ctrl_we    = 1;
              end
          end


        CTRL_DONE:
          begin
            digest_valid_new = 1;
            digest_valid_we  = 1;

            hmac_ctrl_new    = CTRL_IDLE;
            hmac_ctrl_we     = 1;
          end

        default:
          begin
            ready_flag       = 0;
            digest_valid_new = 0;
            digest_valid_we  = 0;
            hmac_ctrl_new    = CTRL_IDLE;
            hmac_ctrl_we     = 0;
          end
      
      endcase // case (hmac_ctrl_reg)
    end // hmac_ctrl_fsm

endmodule // hmac_core

//======================================================================
// EOF hmac_core.v
//======================================================================
