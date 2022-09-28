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
      input wire            clk,
      input wire            reset_n,
      
      // Control.
      input wire            init,
      input wire            next,
      output wire           ready,
      output wire           tag_valid,

      // Data ports.
      input wire [383 : 0]  key,
      input wire [1023 : 0]  block,
      output wire [383 : 0] tag
    );


  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam IPAD       = 1024'h3636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636;
  localparam OPAD       = 1024'h5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c;
  localparam FINAL_PAD  = 640'h8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000580;

  localparam CTRL_IDLE   = 0;
  localparam CTRL_IPAD   = 1;
  localparam CTRL_OPAD   = 2;
  localparam CTRL_HMAC   = 3;
  localparam CTRL_DONE   = 4;
  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------

  reg [2 : 0] hmac_ctrl_reg;
  reg [2 : 0] hmac_ctrl_new;
  reg         hmac_ctrl_we;
  reg [2 : 0] hmac_ctrl_last;

  reg         ready_flag;
  reg         digest_valid_reg; 
  reg         digest_valid_new;
  reg         digest_valid_we;

  reg [1023:0] key_opadded;
  reg [1023:0] key_ipadded;
  reg [1023:0] HMAC_padded;

  reg         first_round; 
  reg         IPAD_ready;
  reg         OPAD_ready;
  reg         HMAC_ready;
  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  reg             H1_init;
  reg             H1_next;
  reg  [1023 : 0] H1_block;
  wire            H1_ready;
  wire [383 : 0]  H1_digest;
  wire            H1_digest_valid;

  reg             H2_init;
  reg             H2_next;
  reg  [1023 : 0] H2_block;
  wire            H2_ready;
  wire [383 : 0]  H2_digest;
  wire            H2_digest_valid;
  wire [127:0]    garbage_bit_vector1,garbage_bit_vector2;

  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign ready      = ready_flag;
  assign tag        = H2_digest;
  assign tag_valid  = digest_valid_reg;
  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  sha512_core H1(
                     .clk(clk),
                     .reset_n(reset_n),

                     .init(H1_init),
                     .next(H1_next),
                     .mode(2'h2),

                     .work_factor(1'b0),
                     .work_factor_num(0),

                     .block(H1_block),

                     .ready(H1_ready),
                     .digest({H1_digest,garbage_bit_vector1}),
                     .digest_valid(H1_digest_valid)
                    );

  sha512_core H2(
                     .clk(clk),
                     .reset_n(reset_n),

                     .init(H2_init),
                     .next(H2_next),
                     .mode(2'h2),

                     .work_factor(1'b0),
                     .work_factor_num(0),

                     .block(H2_block),

                     .ready(H2_ready),
                     .digest({H2_digest,garbage_bit_vector2}),
                     .digest_valid(H2_digest_valid)
                    );

  //----------------------------------------------------------------
  // reg_update
  //
  // Update functionality for all registers in the core.
  // All registers are positive edge triggered with asynchronous
  // active low reset. All registers have write enable.
  //----------------------------------------------------------------
  always @ (posedge clk or negedge reset_n)
    begin : reg_update
      if (!reset_n)
        begin
          digest_valid_reg <= 0;
          hmac_ctrl_reg  <= CTRL_IDLE;
          hmac_ctrl_last <= CTRL_IDLE;
        end
      else
        begin
          if (digest_valid_we)
            digest_valid_reg <= digest_valid_new;

          if (hmac_ctrl_we)
            hmac_ctrl_reg <= hmac_ctrl_new;

          hmac_ctrl_last <= hmac_ctrl_reg;
        end
    end // reg_update

  //----------------------------------------------------------------
  // state_logic
  //
  // The logic needed to init as well as update the state during
  // round processing.
  //----------------------------------------------------------------

 always @*
    begin : state_fsm
      IPAD_ready = H1_ready;
      OPAD_ready = H1_ready & H2_ready;
      HMAC_ready = H2_ready;

      key_ipadded = {key, 640'b0} ^ IPAD;
      key_opadded = {key, 640'b0} ^ OPAD;
      HMAC_padded = {H1_digest, FINAL_PAD};
      
      H1_block = key_ipadded;
      H2_block = key_opadded;

      H1_init = 0;
      H1_next = 0;
      H2_init = 0;
      H2_next = 0;

      first_round = (hmac_ctrl_reg == hmac_ctrl_last)? 0 : 1;

      case (hmac_ctrl_reg)
        CTRL_IPAD:
          begin
            if (first_round)
              begin
                H1_init = 1;
                H1_next = 0;
                IPAD_ready = 0;
              end
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

            H1_block = block;  
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
          end
      endcase;
    end;

  //----------------------------------------------------------------
  // hmac_ctrl_fsm
  //
  // Logic for the state machine controlling the core behaviour.
  //----------------------------------------------------------------
  always @*
    begin : hmac_ctrl_fsm
      ready_flag       = 0;
      digest_valid_new = 0;
      digest_valid_we  = 0;
      hmac_ctrl_new    = CTRL_IDLE;
      hmac_ctrl_we     = 0;

      case (hmac_ctrl_reg)
        CTRL_IDLE:
          begin
            ready_flag = 1;

            if (init)
              begin
                digest_valid_new = 0;
                digest_valid_we  = 1;
                hmac_ctrl_new    = CTRL_IPAD;
                hmac_ctrl_we     = 1;
              end

            if (next)
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
      endcase // case (hmac_ctrl_reg)
    end // hmac_ctrl_fsm

endmodule // hmac_core

//======================================================================
// EOF hmac_core.v
//======================================================================
