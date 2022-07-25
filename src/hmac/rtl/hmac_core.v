//======================================================================
//
// Updated by: Emre Karabulut
// I updated the SHA function. The SHA was SHA-256 and now is SHA-384 
// I forced a parametric SHA-512 to work always as SHA-384, when I 
// instantiated. Addition to this, I had to update the data paths
//
// hmac_core.v
// -----------
//
//
// Author: Joachim Strombergson
// Copyright (c) 2018, Assured AB
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or
// without modification, are permitted provided that the following
// conditions are met:
//
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
// FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
// COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
// BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
// STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
// ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
//======================================================================

module hmac_core(
                 input wire            clk,
                 input wire            reset_n,

                 input wire            init,
                 input wire            next,

                 input wire [383 : 0]  key,

                 input wire [1023 : 0]  block,

                 output wire           ready,
                 output wire [383 : 0] tag,
                 output wire           tag_valid
                );


  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam IPAD       = 1024'h3636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636;
  localparam OPAD       = 1024'h5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c;
  localparam FINAL_PAD  = 640'h8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000580;


  //localparam STATE_IDLE   = 0;
  //localparam STATE_INIT   = 1;
  //localparam STATE_NEXT   = 2;
  //localparam STATE_FINAL  = 3;

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

  //reg [1 : 0] hmac_state_reg;
  //reg [1 : 0] hmac_state_new;
  //reg         hmac_state_we;

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

  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign ready      = ready_flag;
  assign tag        = H2_digest;
  assign tag_valid  = digest_valid_reg;
  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  sha384_core H1(
                     .clk(clk),
                     .reset_n(reset_n),

                     .init(H1_init),
                     .next(H1_next),

                     .work_factor(0),
                     .work_factor_num(0),

                     .block(H1_block),

                     .ready(H1_ready),
                     .digest(H1_digest),
                     .digest_valid(H1_digest_valid)
                    );

  sha384_core H2(
                     .clk(clk),
                     .reset_n(reset_n),

                     .init(H2_init),
                     .next(H2_next),

                     .work_factor(0),
                     .work_factor_num(0),

                     .block(H2_block),

                     .ready(H2_ready),
                     .digest(H2_digest),
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