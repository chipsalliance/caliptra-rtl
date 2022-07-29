//======================================================================
//
// Updated by: Emre Karabulut
// Updated locations: 
//          Line 57 IV was added in the port list.
//          Line 139 IV was XORed with plaintext.
//          Line 193-245 has an always block to store IV values for
//              the next encry/decry due to the chain requirement
//          Line 261 IV was XORed with decrypted ciphertext.
// aes_core_cbc.v
// ----------
// The AES core. This core supports key size of 128, and 256 bits.
// Most of the functionality is within the submodules.
//
//
// Author: Joachim Strombergson
// Copyright (c) 2013, 2014, Secworks Sweden AB
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

`default_nettype none

module aes_core_cbc(
                // Clock and reset.
                input wire            clk,
                input wire            reset_n,

                // Control.
                input wire            encdec,
                input wire            init,
                input wire            next,
                output wire           ready,

                //Data.
                input wire [255 : 0]  key,
                input wire            keylen,
                input wire [127 : 0]  IV,
                input wire            IV_updated,
                input wire [127 : 0]  block,
                output wire [127 : 0] result,
                output wire           result_valid
               );




  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam CTRL_IDLE  = 2'h0;
  localparam CTRL_INIT  = 2'h1;
  localparam CTRL_NEXT  = 2'h2;


  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  reg [1 : 0] aes_core_ctrl_reg;
  reg [1 : 0] aes_core_ctrl_new;
  reg         aes_core_ctrl_we;

  reg         result_valid_reg;
  reg         result_valid_new;
  reg         result_valid_we;

  reg         ready_reg;
  reg         ready_new;
  reg         ready_we;


  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  reg            init_state;

  wire [127 : 0] round_key;
  wire           key_ready;

  reg            enc_next;
  wire [3 : 0]   enc_round_nr;
  wire [127 : 0] enc_new_block;
  wire           enc_ready;
  wire [31 : 0]  enc_sboxw;

  reg            dec_next;
  wire [3 : 0]   dec_round_nr;
  wire [127 : 0] dec_new_block;
  wire           dec_ready;

  reg [127 : 0]  muxed_new_block;
  reg [3 : 0]    muxed_round_nr;
  reg            muxed_ready;

  wire [31 : 0]  keymem_sboxw;

/* verilator lint_off UNOPTFLAT */
  reg [31 : 0]   muxed_sboxw;
  wire [31 : 0]  new_sboxw;
/* verilator lint_on UNOPTFLAT */

/* IV registers for chain based encryption */
  reg [127 : 0]  IV_encry;
  reg [127 : 0]  IV_decry;
  reg [127 : 0]  IV_decry_next;
  reg IV_updated_delayed;


  //----------------------------------------------------------------
  // Instantiations.
  //----------------------------------------------------------------
  aes_encipher_block enc_block(
                               .clk(clk),
                               .reset_n(reset_n),

                               .next(enc_next),

                               .keylen(keylen),
                               .round(enc_round_nr),
                               .round_key(round_key),

                               .sboxw(enc_sboxw),
                               .new_sboxw(new_sboxw),

                               .block(block^IV_encry),
                               .new_block(enc_new_block),
                               .ready(enc_ready)
                              );


  aes_decipher_block dec_block(
                               .clk(clk),
                               .reset_n(reset_n),

                               .next(dec_next),

                               .keylen(keylen),
                               .round(dec_round_nr),
                               .round_key(round_key),

                               .block(block),
                               .new_block(dec_new_block),
                               .ready(dec_ready)
                              );


  aes_key_mem keymem(
                     .clk(clk),
                     .reset_n(reset_n),

                     .key(key),
                     .keylen(keylen),
                     .init(init),

                     .round(muxed_round_nr),
                     .round_key(round_key),
                     .ready(key_ready),

                     .sboxw(keymem_sboxw),
                     .new_sboxw(new_sboxw)
                    );


  aes_sbox sbox_inst(.sboxw(muxed_sboxw), .new_sboxw(new_sboxw));

  //----------------------------------------------------------------
  // IV Storage for Encryption and Decryption
  // FSM design for IV value storage
  // 
  // Since the IV is used to encry/decry next block, the IV should 
  // be preserved and updated after each encry/decry. The following
  // FSM provides this functionality
  //----------------------------------------------------------------

  reg IV_enc_state;
  reg [1:0]IV_dec_state;
  localparam st_IV_engine_idle  = 0,
             st_IV_engine_stars = 1,
             st_IV_1st_decrypt  = 2;

  always @ (posedge clk or negedge reset_n)
  begin:IV_storage_management
      if (!reset_n)
        begin
          IV_encry            <= 128'h0;
          IV_decry            <= 128'h0;
          IV_decry_next       <= 128'h0;
          IV_enc_state        <= st_IV_engine_idle;
          IV_dec_state        <= st_IV_engine_idle;
          IV_updated_delayed  <= 1'b0;
        end
      else
        begin
            IV_updated_delayed <= IV_updated;
        // ENCRYPTION IV CONTROLLER
            if(IV_updated_delayed)
                IV_encry <= IV;
            else if ((IV_enc_state == st_IV_engine_stars) && enc_ready)
                IV_encry <= enc_new_block;
            else
                IV_encry <= IV_encry;

            case (IV_enc_state)
                st_IV_engine_idle:
                begin
                    if(enc_ready & enc_next)
                        IV_enc_state <= st_IV_engine_stars;
                    else
                        IV_enc_state <= st_IV_engine_idle;                 
                end
                st_IV_engine_stars:
                begin
                    if (IV_updated_delayed)
                        IV_enc_state <= st_IV_engine_idle; 
                    else if(enc_ready)
                        IV_enc_state <= st_IV_engine_idle;
                    else
                        IV_enc_state <= st_IV_engine_stars;                 
                end
                default: 
                    IV_enc_state <= st_IV_engine_idle;  
            endcase //IV_enc_state

        // DECRYPTION IV CONTROLLER
            case (IV_dec_state)
                st_IV_engine_idle:
                begin
                    IV_decry_next <= block;
                    IV_decry      <= IV;
                    if(dec_ready & dec_next)
                        IV_dec_state <= st_IV_1st_decrypt;
                    else
                        IV_dec_state <= st_IV_engine_idle;                 
                end
                st_IV_1st_decrypt:
                begin                    
                    if(IV_updated_delayed)
                    begin
                        IV_decry_next <= IV;
                        IV_decry      <= IV;
                        IV_dec_state  <= st_IV_engine_idle;
                    end
                    else if(dec_ready & dec_next)
                    begin
                        IV_dec_state  <= st_IV_engine_stars;
                        IV_decry_next <= block;
                        IV_decry      <= IV_decry_next;
                    end
                    else
                    begin
                        IV_dec_state  <= st_IV_1st_decrypt;
                        IV_decry_next <= IV_decry_next;
                        IV_decry      <= IV_decry;
                    end              
                end
                st_IV_engine_stars:
                begin
                    IV_dec_state  <= st_IV_1st_decrypt;
                    IV_decry_next <= IV_decry_next;
                    IV_decry      <= IV_decry;             
                end
                default:
                begin 
                    IV_dec_state <= st_IV_engine_idle;  
                    IV_decry_next <= IV;
                    IV_decry      <= IV;
                end
            endcase //IV_dec_state             
        end
  end //IV_storage_management




  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign ready        = ready_reg;
  assign result       = muxed_new_block;
  assign result_valid = result_valid_reg;


  //----------------------------------------------------------------
  // reg_update
  //
  // Update functionality for all registers in the core.
  // All registers are positive edge triggered with asynchronous
  // active low reset. All registers have write enable.
  //----------------------------------------------------------------
  always @ (posedge clk or negedge reset_n)
    begin: reg_update
      if (!reset_n)
        begin
          result_valid_reg  <= 1'b0;
          ready_reg         <= 1'b1;
          aes_core_ctrl_reg <= CTRL_IDLE;
        end
      else
        begin
          if (result_valid_we)
            result_valid_reg <= result_valid_new;

          if (ready_we)
            ready_reg <= ready_new;

          if (aes_core_ctrl_we)
            aes_core_ctrl_reg <= aes_core_ctrl_new;
        end
    end // reg_update


  //----------------------------------------------------------------
  // sbox_mux
  //
  // Controls which of the encipher datapath or the key memory
  // that gets access to the sbox.
  //----------------------------------------------------------------
  always @*
    begin : sbox_mux
      if (init_state)
        begin
          muxed_sboxw = keymem_sboxw;
        end
      else
        begin
          muxed_sboxw = enc_sboxw;
        end
    end // sbox_mux


  //----------------------------------------------------------------
  // encdex_mux
  //
  // Controls which of the datapaths that get the next signal, have
  // access to the memory as well as the block processing result.
  //----------------------------------------------------------------
  always @*
    begin : encdec_mux
      enc_next = 1'b0;
      dec_next = 1'b0;

      if (encdec)
        begin
          // Encipher operations
          enc_next        = next;
          muxed_round_nr  = enc_round_nr;
          muxed_new_block = enc_new_block;
          muxed_ready     = enc_ready;
        end
      else
        begin
          // Decipher operations
          dec_next        = next;
          muxed_round_nr  = dec_round_nr;
          muxed_new_block = dec_new_block^IV_decry;
          muxed_ready     = dec_ready;
        end
    end // encdec_mux


  //----------------------------------------------------------------
  // aes_core_ctrl
  //
  // Control FSM for aes core. Basically tracks if we are in
  // key init, encipher or decipher modes and connects the
  // different submodules to shared resources and interface ports.
  //----------------------------------------------------------------
  always @*
    begin : aes_core_ctrl
      init_state        = 1'b0;
      ready_new         = 1'b0;
      ready_we          = 1'b0;
      result_valid_new  = 1'b0;
      result_valid_we   = 1'b0;
      aes_core_ctrl_new = CTRL_IDLE;
      aes_core_ctrl_we  = 1'b0;

      case (aes_core_ctrl_reg)
        CTRL_IDLE:
          begin
            if (init)
              begin
                init_state        = 1'b1;
                ready_new         = 1'b0;
                ready_we          = 1'b1;
                result_valid_new  = 1'b0;
                result_valid_we   = 1'b1;
                aes_core_ctrl_new = CTRL_INIT;
                aes_core_ctrl_we  = 1'b1;
              end
            else if (next)
              begin
                init_state        = 1'b0;
                ready_new         = 1'b0;
                ready_we          = 1'b1;
                result_valid_new  = 1'b0;
                result_valid_we   = 1'b1;
                aes_core_ctrl_new = CTRL_NEXT;
                aes_core_ctrl_we  = 1'b1;
              end
          end

        CTRL_INIT:
          begin
            init_state = 1'b1;

            if (key_ready)
              begin
                ready_new         = 1'b1;
                ready_we          = 1'b1;
                aes_core_ctrl_new = CTRL_IDLE;
                aes_core_ctrl_we  = 1'b1;
              end
          end

        CTRL_NEXT:
          begin
            init_state = 1'b0;

            if (muxed_ready)
              begin
                ready_new         = 1'b1;
                ready_we          = 1'b1;
                result_valid_new  = 1'b1;
                result_valid_we   = 1'b1;
                aes_core_ctrl_new = CTRL_IDLE;
                aes_core_ctrl_we  = 1'b1;
             end
          end

        default:
          begin

          end
      endcase // case (aes_core_ctrl_reg)

    end // aes_core_ctrl
endmodule // aes_core

//======================================================================
// EOF aes_core.v
//======================================================================
