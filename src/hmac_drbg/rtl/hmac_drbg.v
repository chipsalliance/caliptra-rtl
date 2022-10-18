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
// hmac_drbg.v
// ------
// HMAC384-drbg top-level wrapper with 384 bit data access.
// The module supports two different modes:
//
// Mode 0: Based on section 10.1.2. of NIST SP 800-90A, Rev 1:
//         "Recommendation for Random Number Generation Using 
//         Deterministic Random Bit Generators"
//         Functionality:
//         Using the given "seed", the module generates a random number 
//         with 384-bit. This mode is used in keygen operation in 
//         deterministic ECDSA. 
//         This mode is also used to generate different random numbers
//         by a given seed "IV" to feed side-channel countermeasures in
//         ECC architecture.
//
// Mode 1: Based on section 3.1. RFC 6979: "Deterministic Usage of the 
//         Digital Signature Algorithm (DSA) and Elliptic Curve Digital 
//         Signature Algorithm (ECDSA)"
//         Functionality:
//         Using the given "privkey" and "hashed_msg", this module 
//         generates a 384-bit nonce "k" used in signing operation in
//         deterministic ECDSA. 
// 
//
//======================================================================

module hmac_drbg  
#(
  parameter                  REG_SIZE        = 384,
  parameter                  SEED_SIZE       = 384,
  parameter [REG_SIZE-1 : 0] HMAC_DRBG_PRIME = 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973
)    
(
  // Clock and reset.
  input wire                        clk,
  input wire                        reset_n,

  //Control
  input wire                        mode,
  input wire                        init_cmd,
  input wire                        next_cmd,
  output wire                       ready,
  output wire                       valid,

  //Data
  input wire   [SEED_SIZE-1 : 0]    seed,
  input wire   [REG_SIZE-1  : 0]    privkey,
  input wire   [REG_SIZE-1  : 0]    hashed_msg,
  output wire  [REG_SIZE-1  : 0]    nonce
);

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam [REG_SIZE-1 : 0] V_init = 384'h010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101;
  localparam [REG_SIZE-1 : 0] K_init = 384'h000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;

  localparam CNT_SIZE = 8;
  localparam [1024-REG_SIZE-SEED_SIZE-CNT_SIZE-1-12-1 : 0] ZERO_PAD_MODE0_K   = '0; // 1 for header and 12 bit for message length  
  localparam [1024-REG_SIZE-1-12-1 : 0] ZERO_PAD_V         = '0; // 1 for header and 12 bit for message length  

  localparam [11 : 0] MODE0_K_SIZE  = 12'd1024 + REG_SIZE + SEED_SIZE + CNT_SIZE;
  localparam [11 : 0] V_SIZE        = 12'd1024 + REG_SIZE;

  /*STATES*/
  localparam [4 : 0] NONCE_IDLE_ST      = 5'd0;  // IDLE WAIT and Return step
  localparam [4 : 0] MODE0_INIT_ST      = 5'd1;
  localparam [4 : 0] MODE0_NEXT_ST      = 5'd2;
  localparam [4 : 0] MODE0_K1_ST        = 5'd3;  // K = HMAC_K(V || 0x00 || seed)
  localparam [4 : 0] MODE0_V1_ST        = 5'd4;  // V = HMAC_K(V) 
  localparam [4 : 0] MODE0_K2_INIT_ST   = 5'd5;
  localparam [4 : 0] MODE0_K2_ST        = 5'd6;  // K = HMAC_K(V || 0x01 || seed) 
  localparam [4 : 0] MODE0_V2_ST        = 5'd7;  // V = HMAC_K(V) 
  localparam [4 : 0] MODE0_DONE_ST      = 5'd8;

  localparam [4 : 0] MODE1_INIT_ST      = 5'd16;
  localparam [4 : 0] MODE1_NEXT_ST      = 5'd17;
  localparam [4 : 0] MODE1_K10_ST       = 5'd18;  // K = HMAC_K(V || 0x00 || privKey || h1) ->long message 
  localparam [4 : 0] MODE1_K11_ST       = 5'd19;  // K = HMAC_K(V || 0x00 || privKey || h1) ->long message 
  localparam [4 : 0] MODE1_V1_ST        = 5'd20;  // V = HMAC_K(V) 
  localparam [4 : 0] MODE1_K20_INIT_ST  = 5'd21;
  localparam [4 : 0] MODE1_K20_ST       = 5'd22;  // K = HMAC_K(V || 0x01 || privKey || h1) ->long message 
  localparam [4 : 0] MODE1_K21_ST       = 5'd23;  // K = HMAC_K(V || 0x01 || privKey || h1) ->long message 
  localparam [4 : 0] MODE1_V2_ST        = 5'd24;  // V = HMAC_K(V) 
  localparam [4 : 0] MODE1_T_ST         = 5'd25;  // T = HMAC_K(V) 
  localparam [4 : 0] MODE1_CHCK_ST      = 5'd26;  // Return T if T is within the [1,q-1] range, otherwise: 
  localparam [4 : 0] MODE1_K3_ST        = 5'd27;  // K = HMAC_K(V || 0x00) 
  localparam [4 : 0] MODE1_V3_ST        = 5'd28;  // V = HMAC_K(V) and Jump to SIGN_T2_ST 
  localparam [4 : 0] MODE1_DONE_ST      = 5'd29;

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  
  /*State register*/
  reg [4:0]  nonce_st_reg;
  reg [4:0]  nonce_next_st;
  reg [4:0]  nonce_st_reg_last;
  
  reg                   ready_reg;
  reg                   valid_reg;
  reg [REG_SIZE-1 : 0]  nonce_reg;
  reg [CNT_SIZE-1 : 0]  cnt_reg;
  reg                   first_round;
  reg                   HMAC_tag_valid_last;
  reg                   HMAC_tag_valid_edge;


  reg [REG_SIZE-1:0]    K_reg;
  reg [REG_SIZE-1:0]    V_reg;

  //----------------------------------------------------------------
  // Register/Wires for HMAC-384 module instantiation.
  //----------------------------------------------------------------
  reg                   HMAC_init;
  reg                   HMAC_next;
  reg  [1023:0]         HMAC_block;
  reg  [REG_SIZE-1:0]   HMAC_key;

  wire                  HMAC_ready;
  wire                  HMAC_tag_valid;
  wire [REG_SIZE-1:0]   HMAC_tag;

  //----------------------------------------------------------------
  // HMAC module instantiation.
  //----------------------------------------------------------------
  hmac_core HMAC_K
  (
   .clk(clk),
   .reset_n(reset_n),
   .init_cmd(HMAC_init),
   .next_cmd(HMAC_next),
   .key(HMAC_key),
   .block_msg(HMAC_block),
   .ready(HMAC_ready),
   .tag(HMAC_tag),
   .tag_valid(HMAC_tag_valid)
  );

  //----------------------------------------------------------------
  // reg_update
  // Update functionality for all registers in the core.
  //----------------------------------------------------------------
  
  always @*
  begin : edge_detector
    first_round = (nonce_st_reg == nonce_st_reg_last)? 1'b0 : 1'b1;
    HMAC_tag_valid_edge = HMAC_tag_valid & (!HMAC_tag_valid_last);
  end // edge_detector

  always @ (posedge clk or negedge reset_n) 
  begin
    if (!reset_n)
      HMAC_tag_valid_last <= '0;
    else 
      HMAC_tag_valid_last <= HMAC_tag_valid;
  end

  always @ (posedge clk or negedge reset_n) 
  begin
    if (!reset_n)
      ready_reg   <= '0; 
    else
      ready_reg   <= (nonce_st_reg == NONCE_IDLE_ST);
  end

  always @ (posedge clk or negedge reset_n) 
  begin : valid_nonce_regs_updates
    if (!reset_n) begin
      valid_reg   <= 0;
      nonce_reg   <= '0;
    end
    else
    begin
      case(nonce_st_reg)
        NONCE_IDLE_ST: begin
          if (init_cmd | next_cmd)
            valid_reg    <= 0;
        end

        MODE0_DONE_ST: begin
          nonce_reg   <= HMAC_tag;
          valid_reg   <= HMAC_tag_valid;
        end

        MODE1_DONE_ST: begin
          nonce_reg   <= HMAC_tag;
          valid_reg   <= HMAC_tag_valid;
        end

        default: begin
          valid_reg   <= 0;
          nonce_reg   <= '0;
        end
      endcase
    end
  end // valid_nonce_regs_updates

  always @ (posedge clk or negedge reset_n) 
  begin : hmac_inputs_update
    if (!reset_n) begin
      HMAC_init <= 0;
      HMAC_next <= 0;
      K_reg   <= '0;
      V_reg   <= '0;
    end
    else begin
      HMAC_init <= 0;
      HMAC_next <= 0;
      if (first_round) begin
        unique casez(nonce_st_reg)
          MODE0_INIT_ST: begin
            K_reg   <= K_init;
            V_reg   <= V_init;
          end

          MODE0_K1_ST: begin
            HMAC_init <= 1;
          end

          MODE0_V1_ST: begin
            HMAC_init <= 1;
            K_reg   <= HMAC_tag;
          end

          MODE0_K2_ST: begin
            HMAC_init <= 1;
            V_reg   <= HMAC_tag;
          end 

          MODE0_V2_ST: begin
            HMAC_init <= 1;
            K_reg   <= HMAC_tag;
          end

          MODE0_DONE_ST: begin
            V_reg   <= HMAC_tag;
          end

          MODE1_INIT_ST: begin
            K_reg   <= K_init;
            V_reg   <= V_init;
          end

          MODE1_K10_ST: begin
            HMAC_init <= 1;
          end

          MODE1_K11_ST: begin
            HMAC_next <= 1;
          end

          MODE1_V1_ST: begin
            HMAC_init <= 1;
            K_reg   <= HMAC_tag;
          end

          MODE1_K20_ST: begin
            HMAC_init <= 1;
            V_reg   <= HMAC_tag;
          end 

          MODE1_K21_ST: begin
            HMAC_next <= 1;
          end 

          MODE1_V2_ST: begin
            HMAC_init <= 1;
            K_reg   <= HMAC_tag;
          end

          MODE1_T_ST: begin
            HMAC_init <= 1;
            V_reg   <= HMAC_tag;
          end 

          MODE1_K3_ST: begin
            HMAC_init <= 1;
          end

          MODE1_V3_ST: begin
            HMAC_init <= 1;
            K_reg   <= HMAC_tag;
          end 
              
          MODE1_DONE_ST: begin
            V_reg   <= HMAC_tag;
          end

          default: begin
            HMAC_init <= 0;
            HMAC_next <= 0;
          end 

        endcase;
      end
    end
  end // hmac_inputs_update

  always @*
  begin : hmac_block_update
    HMAC_key = K_reg;
    unique casez(nonce_st_reg)
      MODE0_K1_ST:    HMAC_block  = {V_reg, cnt_reg, seed, 1'h1, ZERO_PAD_MODE0_K, MODE0_K_SIZE};
      MODE0_V1_ST:    HMAC_block  = {V_reg, 1'h1, ZERO_PAD_V, V_SIZE};
      MODE0_K2_ST:    HMAC_block  = {V_reg, cnt_reg, seed, 1'h1, ZERO_PAD_MODE0_K, MODE0_K_SIZE};
      MODE0_V2_ST:    HMAC_block  = {V_reg, 1'h1, ZERO_PAD_V, V_SIZE};
      MODE1_K10_ST:   HMAC_block  = {V_reg, cnt_reg, privkey, hashed_msg[383:136]};
      MODE1_K11_ST:   HMAC_block  = {hashed_msg[135:0], 1'h1, 875'b0, 12'h888};
      MODE1_V1_ST:    HMAC_block  = {V_reg, 1'h1, ZERO_PAD_V, V_SIZE};
      MODE1_K20_ST:   HMAC_block  = {V_reg, cnt_reg, privkey, hashed_msg[383:136]};
      MODE1_K21_ST:   HMAC_block  = {hashed_msg[135:0], 1'h1, 875'b0, 12'h888};
      MODE1_V2_ST:    HMAC_block  = {V_reg, 1'h1, ZERO_PAD_V, V_SIZE};
      MODE1_T_ST:     HMAC_block  = {V_reg, 1'h1, ZERO_PAD_V, V_SIZE};
      MODE1_K3_ST:    HMAC_block  = {V_reg, 8'h00, 1'h1, 619'b0, 12'h578};
      MODE1_V3_ST:    HMAC_block  = {V_reg, 1'h1, ZERO_PAD_V, V_SIZE};
      default:        HMAC_block  = '0;
    endcase;
  end // hmac_block_update
     
  always @ (posedge clk or negedge reset_n) 
  begin : cnt_reg_update
    if (!reset_n)
      cnt_reg    <= '0;
    else begin
      case(nonce_st_reg)
        MODE0_INIT_ST:      cnt_reg    <= '0;
        MODE1_INIT_ST:      cnt_reg    <= '0;
        MODE0_NEXT_ST:      cnt_reg    <= cnt_reg + 1;
        MODE1_NEXT_ST:      cnt_reg    <= cnt_reg + 1;
        MODE0_K2_INIT_ST:   cnt_reg    <= cnt_reg + 1;
        MODE1_K20_INIT_ST:  cnt_reg    <= cnt_reg + 1;
        default:            cnt_reg    <= cnt_reg;
      endcase
    end
  end // cnt_reg_update

  always @ (posedge clk or negedge reset_n) 
  begin : state_update
    if (!reset_n) 
      nonce_st_reg      <= NONCE_IDLE_ST;
    else 
      nonce_st_reg      <= nonce_next_st;
  end // state_update

  always @ (posedge clk or negedge reset_n) 
  begin : ff_state_update
    if (!reset_n) 
      nonce_st_reg_last <= NONCE_IDLE_ST;
    else 
      nonce_st_reg_last <= nonce_st_reg;
  end // ff_state_update
   
  //----------------------------------------------------------------
  // FSM_flow
  //
  // This FSM starts with the init command and then generates a nonce.
  // Active low and async reset.
  //----------------------------------------------------------------

  always @*
  begin: state_logic
    case(nonce_st_reg)
      NONCE_IDLE_ST: // IDLE WAIT
      begin
        if (HMAC_ready) begin
          case ({init_cmd, next_cmd, mode})  // check the mode
            3'b100 :    nonce_next_st    = MODE0_INIT_ST;
            3'b101 :    nonce_next_st    = MODE1_INIT_ST;
            3'b010 :    nonce_next_st    = MODE0_NEXT_ST;
            3'b011 :    nonce_next_st    = MODE1_NEXT_ST;
            default:    nonce_next_st    = NONCE_IDLE_ST;
          endcase
        end
        else
          nonce_next_st    = NONCE_IDLE_ST;
      end

      MODE0_INIT_ST:
      begin
        nonce_next_st    = MODE0_K1_ST;
      end

      MODE0_NEXT_ST:
      begin
        nonce_next_st    = MODE0_K1_ST;
      end

      MODE0_K1_ST:
      begin
        if (HMAC_tag_valid_edge)
          nonce_next_st    = MODE0_V1_ST;
        else
          nonce_next_st    = MODE0_K1_ST;
      end

      MODE0_V1_ST:
      begin
        if (HMAC_tag_valid_edge)
          nonce_next_st    = MODE0_K2_INIT_ST;
        else
          nonce_next_st    = MODE0_V1_ST;
      end

      MODE0_K2_INIT_ST:
      begin
          nonce_next_st    = MODE0_K2_ST;
      end

      MODE0_K2_ST:
      begin
        if (HMAC_tag_valid_edge)
          nonce_next_st    = MODE0_V2_ST;
        else
          nonce_next_st    = MODE0_K2_ST;
      end

      MODE0_V2_ST:
      begin
        if (HMAC_tag_valid_edge)
          nonce_next_st    = MODE0_DONE_ST;
        else
          nonce_next_st    = MODE0_V2_ST;
      end

      MODE0_DONE_ST:
      begin
        nonce_next_st    = NONCE_IDLE_ST;
      end

      MODE1_INIT_ST:
      begin
        nonce_next_st    = MODE1_K10_ST;
      end

      MODE1_NEXT_ST:
      begin
        nonce_next_st    = MODE1_K10_ST;
      end

      MODE1_K10_ST:
      begin
        if (HMAC_tag_valid_edge)
          nonce_next_st    = MODE1_K11_ST;
        else
          nonce_next_st    = MODE1_K10_ST;
      end

      MODE1_K11_ST:
      begin
        if (HMAC_tag_valid_edge)
          nonce_next_st    = MODE1_V1_ST;
        else
          nonce_next_st    = MODE1_K11_ST;
      end

      MODE1_V1_ST:
      begin
        if (HMAC_tag_valid_edge)
          nonce_next_st    = MODE1_K20_INIT_ST;
        else
          nonce_next_st    = MODE1_V1_ST;
      end

      MODE1_K20_INIT_ST:
      begin
        nonce_next_st    = MODE1_K20_ST;
      end

      MODE1_K20_ST:
      begin
        if (HMAC_tag_valid_edge)
          nonce_next_st    = MODE1_K21_ST;
        else
          nonce_next_st    = MODE1_K20_ST;
      end

      MODE1_K21_ST:
      begin
        if (HMAC_tag_valid_edge)
          nonce_next_st    = MODE1_V2_ST;
        else
          nonce_next_st    = MODE1_K21_ST;
      end

      MODE1_V2_ST:
      begin
        if (HMAC_tag_valid_edge)
          nonce_next_st    = MODE1_T_ST;
        else
          nonce_next_st    = MODE1_V2_ST;
      end

      MODE1_T_ST:
      begin
        if (HMAC_tag_valid_edge)
          nonce_next_st    = MODE1_CHCK_ST;
        else
          nonce_next_st    = MODE1_T_ST;
      end

      MODE1_CHCK_ST:
      begin
        if ((HMAC_tag==0) || (HMAC_tag > HMAC_DRBG_PRIME))
          nonce_next_st    = MODE1_K3_ST;
        else
          nonce_next_st    = MODE1_DONE_ST;
      end

      MODE1_K3_ST:
      begin
        if (HMAC_tag_valid_edge)
          nonce_next_st    = MODE1_V3_ST;
        else
          nonce_next_st    = MODE1_K3_ST;
      end

      MODE1_V3_ST:
      begin
        if (HMAC_tag_valid_edge)
          nonce_next_st    = MODE1_T_ST;
        else
          nonce_next_st    = MODE1_V3_ST;
      end

      MODE1_DONE_ST:
      begin
        nonce_next_st    = NONCE_IDLE_ST;
      end

      default:
      begin
        nonce_next_st    = NONCE_IDLE_ST;
      end

    endcase
  end //state_logic

  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign ready = ready_reg; 
  assign valid = valid_reg;
  assign nonce = nonce_reg;

endmodule // hmac_drbg

//======================================================================
// EOF hmac_drbg.v
//======================================================================
