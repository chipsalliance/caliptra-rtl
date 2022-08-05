//======================================================================
// 
// A module draft for HMAC DRBG design.
//
//
// Author: Emre Karabulut
//======================================================================

module hmac_drbg  
#(
  parameter SEED_LENGTH = 384
)    
(
  // Clock and reset.
  input wire                        clk,
  input wire                        reset_n,

  //Control
  input wire                        KEYGEN_SIGN,
  input wire                        init,
  output wire                       ready,
  output wire                       valid,

  //Data
  input wire   [SEED_LENGTH-1 : 0]  seed,
  input wire   [383 : 0]            privKey,
  input wire   [383 : 0]            h1,
  output wire  [383 : 0]            nonce

);

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  `include "hmac_drbg_param.sv"

  localparam V_init = 384'h010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101;
  localparam K_init = 384'h000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  reg         ready_reg;
  reg         valid_reg;

  reg [383:0] nonce_reg;

  /*Division for hashed message*/
  reg   [135:0] h1_135_0_bits;
  reg   [247:0] h1_383_136_bits;

  //----------------------------------------------------------------
  // Register/Wires for HMAC module instantiation.
  //----------------------------------------------------------------
  reg             HMAC_init;
  reg             HMAC_next;
  reg  [1023:0]   HMAC_block;
  reg  [383:0]    HMAC_key;

  wire            HMAC_ready,HMAC_tag_valid;
  wire [383:0]    HMAC_tag;

  //----------------------------------------------------------------
  // HMAC module instantiation.
  //----------------------------------------------------------------
  hmac_core HMAC_K
  (
   .clk(clk),
   .reset_n(reset_n),
   .init(HMAC_init),
   .next(HMAC_next),  // There will be no next message! 
   .key(HMAC_key),
   .block(HMAC_block),
   .ready(HMAC_ready),
   .tag(HMAC_tag),
   .tag_valid(HMAC_tag_valid)
  );

  //----------------------------------------------------------------
  // HMAC DRBG Port Assignments
  //----------------------------------------------------------------

  assign ready            = ready_reg;
  assign nonce            = nonce_reg;
  assign valid            = valid_reg;

  //----------------------------------------------------------------
  // FSM_flow
  //
  // This FSM starts with the init command and then generates a nonce.
  // Active low and async reset.
  //----------------------------------------------------------------

  /*State register*/
  reg [3:0]  nonce_st;
  /*STATES*/
  localparam NONCE_IDLE_ST    = 0,  // IDLE WAIT and Return step
             KEYGEN_K1_ST     = 1,  // K = HMAC_K(V || 0x00 || seed)
             KEYGEN_V1_ST     = 2,  // V = HMAC_K(V) 
             KEYGEN_K2_ST     = 3,  // K = HMAC_K(V || 0x01 || seed) 
             KEYGEN_V2_ST     = 4,  // V = HMAC_K(V) 
             SIGN_K1_1_ST     = 5,  // K = HMAC_K(V || 0x00 || privKey || h1) ->long message 
             SIGN_K1_2_ST     = 6,  // K = HMAC_K(V || 0x00 || privKey || h1) ->long message 
             SIGN_V1_1_ST     = 7,  // V = HMAC_K(V) 
             SIGN_V1_2_ST     = 8,  // K = HMAC_K(V || 0x01 || privKey || h1) ->long message 
             SIGN_K2_ST       = 9,  // K = HMAC_K(V || 0x01 || privKey || h1) ->long message 
             SIGN_V2_ST       = 10, // V = HMAC_K(V) 
             SIGN_T1_ST       = 11, // Set T = [] 
             SIGN_T2_ST       = 12, // T = T || HMAC_K(V) 
             SIGN_CHCK_ST     = 13, // Return T if T is within the [1,q-1] range, otherwise: 
             SIGN_K3_ST       = 14, // K = HMAC_K(V || 0x00) 
             SIGN_V3_ST       = 15; // V = HMAC_K(V) and Jump to SIGN_T2_ST 


  always @ (posedge clk or negedge reset_n) begin: nonce_fsm
    if (!reset_n)
    begin
      nonce_st    <= NONCE_IDLE_ST;

      //HMAC registers
      HMAC_init   <= 1'h0;
      HMAC_next   <= 1'h0;
      HMAC_block  <= 1023'h0;
      HMAC_key    <= 384'h0;

      //DRBG registers
      ready_reg       <= 1'h0;
      valid_reg       <= 1'h0;
      nonce_reg       <= 384'h0;
      h1_135_0_bits   <= 136'h0;
      h1_383_136_bits <= 248'h0;

    end
    else
    begin
      case(nonce_st)
        NONCE_IDLE_ST  : // IDLE WAIT
        begin

          if ( (KEYGEN_SIGN == HMAC_DRBG_KEYGEN) && init && HMAC_ready) // BRANCH2KEYGEN
          begin
            nonce_st    <= KEYGEN_K1_ST;
            HMAC_init   <= 1'h1;
            HMAC_block  <= {V_init, 8'h00, seed, 1'h1, {HMAC_DRBG_GARBAGE_LENGTH{ 1'b0 }}, 12'h708};
            ready_reg   <= 1'h0;
            valid_reg   <= 1'h0;
          end
          else if ( (KEYGEN_SIGN == HMAC_DRBG_SIGNING) && init && HMAC_ready) // BRANCH2SIGNING
          begin
            nonce_st    <= SIGN_K1_1_ST;
            HMAC_init   <= 1'h1;
            HMAC_block  <= {V_init, 8'h00, privKey, h1[383:136]};
            ready_reg   <= 1'h0;
            valid_reg   <= 1'h0;
          end
          else
          begin
            nonce_st    <= NONCE_IDLE_ST;
            HMAC_init   <= 1'h0;
            HMAC_block  <= 1023'h0;
            ready_reg   <= 1'h1;
            valid_reg   <= valid_reg;
          end

          //HMAC registers
          HMAC_key    <= K_init;
          HMAC_next   <= 1'h0;

          //DRBG register
          nonce_reg   <= nonce_reg;
          h1_135_0_bits   <= h1[135:0];
          h1_383_136_bits <= h1[383:136];
          
        end
        KEYGEN_K1_ST   : // K = HMAC_K(V || 0x00 || seed)
        begin            // K is generated when it comes here

          if (HMAC_tag_valid && !HMAC_init && !HMAC_next )
          begin
            nonce_st    <= KEYGEN_V1_ST;
            HMAC_init   <= 1'h1;
            HMAC_key    <= HMAC_tag;
            HMAC_block  <= {V_init, 1'h1, {627{1'b0}}, 12'h580};
          end
          else
          begin
            nonce_st    <= KEYGEN_K1_ST;
            HMAC_init   <= 1'h0;
            HMAC_key    <= HMAC_key;
            HMAC_block  <= HMAC_block;
          end

          //HMAC registers
          HMAC_next   <= 1'h0;
    
          //DRBG registers
          ready_reg   <= 1'h0;
          nonce_reg   <= nonce_reg;
          valid_reg   <= 1'h0;
        end
        KEYGEN_V1_ST   : // V = HMAC_K(V) 
        begin            // V is generated when it comes here

          if (HMAC_tag_valid && !HMAC_init && !HMAC_next )
          begin
            nonce_st    <= KEYGEN_K2_ST;
            HMAC_init   <= 1'h1;
            HMAC_block  <= {HMAC_tag, 8'h01, seed, 1'h1, {HMAC_DRBG_GARBAGE_LENGTH{1'b0}},12'h708};
          end
          else
          begin
            nonce_st    <= KEYGEN_V1_ST;
            HMAC_init   <= 1'h0;
            HMAC_block  <= HMAC_block;
          end

          //HMAC registers
          HMAC_next   <= 1'h0;
          HMAC_key    <= HMAC_key;          
    
          //DRBG registers
          ready_reg   <= 1'h0;
          valid_reg   <= 1'h0;
          nonce_reg   <= nonce_reg;
        end
        KEYGEN_K2_ST   : // K = HMAC_K(V || 0x01 || seed) 
        begin            // K is generated when it comes here

          if (HMAC_tag_valid && !HMAC_init && !HMAC_next )
          begin
            nonce_st    <= KEYGEN_V2_ST;
            HMAC_init   <= 1'h1;
            HMAC_key    <= HMAC_tag;
            HMAC_block  <= {HMAC_block[1023:640],  1'h1, {627{1'b0}}, 12'h580};
          end
          else
          begin
            nonce_st    <= KEYGEN_K2_ST;
            HMAC_init   <= 1'h0;
            HMAC_key    <= HMAC_key;
            HMAC_block  <= HMAC_block;
          end

          //HMAC registers
          HMAC_next   <= 1'h0;
    
          //DRBG registers
          ready_reg   <= 1'h0;
          nonce_reg   <= nonce_reg;
          valid_reg   <= 1'h0;
        end
        KEYGEN_V2_ST   : // V = HMAC_K(V) 
        begin
          if (HMAC_tag_valid && !HMAC_init && !HMAC_next )
          begin
            nonce_st    <= NONCE_IDLE_ST;
            ready_reg   <= 1'h1;
            valid_reg   <= 1'h1;
            nonce_reg   <= HMAC_tag;
          end
          else
          begin
            nonce_st    <= KEYGEN_V2_ST;
            ready_reg   <= 1'h0;
            valid_reg   <= 1'h0;
            nonce_reg   <= nonce_reg;
          end

          //HMAC registers
          HMAC_init   <= 1'h0;
          HMAC_next   <= 1'h0;
          HMAC_block  <= HMAC_block;
          HMAC_key    <= HMAC_key;
          
        end
        SIGN_K1_1_ST   :  // K = HMAC_K(V || 0x00 || privKey || h1)
        begin
          if (HMAC_tag_valid && !HMAC_init && !HMAC_next )
          begin
            nonce_st    <= SIGN_K1_2_ST;
            HMAC_next   <= 1'h1;
            HMAC_block  <= {h1_135_0_bits, 1'h1, {875{1'b0}}, 12'h888};
          end
          else
          begin
            nonce_st    <= SIGN_K1_1_ST;
            HMAC_next   <= 1'h0;
            HMAC_block  <= HMAC_block;
          end

          //HMAC registers
          HMAC_init   <= 1'h0;
          HMAC_key    <= K_init;
    
          //DRBG registers
          ready_reg   <= 1'h0;
          valid_reg   <= 1'h0;
          nonce_reg   <= nonce_reg;
          h1_135_0_bits   <= h1_135_0_bits;
          h1_383_136_bits <= h1_383_136_bits;
        end
        SIGN_K1_2_ST     : // K = HMAC_K(V || 0x00 || privKey || h1)
        begin            // K is generated when it comes here
          if (HMAC_tag_valid && !HMAC_init && !HMAC_next )
          begin
            nonce_st    <= SIGN_V1_1_ST;
            HMAC_init   <= 1'h1;
            HMAC_key    <= HMAC_tag;
            HMAC_block  <= {V_init, 1'h1, {627{1'b0}}, 12'h580};
          end
          else
          begin
            nonce_st    <= SIGN_K1_2_ST;
            HMAC_init   <= 1'h0;
            HMAC_key    <= HMAC_key;
            HMAC_block  <= HMAC_block;
          end

          //HMAC registers
          HMAC_next   <= 1'h0;
    
          //DRBG registers
          ready_reg   <= 1'h0;
          nonce_reg   <= nonce_reg;
          valid_reg   <= 1'h0;
          h1_135_0_bits   <= h1_135_0_bits;
          h1_383_136_bits <= h1_383_136_bits;
        end
        SIGN_V1_1_ST     : // V = HMAC_K(V) 
        begin            // V is generated when it comes here
          if (HMAC_tag_valid && !HMAC_init && !HMAC_next )
          begin
            nonce_st    <= SIGN_V1_2_ST;
            HMAC_init   <= 1'h1;
            HMAC_block  <= {HMAC_tag, 8'h01, privKey, h1[383:136]};
          end
          else
          begin
            nonce_st    <= SIGN_V1_1_ST;
            HMAC_init   <= 1'h0;
            HMAC_block  <= HMAC_block;
          end

          //HMAC registers
          HMAC_next   <= 1'h0;
          HMAC_key    <= HMAC_key;          
    
          //DRBG registers
          ready_reg   <= 1'h0;
          valid_reg   <= 1'h0;
          nonce_reg   <= nonce_reg;
          h1_135_0_bits   <= h1_135_0_bits;
          h1_383_136_bits <= h1_383_136_bits;
        end
        SIGN_V1_2_ST     : // K = HMAC_K(V || 0x01 || privKey || h1) 
        begin
          if (HMAC_tag_valid && !HMAC_init && !HMAC_next )
          begin
            nonce_st        <= SIGN_K2_ST;
            HMAC_next       <= 1'h1;
            HMAC_block      <= {h1_135_0_bits, 1'h1, {875{1'b0}}, 12'h888};
            h1_383_136_bits <= HMAC_block[1023:776]; // V[1023:888]
            h1_135_0_bits   <= HMAC_block[775:640];  // V[887:640]
          end
          else
          begin
            nonce_st        <= SIGN_V1_2_ST;
            HMAC_next       <= 1'h0;
            HMAC_block      <= HMAC_block;
            h1_135_0_bits   <= h1_135_0_bits;
            h1_383_136_bits <= h1_383_136_bits;
          end

          //HMAC registers
          HMAC_init   <= 1'h0;
          HMAC_key    <= HMAC_key;
    
          //DRBG registers
          ready_reg   <= 1'h0;
          valid_reg   <= 1'h0;
          nonce_reg   <= nonce_reg;
        end
        SIGN_K2_ST     : // K = HMAC_K(V || 0x01 || privKey || h1) 
        begin            // K is generated when it comes here
          if (HMAC_tag_valid && !HMAC_init && !HMAC_next )
          begin
            nonce_st    <= SIGN_V2_ST;
            HMAC_init   <= 1'h1;
            HMAC_key    <= HMAC_tag;
            HMAC_block  <= {{h1_383_136_bits,h1_135_0_bits}, 1'h1, {627{1'b0}}, 12'h580};
          end
          else
          begin
            nonce_st    <= SIGN_K2_ST;
            HMAC_init   <= 1'h0;
            HMAC_key    <= HMAC_key;
            HMAC_block  <= HMAC_block;
          end

          //HMAC registers
          HMAC_next   <= 1'h0;
    
          //DRBG registers
          ready_reg   <= 1'h0;
          nonce_reg   <= nonce_reg;
          valid_reg   <= 1'h0;
          h1_135_0_bits   <= h1_135_0_bits;
          h1_383_136_bits <= h1_383_136_bits;
        end
        SIGN_V2_ST     : // V = HMAC_K(V) 
        begin            // V is generated when it comes here
          if (HMAC_tag_valid && !HMAC_init && !HMAC_next )
          begin
            nonce_st    <= SIGN_T1_ST;            
            HMAC_block  <= {HMAC_tag, 1'h1, {627{1'b0}}, 12'h580};
            nonce_reg   <= HMAC_tag;
            HMAC_init   <= 1'h1;
          end
          else
          begin
            nonce_st    <= SIGN_V2_ST;
            HMAC_block  <= HMAC_block;
            nonce_reg   <= nonce_reg;
            HMAC_init   <= 1'h0;
          end

          //HMAC registers
          HMAC_next   <= 1'h0;
          HMAC_key    <= HMAC_key;
          
    
          //DRBG registers
          ready_reg   <= 1'h0;          
          valid_reg   <= 1'h0;
          h1_135_0_bits   <= h1_135_0_bits;
          h1_383_136_bits <= h1_383_136_bits;
        end
        SIGN_T1_ST     : // Set T = [] 
        begin
          if (HMAC_tag_valid && !HMAC_init && !HMAC_next )
          begin
            nonce_st    <= SIGN_T2_ST;            
            HMAC_block  <= {HMAC_tag, 1'h1, {627{1'b0}}, 12'h580};
            nonce_reg   <= HMAC_tag;
          end
          else
          begin
            nonce_st    <= SIGN_T1_ST;
            HMAC_block  <= HMAC_block;
            nonce_reg   <= nonce_reg;
          end

          //HMAC registers
          HMAC_next   <= 1'h0;
          HMAC_key    <= HMAC_key;
          HMAC_init   <= 1'h0;
    
          //DRBG registers
          ready_reg   <= 1'h0;          
          valid_reg   <= 1'h0;
          h1_135_0_bits   <= h1_135_0_bits;
          h1_383_136_bits <= h1_383_136_bits;
        end
        SIGN_T2_ST     : // T = T || HMAC_K(V) 
        begin            // K is generated when it comes here
          if (nonce_reg==0 || nonce_reg > HMAC_DRBG_PRIME)
          begin
            nonce_st    <= SIGN_CHCK_ST;
            HMAC_init   <= 1'h1;            
            HMAC_block  <= {nonce_reg, 8'h00, 1'h1, {619{1'b0}}, 12'h578};
            ready_reg   <= 1'h0;
            valid_reg   <= 1'h0;            
          end
          else
          begin
            nonce_st    <= NONCE_IDLE_ST;
            HMAC_init   <= 1'h0;  
            HMAC_block  <= HMAC_block;
            ready_reg   <= 1'h1;
            valid_reg   <= 1'h1;
          end

          //HMAC registers
          HMAC_next   <= 1'h0;
          HMAC_key    <= HMAC_key;
    
          //DRBG registers  
          nonce_reg   <= nonce_reg;     
          h1_135_0_bits   <= h1_135_0_bits;
          h1_383_136_bits <= h1_383_136_bits;
        end
        SIGN_CHCK_ST   : // Return T if T is within the [1,q-1] range, otherwise:
        begin            // V is generated when it comes here
          if (HMAC_tag_valid && !HMAC_init && !HMAC_next )
          begin
            nonce_st    <= SIGN_K3_ST;
            HMAC_init   <= 1'h1;
            HMAC_key    <= HMAC_tag;
            HMAC_block  <= {nonce_reg, 1'h1, {627{1'b0}}, 12'h580};
          end
          else
          begin
            nonce_st    <= SIGN_CHCK_ST;
            HMAC_init   <= 1'h0;
            HMAC_key    <= HMAC_key;
            HMAC_block  <= HMAC_block;
          end

          //HMAC registers
          HMAC_next   <= 1'h0;
    
          //DRBG registers
          ready_reg   <= 1'h0;
          nonce_reg   <= nonce_reg;
          valid_reg   <= 1'h0;
          h1_135_0_bits   <= h1_135_0_bits;
          h1_383_136_bits <= h1_383_136_bits;
        end
        SIGN_K3_ST   : // Return T if T is within the [1,q-1] range, otherwise:
        begin            // V is generated when it comes here
          if (HMAC_tag_valid && !HMAC_init && !HMAC_next )
          begin
            nonce_st    <= SIGN_V2_ST;            
            HMAC_block  <= {HMAC_tag, 1'h1, {627{1'b0}}, 12'h580};
            nonce_reg   <= HMAC_tag;
            HMAC_init   <= 1'h1;
          end
          else
          begin
            nonce_st    <= SIGN_K3_ST;
            HMAC_block  <= HMAC_block;
            nonce_reg   <= nonce_reg;
            HMAC_init   <= 1'h0;
          end

          //HMAC registers
          HMAC_next   <= 1'h0;
          HMAC_key    <= HMAC_key;
    
          //DRBG registers
          ready_reg   <= 1'h0;          
          valid_reg   <= 1'h0;
          h1_135_0_bits   <= h1_135_0_bits;
          h1_383_136_bits <= h1_383_136_bits;
        end
        default        : // ERROR
        begin
          nonce_st    <= NONCE_IDLE_ST;

          //HMAC registers
          HMAC_init   <= 1'h0;
          HMAC_next   <= 1'h0;
          HMAC_block  <= 1023'h0;
          HMAC_key    <= 384'h0;
    
          //DRBG registers
          ready_reg   <= 1'h0;
          valid_reg   <= 1'h0;
          nonce_reg   <= nonce_reg;
          h1_135_0_bits   <= 384'h0;
          h1_383_136_bits <= 384'h0;
        end
      endcase  // case (nonce_st)
    end

  end //nonce_fsm
  
endmodule // hmac_drbg

//======================================================================
// EOF hmac_drbg.v
//======================================================================