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
    input wire                        clk,
    input wire                        reset_n,
    input wire                        KEYGEN_SIGN,
    input wire                        init,
    output wire                       ready,
    input wire   [SEED_LENGTH-1 : 0]  seed,
    input wire   [383 : 0]            privKey,
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
  reg         ready_new;
  reg         ready_we;

  reg [383:0] nonce_reg;

  //----------------------------------------------------------------
  // FSM_flow
  //
  // This FSM starts with the init command and then generates a nonce.
  // Active low and async reset.
  //----------------------------------------------------------------
  reg [3:0]  nonce_st;
  localparam NONCE_IDLE_ST    = 0,
             KEYGEN_K1_ST     = 1,
             KEYGEN_V1_ST     = 2,
             KEYGEN_K2_ST     = 3,
             KEYGEN_V2_ST     = 4,
             KEYGEN_FINAL_ST  = 5,
             SIGN_K1_ST       = 6,
             SIGN_V1_ST       = 7,
             SIGN_K2_ST       = 8,
             SIGN_V2_ST       = 9,
             SIGN_T1_ST       = 10,
             SIGN_T2_ST       = 11,
             SIGN_CHCK_ST     = 12,
             SIGN_K3_ST       = 13,
             SIGN_V3_ST       = 14;


  always @ (posedge clk or negedge reset_n)
  begin

  end
  
endmodule // hmac_drbg

//======================================================================
// EOF hmac_drbg.v
//======================================================================