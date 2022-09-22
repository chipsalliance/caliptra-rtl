///////////////////////////////////////////////////////////////////////////////////////
// Company             : UEC
// Engineer            : 
// 
// Create Date         : July/29/2014 
// Module Name         : aes128_table_ecb
// Project Name        : sakura_g_aes128
// Target Devices      : xc6slx75-2csg484
// Tool versions       : 13.4
// Description         : 
//
// Dependencies        : 
//
// Version             : 1.0
// Last Uodate         : July/29/2014
// Additional Comments : 
///////////////////////////////////////////////////////////////////////////////////////
// Copyright (c) Satoh LaboratoryÅCUEC

`timescale 1 ns/10 ps


module aes128_table_ecb (
  input               resetn,       // Async reset.
  input               clock,        // clock.

  input               enc_dec,      // Encrypt/Decrypt select. 0:Encrypt  1:Decrypt
  input               key_exp,      // Round Key Expansion
  input               start,        // Encrypt or Decrypt Start
  output reg          key_val,      // Round Key valid
  output reg          text_val,     // Cipher Text or Inverse Cipher Text valid
  input      [127:0]  key_in,       // Key input
  input      [127:0]  text_in,      // Cipher Text or Inverse Cipher Text input
  output     [127:0]  text_out,     // Cipher Text or Inverse Cipher Text output
  output reg          busy          // AES unit Busy
);

// State Machine stage name
`define  IDLE        3'h0           // Idle stage.
`define  KEY_EXP     3'h1           // Key expansion stage.
`define  ROUND_LOOP  3'h2           // Cipher/InvCipher stage.

// ==================================================================
// Internal signals
// ==================================================================
  reg       [2:0]  now_state;       // State Machine register
  reg       [2:0]  next_state;      // Next State Machine value
  reg              start_flag;      // Cipher or Inverse Cipher start pending flag
  reg       [3:0]  round_n;         // Number of Round counter

// Cipher Key Expansion
  reg      [31:0]  w[0:3];          // Cipher Key work register
  wire     [31:0]  rotword;
  wire      [7:0]  rcon;            // The round constant word arrey
  wire     [31:0]  temp;            // Key Expansion temporary value
  wire    [127:0]  next_key;        // Cipher Next round Key value
  reg     [127:0]  round10_key;     // Cipher round'10'key latch register

// Inverse Cipher Key Expansion
  reg      [31:0]  iw[0:3];         // Inverse Cipher Key work register
  wire      [7:0]  ircon;
  wire     [31:0]  itemp;
  wire     [31:0]  sword;
  wire     [31:0]  irotword;
  wire    [127:0]  next_ikey;       // Inverse Cipher Next round Key value

// Cipher (Encrypt)
  reg      [31:0]  state[0:3];      // Cipher working registers
  wire      [7:0]  s_box[0:3][0:3];
  wire      [7:0]  s_row[0:3][0:3];
  wire      [7:0]  m_col[0:3][0:3];
  wire    [127:0]  add_roundkey0;
  wire    [127:0]  add_roundkey;
  wire    [127:0]  cipher_text;

// Inverse Cipher (Decrypt)
  reg      [31:0]  istate[0:3];     // Inverse Cipher working registers
  wire      [7:0]  is_row_in[0:3][0:3];
  wire      [7:0]  is_row[0:3][0:3];
  wire      [7:0]  is_box[0:3][0:3];
  wire     [31:0]  im_col[0:3];
  wire    [127:0]  add_iroundkey0;
  wire    [127:0]  add_iroundkey;
  wire    [127:0]  plainte_text;

// ================================================================================
// Equasions
// ================================================================================
// --------------------------------------------------------------------------------
// Main State Machine
// --------------------------------------------------------------------------------
  always @( now_state or enc_dec or key_exp or start or start_flag or round_n or key_val ) begin
    case ( now_state )
      `IDLE       : if ( key_exp == 1'b1 ) next_state = `KEY_EXP;       // Idle
                    else if ( start == 1'b1 )
                      if ( key_val == 1'b0 ) next_state = `KEY_EXP;
                      else next_state = `ROUND_LOOP;
                    else if ( start_flag == 1'b1 ) next_state = `ROUND_LOOP;
                    else next_state = `IDLE;
      `KEY_EXP    : if ( round_n == 4'd10 ) next_state = `IDLE;         // Key Expansion state
                    else next_state = `KEY_EXP;
      `ROUND_LOOP : if ( round_n == 4'd10 ) next_state = `IDLE;         // Cipher/Invese Cipher state
                    else next_state = `ROUND_LOOP;
       default    : next_state = `IDLE;
    endcase
  end

  always @(posedge clock or negedge resetn) begin
    if ( resetn == 1'b0 ) now_state <= `IDLE;
    else now_state <= next_state;
  end


// ------------------------------------------------------------------------------
// Conrol signals
// ------------------------------------------------------------------------------
  always @(posedge clock or negedge resetn) begin
    if ( resetn == 1'b0 ) begin
      busy <= 1'b0;
      start_flag <= 1'b0;
      key_val <= 1'b0;
      round_n <= 4'h0;
      key_val <= 1'b0;
      text_val <= 1'b0;
    end
    else begin
      // Busy flag
      if (( key_exp == 1'b1 ) || ( start == 1'b1 )) busy <= 1'b1;
      else if (( now_state == `KEY_EXP ) && ( round_n == 4'd10 ) && ( start_flag != 1'b1 )) busy <= 1'b0;
      else if (( now_state == `ROUND_LOOP ) && ( round_n == 4'd10 )) busy <= 1'b0;
      else busy <= busy;

      // Start flag
      if ( start == 1'b1 ) start_flag <= 1'b1;
      else if ( now_state == `ROUND_LOOP ) start_flag <= 1'b0;
      else start_flag <= start_flag;

      // Nr counter
      if ( next_state == `IDLE ) round_n <= 4'h0;
      else round_n <= round_n + 1'b1;

      // Key valid flag
      if ( key_exp == 1'b1 ) key_val <= 1'b0;
      else if (( now_state == `KEY_EXP ) && ( round_n == 4'd10 )) key_val <= 1'b1;
      else key_val <= key_val;

      // Data valid flag
      if (( now_state == `ROUND_LOOP ) && ( round_n == 4'd10 )) text_val <= 1'b1;
      else text_val <= 1'b0;
    end
  end

  // Cipher/Plainte Text output
  assign text_out = ( enc_dec == 1'b0 )? { state[0], state[1], state[2], state[3] } : { istate[0], istate[1], istate[2], istate[3] };


// ----------------------------------------------------------------
// 128-bit Cipher Key Expansion
// ----------------------------------------------------------------
  always @(posedge clock or negedge resetn) begin
    if ( resetn == 1'b0 ) begin
      { w[0], w[1], w[2], w[3] } <= {128{1'b0}};   // Cipher Round Key register
      round10_key <= {128{1'b0}};
    end
    else begin
      // Cipher Round Key
      if ( next_state == `IDLE ) { w[0], w[1], w[2], w[3] } <= key_in;
      else if (( next_state == `KEY_EXP ) || ( next_state == `ROUND_LOOP )) { w[0], w[1], w[2], w[3] } <= next_key;
      else { w[0], w[1], w[2], w[3] } <= { w[0], w[1], w[2], w[3] };

      // Round10 Key Latch
      if (( now_state == `KEY_EXP ) && ( round_n == 4'd10 )) round10_key <= { w[0], w[1], w[2], w[3] };
      else round10_key <= round10_key;
    end
  end

  // RotWord
  assign rotword = {w[3][23:0], w[3][31:24]};
  // SubWord
  subword SubWord ( .a( rotword ), .b( temp ));

  // Next Round Key
  assign next_key[127:96] = w[0] ^ {( temp[31:24] ^ rcon ), temp[23:0] };
  assign next_key[ 95:64] = w[1] ^ next_key[127:96];
  assign next_key[ 63:32] = w[2] ^ next_key[ 95:64];
  assign next_key[ 31: 0] = w[3] ^ next_key[ 63:32];

  // Rcon[] The round constant word arrey
  assign rcon = ( round_n == 4'h0 )? 8'h01 : 8'h00
              | ( round_n == 4'h1 )? 8'h02 : 8'h00
              | ( round_n == 4'h2 )? 8'h04 : 8'h00
              | ( round_n == 4'h3 )? 8'h08 : 8'h00
              | ( round_n == 4'h4 )? 8'h10 : 8'h00
              | ( round_n == 4'h5 )? 8'h20 : 8'h00
              | ( round_n == 4'h6 )? 8'h40 : 8'h00
              | ( round_n == 4'h7 )? 8'h80 : 8'h00
              | ( round_n == 4'h8 )? 8'h1b : 8'h00
              | ( round_n == 4'h9 )? 8'h36 : 8'h00;


// ----------------------------------------------------------------
// 128-bit Invese Cipher Key Expansion
// ----------------------------------------------------------------
  // Invese Round Key WORK register
  always @(posedge clock or negedge resetn) begin
    if ( resetn == 1'b0 ) begin
      { iw[0], iw[1], iw[2], iw[3] } <= {128{1'b0}};
    end
    else begin
      if (( now_state == `KEY_EXP ) && ( round_n == 4'd10 )) { iw[0], iw[1], iw[2], iw[3] } <= { w[0], w[1], w[2], w[3] };
      else if ( next_state == `IDLE ) { iw[0], iw[1], iw[2], iw[3] } <= round10_key;
      else if (( start == 1'b1 ) || ( start_flag == 1'b1 ) || ( now_state == `ROUND_LOOP )) { iw[0], iw[1], iw[2], iw[3] } <= next_ikey;
      else { iw[0], iw[1], iw[2], iw[3] } <= { iw[0], iw[1], iw[2], iw[3] };
    end
  end

  assign itemp = iw[3] ^ iw[2];

  // InvSubWord
  subword iSubWord ( .a( itemp ), .b( sword ));

  // InvRotWord
  assign irotword = {sword[23:0], sword[31:24]};

  // Next Invese Round Key
  assign next_ikey[127:96] = {( iw[0][31:24] ^ irotword[31:24] ^ ircon ), ( iw[0][23:0] ^ irotword[23:0] )};
  assign next_ikey[ 95:64] = iw[1] ^ iw[0];
  assign next_ikey[ 63:32] = iw[2] ^ iw[1];
  assign next_ikey[ 31: 0] = iw[3] ^ iw[2];

  assign ircon = ( round_n == 4'h9 )? 8'h01 : 8'h00
               | ( round_n == 4'h8 )? 8'h02 : 8'h00
               | ( round_n == 4'h7 )? 8'h04 : 8'h00
               | ( round_n == 4'h6 )? 8'h08 : 8'h00
               | ( round_n == 4'h5 )? 8'h10 : 8'h00
               | ( round_n == 4'h4 )? 8'h20 : 8'h00
               | ( round_n == 4'h3 )? 8'h40 : 8'h00
               | ( round_n == 4'h2 )? 8'h80 : 8'h00
               | ( round_n == 4'h1 )? 8'h1b : 8'h00
               | ( round_n == 4'h0 )? 8'h36 : 8'h00;


// ------------------------------------------------------------------------------------------
// ECB-AES128.Encrypt
// Cipher
// ------------------------------------------------------------------------------------------
  // Cipher state registers
  always @(posedge clock or negedge resetn) begin
    if ( resetn == 1'b0 ) begin
      { state[0], state[1], state[2], state[3]} <= {128{1'b0}};
    end
    else begin
      if ( enc_dec == 1'b0 ) begin
        if ((( start == 1'b1 ) || ( start_flag == 1'b1 )) && ( round_n == 4'h0 )) begin                                                        // Nr = 0  Add Round Key
          { state[0], state[1], state[2], state[3]} <= add_roundkey0;
        end
        else if (( now_state == `ROUND_LOOP ) && ( round_n >= 4'd1 ) && ( round_n <= 4'h9 )) begin   // Nr = 1 to Nr = 9  Add round key
          { state[0], state[1], state[2], state[3]} <= add_roundkey;
        end
        else if (( now_state == `ROUND_LOOP ) && ( round_n == 4'd10 )) begin   // Nr = 10
          { state[0], state[1], state[2], state[3]} <= cipher_text;
        end
        else { state[0], state[1], state[2], state[3]} <= { state[0], state[1], state[2], state[3]};
      end
      else { state[0], state[1], state[2], state[3]} <= { state[0], state[1], state[2], state[3]};
    end
  end

  // ------------------------------------------------------------------------------------------------------------
  // Data Input and Add Round Key(Nr = 0)
  // ------------------------------------------------------------------------------------------------------------
  assign add_roundkey0 = text_in ^ { w[0], w[1], w[2], w[3] };

  // ------------------------------------------------------------------------------------------------------------
  // SubBytes Transformation
  // ------------------------------------------------------------------------------------------------------------
  subbytes SubBytes (
    .a00( state[0][31:24] ), .a10( state[0][23:16] ), .a20( state[0][15:8] ), .a30( state[0][7:0] ),
    .a01( state[1][31:24] ), .a11( state[1][23:16] ), .a21( state[1][15:8] ), .a31( state[1][7:0] ),
    .a02( state[2][31:24] ), .a12( state[2][23:16] ), .a22( state[2][15:8] ), .a32( state[2][7:0] ),
    .a03( state[3][31:24] ), .a13( state[3][23:16] ), .a23( state[3][15:8] ), .a33( state[3][7:0] ),

    .b00( s_box[0][0] ), .b10( s_box[1][0] ), .b20( s_box[2][0] ), .b30( s_box[3][0] ),
    .b01( s_box[0][1] ), .b11( s_box[1][1] ), .b21( s_box[2][1] ), .b31( s_box[3][1] ),
    .b02( s_box[0][2] ), .b12( s_box[1][2] ), .b22( s_box[2][2] ), .b32( s_box[3][2] ),
    .b03( s_box[0][3] ), .b13( s_box[1][3] ), .b23( s_box[2][3] ), .b33( s_box[3][3] )
  );

  // ------------------------------------------------------------------------------------------------------------
  // ShiftRows
  // ------------------------------------------------------------------------------------------------------------
  assign { s_row[0][0], s_row[0][1], s_row[0][2], s_row[0][3] } = { s_box[0][0], s_box[0][1], s_box[0][2], s_box[0][3] };
  assign { s_row[1][0], s_row[1][1], s_row[1][2], s_row[1][3] } = { s_box[1][1], s_box[1][2], s_box[1][3], s_box[1][0] };
  assign { s_row[2][0], s_row[2][1], s_row[2][2], s_row[2][3] } = { s_box[2][2], s_box[2][3], s_box[2][0], s_box[2][1] };
  assign { s_row[3][0], s_row[3][1], s_row[3][2], s_row[3][3] } = { s_box[3][3], s_box[3][0], s_box[3][1], s_box[3][2] };

  // ------------------------------------------------------------------------------------------------------------
  // MixColumns
  // ------------------------------------------------------------------------------------------------------------
  mixcolumns MixColumns0 (
    .s0c( s_row[0][0] ), .s1c( s_row[1][0] ), .s2c( s_row[2][0] ), .s3c( s_row[3][0] ),
    .m0c( m_col[0][0] ), .m1c( m_col[1][0] ), .m2c( m_col[2][0] ), .m3c( m_col[3][0] )
  );
  mixcolumns MixColumns1 (
    .s0c( s_row[0][1] ), .s1c( s_row[1][1] ), .s2c( s_row[2][1] ), .s3c( s_row[3][1] ),
    .m0c( m_col[0][1] ), .m1c( m_col[1][1] ), .m2c( m_col[2][1] ), .m3c( m_col[3][1] )
  );
  mixcolumns MixColumns2 (
    .s0c( s_row[0][2] ), .s1c( s_row[1][2] ), .s2c( s_row[2][2] ), .s3c( s_row[3][2] ),
    .m0c( m_col[0][2] ), .m1c( m_col[1][2] ), .m2c( m_col[2][2] ), .m3c( m_col[3][2] )
  );
  mixcolumns MixColumns3 (
    .s0c( s_row[0][3] ), .s1c( s_row[1][3] ), .s2c( s_row[2][3] ), .s3c( s_row[3][3] ),
    .m0c( m_col[0][3] ), .m1c( m_col[1][3] ), .m2c( m_col[2][3] ), .m3c( m_col[3][3] )
  );

  // ------------------------------------------------------------------------------------------------------------
  // Add Round Key
  // ------------------------------------------------------------------------------------------------------------
  // Nr = 1 to Nr = 9
  assign add_roundkey[127:96] = { m_col[0][0], m_col[1][0], m_col[2][0], m_col[3][0] } ^ w[0];
  assign add_roundkey[ 95:64] = { m_col[0][1], m_col[1][1], m_col[2][1], m_col[3][1] } ^ w[1];
  assign add_roundkey[ 63:32] = { m_col[0][2], m_col[1][2], m_col[2][2], m_col[3][2] } ^ w[2];
  assign add_roundkey[ 31: 0] = { m_col[0][3], m_col[1][3], m_col[2][3], m_col[3][3] } ^ w[3];

  // Nr = 10 
  // Cipher Text Output
  assign cipher_text[127:96] = { s_row[0][0], s_row[1][0], s_row[2][0], s_row[3][0] } ^ w[0];
  assign cipher_text[ 95:64] = { s_row[0][1], s_row[1][1], s_row[2][1], s_row[3][1] } ^ w[1];
  assign cipher_text[ 63:32] = { s_row[0][2], s_row[1][2], s_row[2][2], s_row[3][2] } ^ w[2];
  assign cipher_text[ 31: 0] = { s_row[0][3], s_row[1][3], s_row[2][3], s_row[3][3] } ^ w[3];



// ------------------------------------------------------------------------------------------------------------
// ECB-AES128.Decrypt
// Invese Cipher
// ------------------------------------------------------------------------------------------------------------
  // Invese Cipher state registers
  always @(posedge clock or negedge resetn) begin
    if ( resetn == 1'b0 ) begin
      { istate[0], istate[1], istate[2], istate[3]} <= {128{1'b0}};
    end
    else begin
      if ( enc_dec == 1'b1 ) begin
        if ((( start == 1'b1 ) || ( start_flag == 1'b1 )) && ( round_n == 4'h0 )) begin      // Nr = 0                                                  // Nr = 0  Add Round Key
          { istate[0], istate[1], istate[2], istate[3]} <= add_iroundkey0;
        end
        else if (( now_state == `ROUND_LOOP ) && ( round_n >= 4'd1 ) && ( round_n <= 4'd9 )) begin   // Nr = 1 to Nr = 9
          { istate[0], istate[1], istate[2], istate[3]} <= { im_col[0], im_col[1], im_col[2], im_col[3] };
        end
        else if (( now_state == `ROUND_LOOP ) && ( round_n == 4'd10 )) begin                         // Nr = 10
          { istate[0], istate[1], istate[2], istate[3]} <= add_iroundkey;
        end
        else { istate[0], istate[1], istate[2], istate[3]} <= { istate[0], istate[1], istate[2], istate[3]};
      end
      else { istate[0], istate[1], istate[2], istate[3]} <= { istate[0], istate[1], istate[2], istate[3]};
    end
  end

  // ------------------------------------------------------------------------------------------------------------
  // Data Input and Add InvRound Key(Nr = 0)
  // ------------------------------------------------------------------------------------------------------------
  assign add_iroundkey0 = text_in ^ { iw[0], iw[1], iw[2], iw[3] };

  // ------------------------------------------------------------------------------------------------------------
  // InvShiftRows
  // ------------------------------------------------------------------------------------------------------------
  // Input data select.
  assign { is_row_in[0][0], is_row_in[1][0], is_row_in[2][0], is_row_in[3][0] } = istate[0];
  assign { is_row_in[0][1], is_row_in[1][1], is_row_in[2][1], is_row_in[3][1] } = istate[1];
  assign { is_row_in[0][2], is_row_in[1][2], is_row_in[2][2], is_row_in[3][2] } = istate[2];
  assign { is_row_in[0][3], is_row_in[1][3], is_row_in[2][3], is_row_in[3][3] } = istate[3];

  assign { is_row[0][0], is_row[0][1], is_row[0][2], is_row[0][3] } = { is_row_in[0][0], is_row_in[0][1], is_row_in[0][2], is_row_in[0][3] };
  assign { is_row[1][1], is_row[1][2], is_row[1][3], is_row[1][0] } = { is_row_in[1][0], is_row_in[1][1], is_row_in[1][2], is_row_in[1][3] };
  assign { is_row[2][2], is_row[2][3], is_row[2][0], is_row[2][1] } = { is_row_in[2][0], is_row_in[2][1], is_row_in[2][2], is_row_in[2][3] };
  assign { is_row[3][3], is_row[3][0], is_row[3][1], is_row[3][2] } = { is_row_in[3][0], is_row_in[3][1], is_row_in[3][2], is_row_in[3][3] };


  // ------------------------------------------------------------------------------------------------------------
  // InvSubBytes
  // ------------------------------------------------------------------------------------------------------------
  invsubbytes InvSubBytes (
    .a00( is_row[0][0] ), .a10( is_row[1][0] ), .a20( is_row[2][0] ), .a30( is_row[3][0] ),
    .a01( is_row[0][1] ), .a11( is_row[1][1] ), .a21( is_row[2][1] ), .a31( is_row[3][1] ),
    .a02( is_row[0][2] ), .a12( is_row[1][2] ), .a22( is_row[2][2] ), .a32( is_row[3][2] ),
    .a03( is_row[0][3] ), .a13( is_row[1][3] ), .a23( is_row[2][3] ), .a33( is_row[3][3] ),

    .b00( is_box[0][0] ), .b10( is_box[1][0] ), .b20( is_box[2][0] ), .b30( is_box[3][0] ),
    .b01( is_box[0][1] ), .b11( is_box[1][1] ), .b21( is_box[2][1] ), .b31( is_box[3][1] ),
    .b02( is_box[0][2] ), .b12( is_box[1][2] ), .b22( is_box[2][2] ), .b32( is_box[3][2] ),
    .b03( is_box[0][3] ), .b13( is_box[1][3] ), .b23( is_box[2][3] ), .b33( is_box[3][3] )
  );

  // ------------------------------------------------------------------------------------------------------------
  // Add InvRound Key
  // ------------------------------------------------------------------------------------------------------------
  // Nr = 1 to Nr = 10
  assign add_iroundkey[127:96] = { is_box[0][0], is_box[1][0], is_box[2][0], is_box[3][0] } ^ iw[0];
  assign add_iroundkey[ 95:64] = { is_box[0][1], is_box[1][1], is_box[2][1], is_box[3][1] } ^ iw[1];
  assign add_iroundkey[ 63:32] = { is_box[0][2], is_box[1][2], is_box[2][2], is_box[3][2] } ^ iw[2];
  assign add_iroundkey[ 31: 0] = { is_box[0][3], is_box[1][3], is_box[2][3], is_box[3][3] } ^ iw[3];

  // ------------------------------------------------------------------------------------------------------------
  // InvMixColumns
  // ------------------------------------------------------------------------------------------------------------
  inv_mixcolumn InvMixColumn0 (
    .s0c( add_iroundkey[127:120] ), .s1c( add_iroundkey[119:112] ), .s2c( add_iroundkey[111:104] ), .s3c( add_iroundkey[103:96] ),
    .m0c( im_col[0][31:24] ),       .m1c( im_col[0][23:16] ),       .m2c( im_col[0][15:8] ),        .m3c( im_col[0][7:0] )
  );
  inv_mixcolumn InvMixColumn1 (
    .s0c( add_iroundkey[95:88] ), .s1c( add_iroundkey[87:80] ), .s2c( add_iroundkey[79:72] ), .s3c( add_iroundkey[71:64] ),
    .m0c( im_col[1][31:24] ),     .m1c( im_col[1][23:16] ),     .m2c( im_col[1][15:8] ),      .m3c( im_col[1][7:0] )
  );
  inv_mixcolumn InvMixColumn2(
    .s0c( add_iroundkey[63:56] ), .s1c( add_iroundkey[55:48] ), .s2c( add_iroundkey[47:40] ), .s3c( add_iroundkey[39:32] ),
    .m0c( im_col[2][31:24] ),     .m1c( im_col[2][23:16] ),     .m2c( im_col[2][15:8] ),      .m3c( im_col[2][7:0] )
  );
  inv_mixcolumn InvMixColumn3 (
    .s0c( add_iroundkey[31:24] ), .s1c( add_iroundkey[23:16] ), .s2c( add_iroundkey[15:8] ), .s3c( add_iroundkey[7:0] ),
    .m0c( im_col[3][31:24] ),     .m1c( im_col[3][23:16] ),     .m2c( im_col[3][15:8] ),     .m3c( im_col[3][7:0] )
  );

endmodule



/////////////////////////////////////////////////////////////////////////////////////////////////////////
// Module Name         : subbytes
/////////////////////////////////////////////////////////////////////////////////////////////////////////
module subbytes (
  input     [7:0]  a00, a10, a20, a30,    // Data input.
  input     [7:0]  a01, a11, a21, a31,    // Data input.
  input     [7:0]  a02, a12, a22, a32,    // Data input.
  input     [7:0]  a03, a13, a23, a33,    // Data input.

  output    [7:0]  b00, b10, b20, b30,    // data output.
  output    [7:0]  b01, b11, b21, b31,    // data output.
  output    [7:0]  b02, b12, b22, b32,    // data output.
  output    [7:0]  b03, b13, b23, b33     // data output.
);

// ========================================================
// Equasions
// ========================================================
  assign b00 = s_box( a00 );
  assign b10 = s_box( a10 );
  assign b20 = s_box( a20 );
  assign b30 = s_box( a30 );

  assign b01 = s_box( a01 );
  assign b11 = s_box( a11 );
  assign b21 = s_box( a21 );
  assign b31 = s_box( a31 );

  assign b02 = s_box( a02 );
  assign b12 = s_box( a12 );
  assign b22 = s_box( a22 );
  assign b32 = s_box( a32 );

  assign b03 = s_box( a03 );
  assign b13 = s_box( a13 );
  assign b23 = s_box( a23 );
  assign b33 = s_box( a33 );


  function [7:0] s_box;
  input    [7:0] aij;
  reg      [7:0] sb[0:255];
  begin
    { sb[  0],sb[  1],sb[  2],sb[  3],sb[  4],sb[  5],sb[  6],sb[  7],sb[  8],sb[  9],sb[ 10],sb[ 11],sb[ 12],sb[ 13],sb[ 14],sb[ 15],
      sb[ 16],sb[ 17],sb[ 18],sb[ 19],sb[ 20],sb[ 21],sb[ 22],sb[ 23],sb[ 24],sb[ 25],sb[ 26],sb[ 27],sb[ 28],sb[ 29],sb[ 30],sb[ 31],
      sb[ 32],sb[ 33],sb[ 34],sb[ 35],sb[ 36],sb[ 37],sb[ 38],sb[ 39],sb[ 40],sb[ 41],sb[ 42],sb[ 43],sb[ 44],sb[ 45],sb[ 46],sb[ 47],
      sb[ 48],sb[ 49],sb[ 50],sb[ 51],sb[ 52],sb[ 53],sb[ 54],sb[ 55],sb[ 56],sb[ 57],sb[ 58],sb[ 59],sb[ 60],sb[ 61],sb[ 62],sb[ 63],
      sb[ 64],sb[ 65],sb[ 66],sb[ 67],sb[ 68],sb[ 69],sb[ 70],sb[ 71],sb[ 72],sb[ 73],sb[ 74],sb[ 75],sb[ 76],sb[ 77],sb[ 78],sb[ 79],
      sb[ 80],sb[ 81],sb[ 82],sb[ 83],sb[ 84],sb[ 85],sb[ 86],sb[ 87],sb[ 88],sb[ 89],sb[ 90],sb[ 91],sb[ 92],sb[ 93],sb[ 94],sb[ 95],
      sb[ 96],sb[ 97],sb[ 98],sb[ 99],sb[100],sb[101],sb[102],sb[103],sb[104],sb[105],sb[106],sb[107],sb[108],sb[109],sb[110],sb[111],
      sb[112],sb[113],sb[114],sb[115],sb[116],sb[117],sb[118],sb[119],sb[120],sb[121],sb[122],sb[123],sb[124],sb[125],sb[126],sb[127],
      sb[128],sb[129],sb[130],sb[131],sb[132],sb[133],sb[134],sb[135],sb[136],sb[137],sb[138],sb[139],sb[140],sb[141],sb[142],sb[143],
      sb[144],sb[145],sb[146],sb[147],sb[148],sb[149],sb[150],sb[151],sb[152],sb[153],sb[154],sb[155],sb[156],sb[157],sb[158],sb[159],
      sb[160],sb[161],sb[162],sb[163],sb[164],sb[165],sb[166],sb[167],sb[168],sb[169],sb[170],sb[171],sb[172],sb[173],sb[174],sb[175],
      sb[176],sb[177],sb[178],sb[179],sb[180],sb[181],sb[182],sb[183],sb[184],sb[185],sb[186],sb[187],sb[188],sb[189],sb[190],sb[191],
      sb[192],sb[193],sb[194],sb[195],sb[196],sb[197],sb[198],sb[199],sb[200],sb[201],sb[202],sb[203],sb[204],sb[205],sb[206],sb[207],
      sb[208],sb[209],sb[210],sb[211],sb[212],sb[213],sb[214],sb[215],sb[216],sb[217],sb[218],sb[219],sb[220],sb[221],sb[222],sb[223],
      sb[224],sb[225],sb[226],sb[227],sb[228],sb[229],sb[230],sb[231],sb[232],sb[233],sb[234],sb[235],sb[236],sb[237],sb[238],sb[239],
      sb[240],sb[241],sb[242],sb[243],sb[244],sb[245],sb[246],sb[247],sb[248],sb[249],sb[250],sb[251],sb[252],sb[253],sb[254],sb[255]
    } =

    { 8'h63, 8'h7c, 8'h77, 8'h7b, 8'hf2, 8'h6b, 8'h6f, 8'hc5, 8'h30, 8'h01, 8'h67, 8'h2b, 8'hfe, 8'hd7, 8'hab, 8'h76,
      8'hca, 8'h82, 8'hc9, 8'h7d, 8'hfa, 8'h59, 8'h47, 8'hf0, 8'had, 8'hd4, 8'ha2, 8'haf, 8'h9c, 8'ha4, 8'h72, 8'hc0,
      8'hb7, 8'hfd, 8'h93, 8'h26, 8'h36, 8'h3f, 8'hf7, 8'hcc, 8'h34, 8'ha5, 8'he5, 8'hf1, 8'h71, 8'hd8, 8'h31, 8'h15,
      8'h04, 8'hc7, 8'h23, 8'hc3, 8'h18, 8'h96, 8'h05, 8'h9a, 8'h07, 8'h12, 8'h80, 8'he2, 8'heb, 8'h27, 8'hb2, 8'h75,
      8'h09, 8'h83, 8'h2c, 8'h1a, 8'h1b, 8'h6e, 8'h5a, 8'ha0, 8'h52, 8'h3b, 8'hd6, 8'hb3, 8'h29, 8'he3, 8'h2f, 8'h84,
      8'h53, 8'hd1, 8'h00, 8'hed, 8'h20, 8'hfc, 8'hb1, 8'h5b, 8'h6a, 8'hcb, 8'hbe, 8'h39, 8'h4a, 8'h4c, 8'h58, 8'hcf,
      8'hd0, 8'hef, 8'haa, 8'hfb, 8'h43, 8'h4d, 8'h33, 8'h85, 8'h45, 8'hf9, 8'h02, 8'h7f, 8'h50, 8'h3c, 8'h9f, 8'ha8,
      8'h51, 8'ha3, 8'h40, 8'h8f, 8'h92, 8'h9d, 8'h38, 8'hf5, 8'hbc, 8'hb6, 8'hda, 8'h21, 8'h10, 8'hff, 8'hf3, 8'hd2,
      8'hcd, 8'h0c, 8'h13, 8'hec, 8'h5f, 8'h97, 8'h44, 8'h17, 8'hc4, 8'ha7, 8'h7e, 8'h3d, 8'h64, 8'h5d, 8'h19, 8'h73,
      8'h60, 8'h81, 8'h4f, 8'hdc, 8'h22, 8'h2a, 8'h90, 8'h88, 8'h46, 8'hee, 8'hb8, 8'h14, 8'hde, 8'h5e, 8'h0b, 8'hdb,
      8'he0, 8'h32, 8'h3a, 8'h0a, 8'h49, 8'h06, 8'h24, 8'h5c, 8'hc2, 8'hd3, 8'hac, 8'h62, 8'h91, 8'h95, 8'he4, 8'h79,
      8'he7, 8'hc8, 8'h37, 8'h6d, 8'h8d, 8'hd5, 8'h4e, 8'ha9, 8'h6c, 8'h56, 8'hf4, 8'hea, 8'h65, 8'h7a, 8'hae, 8'h08,
      8'hba, 8'h78, 8'h25, 8'h2e, 8'h1c, 8'ha6, 8'hb4, 8'hc6, 8'he8, 8'hdd, 8'h74, 8'h1f, 8'h4b, 8'hbd, 8'h8b, 8'h8a,
      8'h70, 8'h3e, 8'hb5, 8'h66, 8'h48, 8'h03, 8'hf6, 8'h0e, 8'h61, 8'h35, 8'h57, 8'hb9, 8'h86, 8'hc1, 8'h1d, 8'h9e,
      8'he1, 8'hf8, 8'h98, 8'h11, 8'h69, 8'hd9, 8'h8e, 8'h94, 8'h9b, 8'h1e, 8'h87, 8'he9, 8'hce, 8'h55, 8'h28, 8'hdf,
      8'h8c, 8'ha1, 8'h89, 8'h0d, 8'hbf, 8'he6, 8'h42, 8'h68, 8'h41, 8'h99, 8'h2d, 8'h0f, 8'hb0, 8'h54, 8'hbb, 8'h16
    };

    s_box =sb[aij];
  end
  endfunction

endmodule


/////////////////////////////////////////////////////////////////////////////////////////////////////////
// Module Name         : invsubbytes
/////////////////////////////////////////////////////////////////////////////////////////////////////////
module invsubbytes (
  input     [7:0]  a00, a10, a20, a30,    // Data input.
  input     [7:0]  a01, a11, a21, a31,    // Data input.
  input     [7:0]  a02, a12, a22, a32,    // Data input.
  input     [7:0]  a03, a13, a23, a33,    // Data input.

  output    [7:0]  b00, b10, b20, b30,    // data output.
  output    [7:0]  b01, b11, b21, b31,    // data output.
  output    [7:0]  b02, b12, b22, b32,    // data output.
  output    [7:0]  b03, b13, b23, b33     // data output.
);

// ========================================================
// Equasions
// ========================================================
  assign b00 = is_box( a00 );
  assign b10 = is_box( a10 );
  assign b20 = is_box( a20 );
  assign b30 = is_box( a30 );

  assign b01 = is_box( a01 );
  assign b11 = is_box( a11 );
  assign b21 = is_box( a21 );
  assign b31 = is_box( a31 );

  assign b02 = is_box( a02 );
  assign b12 = is_box( a12 );
  assign b22 = is_box( a22 );
  assign b32 = is_box( a32 );

  assign b03 = is_box( a03 );
  assign b13 = is_box( a13 );
  assign b23 = is_box( a23 );
  assign b33 = is_box( a33 );
  


  function [7:0] is_box;
  input    [7:0] aij;
  reg      [7:0] sb[0:255];
  begin
    { sb[  0],sb[  1],sb[  2],sb[  3],sb[  4],sb[  5],sb[  6],sb[  7],sb[  8],sb[  9],sb[ 10],sb[ 11],sb[ 12],sb[ 13],sb[ 14],sb[ 15],
      sb[ 16],sb[ 17],sb[ 18],sb[ 19],sb[ 20],sb[ 21],sb[ 22],sb[ 23],sb[ 24],sb[ 25],sb[ 26],sb[ 27],sb[ 28],sb[ 29],sb[ 30],sb[ 31],
      sb[ 32],sb[ 33],sb[ 34],sb[ 35],sb[ 36],sb[ 37],sb[ 38],sb[ 39],sb[ 40],sb[ 41],sb[ 42],sb[ 43],sb[ 44],sb[ 45],sb[ 46],sb[ 47],
      sb[ 48],sb[ 49],sb[ 50],sb[ 51],sb[ 52],sb[ 53],sb[ 54],sb[ 55],sb[ 56],sb[ 57],sb[ 58],sb[ 59],sb[ 60],sb[ 61],sb[ 62],sb[ 63],
      sb[ 64],sb[ 65],sb[ 66],sb[ 67],sb[ 68],sb[ 69],sb[ 70],sb[ 71],sb[ 72],sb[ 73],sb[ 74],sb[ 75],sb[ 76],sb[ 77],sb[ 78],sb[ 79],
      sb[ 80],sb[ 81],sb[ 82],sb[ 83],sb[ 84],sb[ 85],sb[ 86],sb[ 87],sb[ 88],sb[ 89],sb[ 90],sb[ 91],sb[ 92],sb[ 93],sb[ 94],sb[ 95],
      sb[ 96],sb[ 97],sb[ 98],sb[ 99],sb[100],sb[101],sb[102],sb[103],sb[104],sb[105],sb[106],sb[107],sb[108],sb[109],sb[110],sb[111],
      sb[112],sb[113],sb[114],sb[115],sb[116],sb[117],sb[118],sb[119],sb[120],sb[121],sb[122],sb[123],sb[124],sb[125],sb[126],sb[127],
      sb[128],sb[129],sb[130],sb[131],sb[132],sb[133],sb[134],sb[135],sb[136],sb[137],sb[138],sb[139],sb[140],sb[141],sb[142],sb[143],
      sb[144],sb[145],sb[146],sb[147],sb[148],sb[149],sb[150],sb[151],sb[152],sb[153],sb[154],sb[155],sb[156],sb[157],sb[158],sb[159],
      sb[160],sb[161],sb[162],sb[163],sb[164],sb[165],sb[166],sb[167],sb[168],sb[169],sb[170],sb[171],sb[172],sb[173],sb[174],sb[175],
      sb[176],sb[177],sb[178],sb[179],sb[180],sb[181],sb[182],sb[183],sb[184],sb[185],sb[186],sb[187],sb[188],sb[189],sb[190],sb[191],
      sb[192],sb[193],sb[194],sb[195],sb[196],sb[197],sb[198],sb[199],sb[200],sb[201],sb[202],sb[203],sb[204],sb[205],sb[206],sb[207],
      sb[208],sb[209],sb[210],sb[211],sb[212],sb[213],sb[214],sb[215],sb[216],sb[217],sb[218],sb[219],sb[220],sb[221],sb[222],sb[223],
      sb[224],sb[225],sb[226],sb[227],sb[228],sb[229],sb[230],sb[231],sb[232],sb[233],sb[234],sb[235],sb[236],sb[237],sb[238],sb[239],
      sb[240],sb[241],sb[242],sb[243],sb[244],sb[245],sb[246],sb[247],sb[248],sb[249],sb[250],sb[251],sb[252],sb[253],sb[254],sb[255]
    } =

    { 
      8'h52, 8'h09, 8'h6a, 8'hd5, 8'h30, 8'h36, 8'ha5, 8'h38, 8'hbf, 8'h40, 8'ha3, 8'h9e, 8'h81, 8'hf3, 8'hd7, 8'hfb,
      8'h7c, 8'he3, 8'h39, 8'h82, 8'h9b, 8'h2f, 8'hff, 8'h87, 8'h34, 8'h8e, 8'h43, 8'h44, 8'hc4, 8'hde, 8'he9, 8'hcb,
      8'h54, 8'h7b, 8'h94, 8'h32, 8'ha6, 8'hc2, 8'h23, 8'h3d, 8'hee, 8'h4c, 8'h95, 8'h0b, 8'h42, 8'hfa, 8'hc3, 8'h4e,
      8'h08, 8'h2e, 8'ha1, 8'h66, 8'h28, 8'hd9, 8'h24, 8'hb2, 8'h76, 8'h5b, 8'ha2, 8'h49, 8'h6d, 8'h8b, 8'hd1, 8'h25,
      8'h72, 8'hf8, 8'hf6, 8'h64, 8'h86, 8'h68, 8'h98, 8'h16, 8'hd4, 8'ha4, 8'h5c, 8'hcc, 8'h5d, 8'h65, 8'hb6, 8'h92,
      8'h6c, 8'h70, 8'h48, 8'h50, 8'hfd, 8'hed, 8'hb9, 8'hda, 8'h5e, 8'h15, 8'h46, 8'h57, 8'ha7, 8'h8d, 8'h9d, 8'h84,
      8'h90, 8'hd8, 8'hab, 8'h00, 8'h8c, 8'hbc, 8'hd3, 8'h0a, 8'hf7, 8'he4, 8'h58, 8'h05, 8'hb8, 8'hb3, 8'h45, 8'h06,
      8'hd0, 8'h2c, 8'h1e, 8'h8f, 8'hca, 8'h3f, 8'h0f, 8'h02, 8'hc1, 8'haf, 8'hbd, 8'h03, 8'h01, 8'h13, 8'h8a, 8'h6b,
      8'h3a, 8'h91, 8'h11, 8'h41, 8'h4f, 8'h67, 8'hdc, 8'hea, 8'h97, 8'hf2, 8'hcf, 8'hce, 8'hf0, 8'hb4, 8'he6, 8'h73,
      8'h96, 8'hac, 8'h74, 8'h22, 8'he7, 8'had, 8'h35, 8'h85, 8'he2, 8'hf9, 8'h37, 8'he8, 8'h1c, 8'h75, 8'hdf, 8'h6e,
      8'h47, 8'hf1, 8'h1a, 8'h71, 8'h1d, 8'h29, 8'hc5, 8'h89, 8'h6f, 8'hb7, 8'h62, 8'h0e, 8'haa, 8'h18, 8'hbe, 8'h1b,
      8'hfc, 8'h56, 8'h3e, 8'h4b, 8'hc6, 8'hd2, 8'h79, 8'h20, 8'h9a, 8'hdb, 8'hc0, 8'hfe, 8'h78, 8'hcd, 8'h5a, 8'hf4,
      8'h1f, 8'hdd, 8'ha8, 8'h33, 8'h88, 8'h07, 8'hc7, 8'h31, 8'hb1, 8'h12, 8'h10, 8'h59, 8'h27, 8'h80, 8'hec, 8'h5f,
      8'h60, 8'h51, 8'h7f, 8'ha9, 8'h19, 8'hb5, 8'h4a, 8'h0d, 8'h2d, 8'he5, 8'h7a, 8'h9f, 8'h93, 8'hc9, 8'h9c, 8'hef,
      8'ha0, 8'he0, 8'h3b, 8'h4d, 8'hae, 8'h2a, 8'hf5, 8'hb0, 8'hc8, 8'heb, 8'hbb, 8'h3c, 8'h83, 8'h53, 8'h99, 8'h61,
      8'h17, 8'h2b, 8'h04, 8'h7e, 8'hba, 8'h77, 8'hd6, 8'h26, 8'he1, 8'h69, 8'h14, 8'h63, 8'h55, 8'h21, 8'h0c, 8'h7d
    };

    is_box =sb[aij];
  end
  endfunction

endmodule


/////////////////////////////////////////////////////////////////////////////////////////////////////////
// Module Name         : subword
/////////////////////////////////////////////////////////////////////////////////////////////////////////
module subword (
  input  [31:0] a,
  output [31:0] b
);

// ========================================================
// Equasions
// ========================================================
  assign b = {s_box( a[31:24] ), s_box( a[23:16] ), s_box( a[15: 8] ),  s_box( a[ 7: 0] )};
  
  function [7:0] s_box;
  input    [7:0] aij;
  reg      [7:0] sb[0:255];
  begin
    { sb[  0],sb[  1],sb[  2],sb[  3],sb[  4],sb[  5],sb[  6],sb[  7],sb[  8],sb[  9],sb[ 10],sb[ 11],sb[ 12],sb[ 13],sb[ 14],sb[ 15],
      sb[ 16],sb[ 17],sb[ 18],sb[ 19],sb[ 20],sb[ 21],sb[ 22],sb[ 23],sb[ 24],sb[ 25],sb[ 26],sb[ 27],sb[ 28],sb[ 29],sb[ 30],sb[ 31],
      sb[ 32],sb[ 33],sb[ 34],sb[ 35],sb[ 36],sb[ 37],sb[ 38],sb[ 39],sb[ 40],sb[ 41],sb[ 42],sb[ 43],sb[ 44],sb[ 45],sb[ 46],sb[ 47],
      sb[ 48],sb[ 49],sb[ 50],sb[ 51],sb[ 52],sb[ 53],sb[ 54],sb[ 55],sb[ 56],sb[ 57],sb[ 58],sb[ 59],sb[ 60],sb[ 61],sb[ 62],sb[ 63],
      sb[ 64],sb[ 65],sb[ 66],sb[ 67],sb[ 68],sb[ 69],sb[ 70],sb[ 71],sb[ 72],sb[ 73],sb[ 74],sb[ 75],sb[ 76],sb[ 77],sb[ 78],sb[ 79],
      sb[ 80],sb[ 81],sb[ 82],sb[ 83],sb[ 84],sb[ 85],sb[ 86],sb[ 87],sb[ 88],sb[ 89],sb[ 90],sb[ 91],sb[ 92],sb[ 93],sb[ 94],sb[ 95],
      sb[ 96],sb[ 97],sb[ 98],sb[ 99],sb[100],sb[101],sb[102],sb[103],sb[104],sb[105],sb[106],sb[107],sb[108],sb[109],sb[110],sb[111],
      sb[112],sb[113],sb[114],sb[115],sb[116],sb[117],sb[118],sb[119],sb[120],sb[121],sb[122],sb[123],sb[124],sb[125],sb[126],sb[127],
      sb[128],sb[129],sb[130],sb[131],sb[132],sb[133],sb[134],sb[135],sb[136],sb[137],sb[138],sb[139],sb[140],sb[141],sb[142],sb[143],
      sb[144],sb[145],sb[146],sb[147],sb[148],sb[149],sb[150],sb[151],sb[152],sb[153],sb[154],sb[155],sb[156],sb[157],sb[158],sb[159],
      sb[160],sb[161],sb[162],sb[163],sb[164],sb[165],sb[166],sb[167],sb[168],sb[169],sb[170],sb[171],sb[172],sb[173],sb[174],sb[175],
      sb[176],sb[177],sb[178],sb[179],sb[180],sb[181],sb[182],sb[183],sb[184],sb[185],sb[186],sb[187],sb[188],sb[189],sb[190],sb[191],
      sb[192],sb[193],sb[194],sb[195],sb[196],sb[197],sb[198],sb[199],sb[200],sb[201],sb[202],sb[203],sb[204],sb[205],sb[206],sb[207],
      sb[208],sb[209],sb[210],sb[211],sb[212],sb[213],sb[214],sb[215],sb[216],sb[217],sb[218],sb[219],sb[220],sb[221],sb[222],sb[223],
      sb[224],sb[225],sb[226],sb[227],sb[228],sb[229],sb[230],sb[231],sb[232],sb[233],sb[234],sb[235],sb[236],sb[237],sb[238],sb[239],
      sb[240],sb[241],sb[242],sb[243],sb[244],sb[245],sb[246],sb[247],sb[248],sb[249],sb[250],sb[251],sb[252],sb[253],sb[254],sb[255]
    } =

    { 8'h63, 8'h7c, 8'h77, 8'h7b, 8'hf2, 8'h6b, 8'h6f, 8'hc5, 8'h30, 8'h01, 8'h67, 8'h2b, 8'hfe, 8'hd7, 8'hab, 8'h76,
      8'hca, 8'h82, 8'hc9, 8'h7d, 8'hfa, 8'h59, 8'h47, 8'hf0, 8'had, 8'hd4, 8'ha2, 8'haf, 8'h9c, 8'ha4, 8'h72, 8'hc0,
      8'hb7, 8'hfd, 8'h93, 8'h26, 8'h36, 8'h3f, 8'hf7, 8'hcc, 8'h34, 8'ha5, 8'he5, 8'hf1, 8'h71, 8'hd8, 8'h31, 8'h15,
      8'h04, 8'hc7, 8'h23, 8'hc3, 8'h18, 8'h96, 8'h05, 8'h9a, 8'h07, 8'h12, 8'h80, 8'he2, 8'heb, 8'h27, 8'hb2, 8'h75,
      8'h09, 8'h83, 8'h2c, 8'h1a, 8'h1b, 8'h6e, 8'h5a, 8'ha0, 8'h52, 8'h3b, 8'hd6, 8'hb3, 8'h29, 8'he3, 8'h2f, 8'h84,
      8'h53, 8'hd1, 8'h00, 8'hed, 8'h20, 8'hfc, 8'hb1, 8'h5b, 8'h6a, 8'hcb, 8'hbe, 8'h39, 8'h4a, 8'h4c, 8'h58, 8'hcf,
      8'hd0, 8'hef, 8'haa, 8'hfb, 8'h43, 8'h4d, 8'h33, 8'h85, 8'h45, 8'hf9, 8'h02, 8'h7f, 8'h50, 8'h3c, 8'h9f, 8'ha8,
      8'h51, 8'ha3, 8'h40, 8'h8f, 8'h92, 8'h9d, 8'h38, 8'hf5, 8'hbc, 8'hb6, 8'hda, 8'h21, 8'h10, 8'hff, 8'hf3, 8'hd2,
      8'hcd, 8'h0c, 8'h13, 8'hec, 8'h5f, 8'h97, 8'h44, 8'h17, 8'hc4, 8'ha7, 8'h7e, 8'h3d, 8'h64, 8'h5d, 8'h19, 8'h73,
      8'h60, 8'h81, 8'h4f, 8'hdc, 8'h22, 8'h2a, 8'h90, 8'h88, 8'h46, 8'hee, 8'hb8, 8'h14, 8'hde, 8'h5e, 8'h0b, 8'hdb,
      8'he0, 8'h32, 8'h3a, 8'h0a, 8'h49, 8'h06, 8'h24, 8'h5c, 8'hc2, 8'hd3, 8'hac, 8'h62, 8'h91, 8'h95, 8'he4, 8'h79,
      8'he7, 8'hc8, 8'h37, 8'h6d, 8'h8d, 8'hd5, 8'h4e, 8'ha9, 8'h6c, 8'h56, 8'hf4, 8'hea, 8'h65, 8'h7a, 8'hae, 8'h08,
      8'hba, 8'h78, 8'h25, 8'h2e, 8'h1c, 8'ha6, 8'hb4, 8'hc6, 8'he8, 8'hdd, 8'h74, 8'h1f, 8'h4b, 8'hbd, 8'h8b, 8'h8a,
      8'h70, 8'h3e, 8'hb5, 8'h66, 8'h48, 8'h03, 8'hf6, 8'h0e, 8'h61, 8'h35, 8'h57, 8'hb9, 8'h86, 8'hc1, 8'h1d, 8'h9e,
      8'he1, 8'hf8, 8'h98, 8'h11, 8'h69, 8'hd9, 8'h8e, 8'h94, 8'h9b, 8'h1e, 8'h87, 8'he9, 8'hce, 8'h55, 8'h28, 8'hdf,
      8'h8c, 8'ha1, 8'h89, 8'h0d, 8'hbf, 8'he6, 8'h42, 8'h68, 8'h41, 8'h99, 8'h2d, 8'h0f, 8'hb0, 8'h54, 8'hbb, 8'h16
    };

    s_box =sb[aij];
  end
  endfunction

endmodule


/////////////////////////////////////////////////////////////////////////////////////////////////////////
// Module Name         : miscolumns
/////////////////////////////////////////////////////////////////////////////////////////////////////////
module mixcolumns( 
  input     [7:0]  s0c, s1c, s2c, s3c,
  output    [7:0]  m0c, m1c, m2c, m3c
);

// ==============================================
// Equasions
// ==============================================
  assign m0c = mul4x8( {4'h2}, s0c ) ^ mul4x8( {4'h3}, s1c ) ^ mul4x8( {4'h1}, s2c ) ^ mul4x8( {4'h1}, s3c );
  assign m1c = mul4x8( {4'h1}, s0c ) ^ mul4x8( {4'h2}, s1c ) ^ mul4x8( {4'h3}, s2c ) ^ mul4x8( {4'h1}, s3c );
  assign m2c = mul4x8( {4'h1}, s0c ) ^ mul4x8( {4'h1}, s1c ) ^ mul4x8( {4'h2}, s2c ) ^ mul4x8( {4'h3}, s3c );
  assign m3c = mul4x8( {4'h3}, s0c ) ^ mul4x8( {4'h1}, s1c ) ^ mul4x8( {4'h1}, s2c ) ^ mul4x8( {4'h2}, s3c );

  // Multiplied
  function [7:0] mul4x8;
  input    [3:0] mx;
  input    [7:0] sc;

  reg      [7:0] sxm0, sxm1, sxm2, sxm3;
  reg     [10:0] temp;
  reg      [7:0] c0, c1, c2;      // Carry

  begin
    sxm0 = sc & {8{mx[0]}};
    sxm1 = sc & {8{mx[1]}};
    sxm2 = sc & {8{mx[2]}};
    sxm3 = sc & {8{mx[3]}};

    temp = {3'b000, sxm0} ^ {2'b00, sxm1, 1'b0} ^ {1'b00, sxm2, 2'b00} ^ {sxm3, 3'b000};

    c0 = ( temp[ 8] == 1'b1 )? 8'h1B : 8'h00;
    c1 = ( temp[ 9] == 1'b1 )? (8'h1B << 1) : 8'h00;
    c2 = ( temp[10] == 1'b1 )? (8'h1B << 2) : 8'h00;

    mul4x8 = temp[7:0] ^ c0 ^ c1 ^ c2;
  end
  endfunction

endmodule


/////////////////////////////////////////////////////////////////////////////////////////////////////////
// Module Name         : inv_miscolumns
/////////////////////////////////////////////////////////////////////////////////////////////////////////
module inv_mixcolumn (
  input     [7:0]  s0c, s1c, s2c, s3c,
  output    [7:0]  m0c, m1c, m2c, m3c
);

// ==============================================
//   Equasions
// ==============================================
  assign m0c = mul4x8( {4'he}, s0c ) ^ mul4x8( {4'hb}, s1c ) ^ mul4x8( {4'hd}, s2c ) ^ mul4x8( {4'h9}, s3c );
  assign m1c = mul4x8( {4'h9}, s0c ) ^ mul4x8( {4'he}, s1c ) ^ mul4x8( {4'hb}, s2c ) ^ mul4x8( {4'hd}, s3c );
  assign m2c = mul4x8( {4'hd}, s0c ) ^ mul4x8( {4'h9}, s1c ) ^ mul4x8( {4'he}, s2c ) ^ mul4x8( {4'hb}, s3c );
  assign m3c = mul4x8( {4'hb}, s0c ) ^ mul4x8( {4'hd}, s1c ) ^ mul4x8( {4'h9}, s2c ) ^ mul4x8( {4'he}, s3c );

  function [7:0] mul4x8;
  input    [3:0] mx;
  input    [7:0] sc;
  reg      [7:0] sxm0, sxm1, sxm2, sxm3;
  reg     [10:0] temp;
  reg      [7:0] c0, c1, c2;
  begin
    sxm0 = sc & {8{mx[0]}};
    sxm1 = sc & {8{mx[1]}};
    sxm2 = sc & {8{mx[2]}};
    sxm3 = sc & {8{mx[3]}};

    temp = {3'b000, sxm0} ^ {2'b00, sxm1, 1'b0} ^ {1'b00, sxm2, 2'b00} ^ {sxm3, 3'b000};

    c0 = ( temp[8] == 1'b1 )? 8'h1B : 8'h00;
    c1 = ( temp[9] == 1'b1 )? (8'h1B << 1) : 8'h00;
    c2 = ( temp[10] == 1'b1 )? (8'h1B << 2) : 8'h00;

    mul4x8 = temp[7:0] ^ c0 ^ c1 ^ c2;
  end
  endfunction

endmodule

