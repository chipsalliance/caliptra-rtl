`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company             : UEC
// Engineer: 
// 
// Create Date         : July/29/2014
// Module Name:        : host_if
// Project Name        : sakura_g_aes128
// Target Devices:     : xc6slx75-2csg484
// Tool versions       : 13.4
// Description         : 
//
// Dependencies        : 
//
// Version             : 1.0
// Last Uodate         : July/29/2014
// Additional Comments : 
//////////////////////////////////////////////////////////////////////////////////
// Copyright (c) Satoh LaboratoryÅCUEC


module host_if(
  input          RSTn,     // Reset input
  input          CLK,      // Clock input

  output         DEVRDY,   // Device ready
  output         RRDYn,    // Read data empty
  output         WRDYn,    // Write buffer almost full
  input          HRE,      // Host read enable
  input          HWE,      // Host write enable
  input    [7:0] HDIN,     // Host data input
  output   [7:0] HDOUT,    // Host data output

  output         RSTOUTn,  // Internal reset output
  output         ENCn_DEC, // Encrypt/Decrypt select
  output         KEY_GEN,  // Round key generate
  output         DATA_EN,  // Encrypt or Decrypt Start
  input          KVAL,     // Round Key valid
  input          TVAL,
  output [127:0] KEY_OUT,  // Cipher key output
  output [127:0] DATA_OUT, // Cipher Text or Inverse Cipher Text output
  input  [127:0] RESULT    // Cipher Text or Inverse Cipher Text input
);


  parameter [3:0]  CMD = 4'h0, READ1 = 4'h1, READ2 = 4'h2, READ3 = 4'h3, READ4 = 4'h4,
                   WRITE1 = 4'h5, WRITE2 = 4'h6, WRITE3 = 4'h7, WRITE4 = 4'h8;

// ==================================================================
// Internal signals
// ==================================================================
  reg    [4:0] cnt;             // Reset delay counter
  reg          lbus_we_reg;     // Write input register
  reg    [7:0] lbus_din_reg;    // Write data input register
  reg    [3:0] next_if_state;   // Host interface next state  machine registers
  reg    [3:0] now_if_state;    // Host interface now state machine registers
  reg   [15:0] addr_reg;        // Internal address bus register
  reg   [15:0] data_reg;        // Internal write data bus register
  reg          write_ena;       // Internal register write enable

  reg          rst;             // Internal reset
  reg          enc_dec;         // Encrypt/Decrypt select register
  reg          key_gen;         // Round key generate
  reg          data_ena;        // Encrypt or Decrypt Start
  reg  [127:0] key_reg;         // Cipher Key register
  reg  [127:0] din_reg;         // Text input register

  reg          wbusy_reg;       // Write busy register
  reg          rrdy_reg;        // Read ready register
  reg   [15:0] dout_mux;        // Read data multiplex
  reg    [7:0] hdout_reg;       // Read data register
 
// ================================================================================
// Equasions
// ================================================================================
  // Reset delay counter
  always @( posedge CLK or negedge RSTn ) begin
    if ( RSTn == 1'b0 ) cnt <= 5'h00;
    else if (~&cnt) cnt <= cnt + 1'b1;
  end

  assign RSTOUTn = &cnt[3:0];
  assign DEVRDY  = &cnt;

  // Local bus input registers
  always @( posedge CLK or negedge RSTn ) begin
    if ( RSTn == 1'b0 ) begin
      lbus_we_reg <= 1'b0;
      lbus_din_reg <= 8'h00;
    end
    else begin
      lbus_we_reg <= HWE;

      if ( HWE == 1'b1 ) lbus_din_reg <= HDIN;
      else lbus_din_reg <= lbus_din_reg;
    end
  end

  // State machine register
  always @( posedge CLK or negedge RSTn ) begin
    if ( RSTn == 1'b0 ) begin
      now_if_state <= CMD;
    end
    else begin
      now_if_state <= next_if_state;
    end
  end

  // State machine control
  always @( now_if_state or lbus_we_reg or lbus_din_reg or HRE ) begin
    case ( now_if_state )
      CMD  : if ( lbus_we_reg == 1'b1 )
                if ( lbus_din_reg == 8'h00 ) next_if_state = READ1;
                else if ( lbus_din_reg == 8'h01 ) next_if_state = WRITE1;
                else next_if_state = CMD;
              else next_if_state = CMD;

      READ1 : if ( lbus_we_reg == 1'b1 ) next_if_state = READ2;   // Address High read
              else next_if_state = READ1;
      READ2 : if ( lbus_we_reg == 1'b1 ) next_if_state = READ3;   // Address Low read
              else next_if_state = READ2;
      READ3 : if ( HRE == 1'b1 ) next_if_state = READ4;           // Data High read
              else  next_if_state = READ3;
      READ4 : if ( HRE == 1'b1 ) next_if_state = CMD;            // Data Low read
              else  next_if_state = READ4;

      WRITE1: if ( lbus_we_reg == 1'b1 ) next_if_state = WRITE2;  // Address High read
              else next_if_state = WRITE1;
      WRITE2: if ( lbus_we_reg == 1'b1 ) next_if_state = WRITE3;  // Address Low read
              else next_if_state = WRITE2;
      WRITE3: if ( lbus_we_reg == 1'b1 ) next_if_state = WRITE4;  // Data High write
              else next_if_state = WRITE3;
      WRITE4: if ( lbus_we_reg == 1'b1 ) next_if_state = CMD;    // Data Low write
              else next_if_state = WRITE4;
     default: next_if_state = CMD; 
    endcase
  end

  // Internal bus 
  always @( posedge CLK or negedge RSTn ) begin
    if ( RSTn == 1'b0 ) begin
      addr_reg <= 16'h0000;
      data_reg <= 16'h0000;
      write_ena <= 1'b0;
    end
    else begin
      if (( now_if_state == READ1 ) || ( now_if_state == WRITE1 )) addr_reg[15:8] <= lbus_din_reg;
      else addr_reg[15:8] <= addr_reg[15:8];

      if (( now_if_state == READ2 ) || ( now_if_state == WRITE2 )) addr_reg[7:0] <= lbus_din_reg;
      else addr_reg[7:0] <= addr_reg[7:0];

      if ( now_if_state == WRITE3 ) data_reg[15:8] <= lbus_din_reg;
      else data_reg[15:8] <= data_reg[15:8];

      if ( now_if_state == WRITE4 ) data_reg[7:0] <= lbus_din_reg;
      else data_reg[7:0] <= data_reg[7:0];

      write_ena <= (( now_if_state == WRITE4 ) && ( next_if_state == CMD ))? 1'b1 : 1'b0;
    end
  end

  // AES register
  always @( posedge CLK or negedge RSTn ) begin
    if ( RSTn == 1'b0 ) begin
      key_gen <= 1'b0;
      data_ena <= 1'b0;
      rst <= 1'b0;
      enc_dec <= 1'b0;
      key_reg <= 128'h00000000_00000000_00000000_00000000;
      din_reg <= 128'h00000000_00000000_00000000_00000000;
    end
    else begin
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0002 ) && ( data_reg[0] == 1'b1 )) data_ena <= 1'b1;
      else data_ena <= 1'b0;

      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0002 ) && ( data_reg[1] == 1'b1 )) key_gen <= 1'b1;
      else key_gen <= 1'b0;

      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0002 ) && ( data_reg[2] == 1'b1 )) rst <= 1'b1;
      else rst <= 1'b0;

      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h000c ) && ( data_reg[0] == 1'b1 )) enc_dec <= data_reg[0];
      else enc_dec <= enc_dec;

      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0100 )) key_reg[127:112] <= data_reg;
      else key_reg[127:112] <= key_reg[127:112];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0102 )) key_reg[111: 96] <= data_reg;
      else key_reg[111:96] <= key_reg[111:96];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0104 )) key_reg[ 95: 80] <= data_reg;
      else key_reg[ 95: 80] <= key_reg[ 95: 80];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0106 )) key_reg[ 79: 64] <= data_reg;
      else key_reg[ 79: 64] <= key_reg[ 79: 64];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0108 )) key_reg[ 63: 48] <= data_reg;
      else key_reg[ 63: 48] <= key_reg[ 63: 48];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h010a )) key_reg[ 47: 32] <= data_reg;
      else key_reg[ 47: 32] <= key_reg[ 47: 32];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h010c )) key_reg[ 31: 16] <= data_reg;
      else key_reg[ 31: 16] <= key_reg[ 31: 16];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h010e )) key_reg[ 15:  0] <= data_reg;
      else key_reg[ 15:  0] <= key_reg[ 15:  0];

      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0140 )) din_reg[127:112] <= data_reg;
      else din_reg[127:112] <= din_reg[127:112];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0142 )) din_reg[111: 96] <= data_reg;
      else din_reg[111:96] <= din_reg[111:96];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0144 )) din_reg[ 95: 80] <= data_reg;
      else din_reg[ 95: 80] <= din_reg[ 95: 80];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0146 )) din_reg[ 79: 64] <= data_reg;
      else din_reg[ 79: 64] <= din_reg[ 79: 64];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0148 )) din_reg[ 63: 48] <= data_reg;
      else din_reg[ 63: 48] <= din_reg[ 63: 48];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h014a )) din_reg[ 47: 32] <= data_reg;
      else din_reg[ 47: 32] <= din_reg[ 47: 32];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h014c )) din_reg[ 31: 16] <= data_reg;
      else din_reg[ 31: 16] <= din_reg[ 31: 16];
      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h014e )) din_reg[ 15:  0] <= data_reg;
      else din_reg[ 15:  0] <= din_reg[ 15:  0];
    end
  end


  // Read data multiplax
  always @( addr_reg or rst or enc_dec or key_gen or data_ena or KVAL or TVAL or RESULT ) begin
    case( addr_reg )
      16'h0002: dout_mux = { 13'h0000, rst, key_gen, data_ena };
      16'h000c: dout_mux = { KVAL, TVAL, enc_dec };
      16'h0180: dout_mux = RESULT[127:112];
      16'h0182: dout_mux = RESULT[111:96];
      16'h0184: dout_mux = RESULT[95:80];
      16'h0186: dout_mux = RESULT[79:64];
      16'h0188: dout_mux = RESULT[63:48];
      16'h018a: dout_mux = RESULT[47:32];
      16'h018c: dout_mux = RESULT[31:16];
      16'h018e: dout_mux = RESULT[15:0];
      16'hfffc: dout_mux = 16'h4522;
       default: dout_mux = 16'h0000;
    endcase
  end

  //
  always @( posedge CLK or negedge RSTn ) begin
    if ( RSTn == 1'b0 ) begin
      wbusy_reg <= 1'b0;
      rrdy_reg <= 1'b0;
      hdout_reg <= 8'h00;
    end
    else begin
      if (( now_if_state == READ2 ) && ( HWE == 1'b1 )) wbusy_reg <= 1'b1;
      else if ( next_if_state == CMD ) wbusy_reg <= 1'b0;
      else wbusy_reg <= wbusy_reg;

      if ( now_if_state == READ3 ) rrdy_reg <= 1'b1;
      else if ( now_if_state == READ4 ) rrdy_reg <= 1'b1;
      else rrdy_reg <= 1'b0;

      if ( now_if_state == READ3 ) hdout_reg <= dout_mux[15:8];
      else if ( now_if_state == READ4 ) hdout_reg <= dout_mux[7:0];
      else hdout_reg <= hdout_reg;
    end
  end

  assign WRDYn = wbusy_reg;
  assign RRDYn = ~rrdy_reg;
  assign HDOUT = hdout_reg;

  assign ENCn_DEC = enc_dec;
  assign KEY_GEN = key_gen;
  assign DATA_EN = data_ena;
  assign KEY_OUT = key_reg;
  assign DATA_OUT = din_reg;

endmodule
