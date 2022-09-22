`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////
// Company             : UEC
// Engineer            : 
// 
// Create Date         : July/29/2014 
// Module Name         : sakura_g_aes128
// Project Name        : sakura_g_aes128
// Target Devices      : xc6slx75-2csg484
// Tool versions       : 14.6
// Description         : 
//
// Dependencies        : 
//
// Version             : 1.0
// Last Uodate         : July/29/2014
// Additional Comments : 
///////////////////////////////////////////////////////////////////////////////////////
// Copyright (c) Satoh Laboratory�CUEC

module sakura_g_aes128(
  // Host interface
  input         lbus_rstn,    // Reset from Control FPGA
  input         lbus_clk,     // Clock from Control FPGA

  output        lbus_rdy,     // Device ready
  input   [7:0] lbus_wd,      // Local bus data input
  input         lbus_we,      // Data write enable
  output        lbus_ful,     // Data write ready low
  output        lbus_aful,    // Data near write end
  output  [7:0] lbus_rd,      // Data output
  input         lbus_re,      // Data read enable
  output        lbus_emp,     // Data read ready low
  output        lbus_aemp,    // Data near read end
  output        TRGOUTn,      // AES start trigger (SAKURA-G Only)

  // LED display
  output  [9:0] led,          // M_LED (led[8], led[9] SAKURA-G Only)

  // Trigger output
  output  [2:0] M_HEADER,     // User Header Pin (SAKURA-G Only)
  output        M_CLK_EXT0_P, // J4 SMA  AES start (SAKURA-G Only)

  // FTDI USB interface portB (SAKURA-G Only)
  // FTDI side
  input         FTDI_BCBUS0_RXF_B,
  input         FTDI_BCBUS1_TXE_B,
  output        FTDI_BCBUS2_RD_B,
  output        FTDI_BCBUS3_WR_B,
  inout   [7:0] FTDI_BDBUS_D,

  // FTDI USB interface portB (SAKURA-G Only)
  // Control FPGA side
  output        PORT_B_RXF,
  output        PORT_B_TXE,
  input         PORT_B_RD,
  input         PORT_B_WR,
  input   [7:0] PORT_B_DIN,
  output  [7:0] PORT_B_DOUT,
  input         PORT_B_OEn
);

// ================================================================================
// Internal signals
// ================================================================================
  // Reset and clock
  wire          resetn;       // Hardware reset
  wire          clock;        // System clock

  // Block cipher
  wire          enc_dec;      // Encrypt/Decrypt select. 0:Encrypt  1:Decrypt
  wire          key_exp;      // Round Key Expansion
  wire          start;        // Encrypt or Decrypt Start
  wire  [127:0] key;          // Round Key input
  wire  [127:0] text_in;      // Cipher Text or Inverse Cipher Text input
  wire  [127:0] text_out;     // Cipher Text or Inverse Cipher Text output
  wire          key_val;      // Round Key valid
  wire          text_val;     // Cipher Text or Inverse Cipher Text valid
  wire          busy;         // AES unit Busy

  // etc
  wire    [8:0] count;        // Clock moniter counter

// ================================================================================
// Equasions
// ================================================================================
  // ------------------------------------------------------------------------------
  // Clock input driver
  // ------------------------------------------------------------------------------
  IBUFG clkdrv (.I( lbus_clk ), .O( clock ));   // 48MHz input

  // ------------------------------------------------------------------------------
  // Triger signals output
  // ------------------------------------------------------------------------------
  assign M_HEADER[0] = start;      // trig_startn
  assign M_HEADER[1] = 1'b0;   // trig_endn
  assign M_HEADER[2] = 1'b0;       // trig_exec

  assign M_CLK_EXT0_P = start;     // SMA J4 output

  assign TRGOUTn = ~start;

  // ------------------------------------------------------------------------------
  // Host interface
  // ------------------------------------------------------------------------------
  host_if host_if (
    .RSTn( lbus_rstn ), .CLK( clock ),
    .RSTOUTn( resetn ),
    .DEVRDY( lbus_rdy ), .RRDYn( lbus_emp ), .WRDYn( lbus_ful ),
    .HRE( lbus_re ), .HWE( lbus_we ), .HDIN( lbus_wd ), .HDOUT( lbus_rd ),
    .DATA_EN( start ), .BUSY(busy), .COUNT(count)
  );

  assign lbus_aful = 1'b1;
  assign lbus_aemp = 1'b1;




  // ------------------------------------------------------------------------------
  // LED display outputs
  // ------------------------------------------------------------------------------
  assign led[0] = count[0];
  assign led[1] = count[1];      // Main FPGA ready
  assign led[2] = count[2];
  assign led[3] = count[3];
  assign led[4] = count[4];
  assign led[5] = count[5];
  assign led[6] = count[6];
  assign led[7] = count[7];
  assign led[8] = count[8];
  assign led[9] = busy;

  // ------------------------------------------------------------------------------
  // USB PORT B
  // ------------------------------------------------------------------------------
  assign PORT_B_RXF = FTDI_BCBUS0_RXF_B;
  assign PORT_B_TXE = FTDI_BCBUS1_TXE_B;
  assign FTDI_BCBUS2_RD_B = PORT_B_RD;
  assign FTDI_BCBUS3_WR_B = PORT_B_WR;
  assign FTDI_BDBUS_D = ( PORT_B_OEn == 1'b0 )? PORT_B_DIN : 8'hzz;
  assign PORT_B_DOUT = FTDI_BDBUS_D;

endmodule

