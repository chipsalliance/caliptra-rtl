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
// Copyright (c) Satoh Laboratory�CUEC


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
  output         DATA_EN,
  output         BUSY,
  output   [8:0] COUNT    
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
  reg          data_ena;        // Encrypt or Decrypt Start
  //------------------------------------------

  localparam REG_SIZE      = 384;
  localparam PRIME         = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff;
  localparam ADD_NUM_ADDS  = 1;
  localparam ADD_BASE_SZ   = 384;


  reg  [31:0]  data_i;          // 32-bit data input
  reg  [7:0]   address_decoder; // Address decoding btw SW and ecc_core
  reg          wr_en_i    ;
  reg  [3:0]   wr_word_sel_i ;
  reg  [1:0]   wr_op_sel_i   ;
  reg  [2:0]   ecc_cmd_i;

  wire [31:0]  data_o;
  wire         busy_o;

  
  reg                 rd_reg_i;
  reg [3 : 0]         rd_word_sel_i;


  reg busy_reg;
  wire [8:0] count_o;
  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  ecc_arith_unit #(
        .REG_SIZE(REG_SIZE),
        .PRIME(PRIME),
        .ADD_NUM_ADDS(ADD_NUM_ADDS),
        .ADD_BASE_SZ(ADD_BASE_SZ)
        )
        ecdsa_keygen (
        .clk(CLK),
        .reset_n(RSTn& (~rst)),
        .ecc_cmd_i(ecc_cmd_i),
        .addr_i(address_decoder),
        .wr_input_sel_i(1'b0),
        .wr_op_sel_i(wr_op_sel_i),
        .wr_word_sel_i(wr_word_sel_i),
        .wr_en_i(wr_en_i),
        .rd_reg_i(rd_reg_i),
        .rd_op_sel_i(2'b00),
        .rd_word_sel_i(rd_word_sel_i),
        .data_i(data_i),
        .data_o(data_o),
        .busy_o(busy_o),
        .count_o(count_o)
        );



  //------------------------------------------

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

  // Internal bus 
  always @( * ) begin
    if ( addr_reg >= 16'h8000 && addr_reg <= 16'h8030 ) // SCALAR
      address_decoder    = 8'd00;
    else if ( addr_reg >= 16'h4000 && addr_reg < 16'h4030 ) // UOP_OPR_CONST_ZERO
      address_decoder    = 8'd00;
    else if ( addr_reg >= 16'h4100 && addr_reg < 16'h4130 ) // UOP_OPR_CONST_ONE
      address_decoder    = 8'd01;
    else if ( addr_reg >= 16'h4200 && addr_reg < 16'h4230 ) // UOP_OPR_CONST_E_a
      address_decoder    = 8'd02;
    else if ( addr_reg >= 16'h4300 && addr_reg < 16'h4330 ) // UOP_OPR_CONST_ONE_MONT
      address_decoder    = 8'd03;

    else if ( addr_reg >= 16'h4400 && addr_reg < 16'h4430 ) // UOP_OPR_CONST_GX_MONT
      address_decoder    = 8'd04;
    else if ( addr_reg >= 16'h4500 && addr_reg < 16'h4530 ) // UOP_OPR_CONST_GY_MONT
      address_decoder    = 8'd05;
    else if ( addr_reg >= 16'h4600 && addr_reg < 16'h4630 ) // UOP_OPR_CONST_GZ_MONT
      address_decoder    = 8'd06;

    else if ( addr_reg >= 16'h4800 && addr_reg < 16'h4830 ) // UOP_OPR_R0_X
      address_decoder    = 8'd08;
    else if ( addr_reg >= 16'h4900 && addr_reg < 16'h4930 ) // UOP_OPR_R0_Y
      address_decoder    = 8'd09;
    else if ( addr_reg >= 16'h4a00 && addr_reg < 16'h4a30 ) // UOP_OPR_R0_Z
      address_decoder    = 8'd10;

    else if ( addr_reg >= 16'h5000 && addr_reg < 16'h5030 ) // UOP_OPR_CONST_Qx_AFFN
      address_decoder    = 8'd16;
    else if ( addr_reg >= 16'h5100 && addr_reg < 16'h5130 ) // UOP_OPR_CONST_Qy_AFFN
      address_decoder    = 8'd17;
    else
      address_decoder    = 8'd00;

  end

  // AES register
  always @( posedge CLK or negedge RSTn ) begin
    if ( RSTn == 1'b0 ) begin
      data_ena <= 1'b0;
      rst <= 1'b0;
      busy_reg  <= 1'b0;
      ecc_cmd_i     <= 3'h0;
      data_i        <= 32'h0;
      wr_en_i       <= 1'b0;
      wr_word_sel_i <= 4'h0;
      wr_op_sel_i   <= 2'b00;
    end
    else begin

      busy_reg  <= busy_o;

      if (( write_ena == 1'b1 ) && ( addr_reg[1] == 1'b0 ) && ( addr_reg >= 16'h4000 )) 
        data_i[31:16] <= data_reg;
      else 
        data_i[31:16] <= data_i[31:16];

      
      if (( write_ena == 1'b1 ) && ( addr_reg[1] == 1'b1 ) && ( addr_reg >= 16'h4000 ))
      begin
        ecc_cmd_i     <= 3'h0;
        data_ena      <= 1'b0; 
        wr_en_i       <= 1'b1;
        wr_word_sel_i <= addr_reg[5:2];
        data_i[15:0]  <= data_reg;
        wr_op_sel_i   <= {1'b0,addr_reg[15]};
      end
      else if (( write_ena == 1'b1 ) && ( addr_reg[1] == 1'b0 ) && ( addr_reg == 16'h3000 ))
      begin
        ecc_cmd_i     <= 3'h1;
        data_ena      <= 1'b1; 
        wr_en_i       <= 1'b0;
        wr_word_sel_i <= 4'h0;
        data_i[15:0]  <= data_i[15:0];
        wr_op_sel_i   <= 2'b00;
      end
      else
      begin
        ecc_cmd_i     <= 3'h0;
        data_ena      <= 1'b0;  
        wr_en_i       <= 1'b0;
        wr_word_sel_i <= 4'h0;
        data_i[15:0]  <= data_i[15:0];
        wr_op_sel_i   <= 2'b00;
      end



      if (( write_ena == 1'b1 ) && ( addr_reg == 16'h0002 ) && ( data_reg[2] == 1'b1 )) rst <= 1'b1;
      else rst <= 1'b0;



    end
  end


  // Read data multiplax
  always @(*) begin      

      if (( now_if_state == READ3 || now_if_state == READ4 )&& ( addr_reg >= 16'h4000 ))
      begin        
        rd_reg_i       = 1;
        rd_word_sel_i  = addr_reg[5:2];
      end
      else
      begin
        rd_reg_i       = 0;
        rd_word_sel_i  = 4'h0;
      end
  end
  reg [7:0] hdout_reg_1;
  //
  always @( posedge CLK or negedge RSTn ) begin
    if ( RSTn == 1'b0 ) begin
      wbusy_reg <= 1'b0;
      rrdy_reg <= 1'b0;
      hdout_reg <=  8'h0;
      hdout_reg_1 <=  8'h0;
    end
    else begin
      if (( now_if_state == READ2 ) && ( HWE == 1'b1 )) wbusy_reg <= 1'b1;
      else if ( next_if_state == CMD ) wbusy_reg <= 1'b0;
      else wbusy_reg <= wbusy_reg;

      if ( now_if_state == READ3 ) rrdy_reg <= 1'b1;
      else if ( now_if_state == READ4 ) rrdy_reg <= 1'b1;
      else rrdy_reg <= 1'b0;

      if ( now_if_state == READ4  && addr_reg < 16'h4000  ) // BUSY address
        hdout_reg <= {5'h0, ~busy_o, ~busy_o, ~busy_o };
      else if ( now_if_state == READ3  && addr_reg[1] == 1'b0 ) 
        hdout_reg <= data_o[31:24];
      else if ( now_if_state == READ4  && addr_reg[1] == 1'b0 && HRE == 1'b1  ) 
        hdout_reg <= data_o[23:16];
      else if ( now_if_state == READ3  && addr_reg[1] == 1'b1 ) 
        hdout_reg <= data_o[15:8];
      else if ( now_if_state == READ4  && addr_reg[1] == 1'b1 && HRE == 1'b1 ) 
        hdout_reg <= data_o[7:0];
      else 
        hdout_reg <=  hdout_reg; 

        hdout_reg_1 <=  hdout_reg; 
    end
  end

  assign WRDYn = wbusy_reg;
  assign RRDYn = ~rrdy_reg;
  assign HDOUT = hdout_reg_1;

  assign DATA_EN = data_ena;
  assign BUSY = busy_reg;
  assign COUNT = count_o;

endmodule
