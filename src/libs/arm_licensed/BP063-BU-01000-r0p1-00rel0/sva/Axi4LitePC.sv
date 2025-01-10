//=============================================================================
//  The confidential and proprietary information contained in this file may
//  only be used by a person authorised under and to the extent permitted
//  by a subsisting licensing agreement from ARM Limited.
//  
//                   (C) COPYRIGHT 2010-2012 ARM Limited.
//                           ALL RIGHTS RESERVED
//  
//  This entire notice must be reproduced on all copies of this file
//  and copies of this file may only be made by a person if such person is
//  permitted to do so under the terms of a subsisting license agreement
//  from ARM Limited.
//
//-----------------------------------------------------------------------------
//  Version and Release Control Information:
//
//  File Revision       : 133304
//
//  Date                :  2012-07-09 09:36:39 +0100 (Mon, 09 Jul 2012)
//
//  Release Information : BP063-VL-70004-r0p1-00rel0
//
//-----------------------------------------------------------------------------
//  Purpose             : These are the AXI4-Lite SVA Protocol Assertions
//
//                        Supports bus widths of 32, 64 bit
//==============================================================================

//----------------------------------------------------------------------------
// CONTENTS
// ========
//  90.  Module: Axi4LitePC
// 131.    1) Parameters
// 134.         - Configurable (user can set)
// 159.         - Calculated (user should not override)
// 169.    2) Inputs (no outputs)
// 172.         - Global Signals
// 177.         - Write Address Channel
// 184.         - Write Data Channel
// 191.         - Write Response Channel
// 197.         - Read Address Channel
// 204.         - Read Data Channel
// 212.    3) Wire and Reg Declarations
// 216.           AXI4PC INSTANTIATION
// 302.    4) Verilog Defines
// 305.         - Clock and Reset
// 327.    5) Initialize simulation
// 333.         - Indicate version and release state of Axi4LitePC
// 340. 
// 341.  AXI4LITE Rules: Read Data Channel (*_R*)
// 345.    1) Functional Rules
// 348.         - AXI4LITE_ERRS_BRESP_EXOKAY
// 361. 
// 362.  AXI4LITE Rules: Write Response Channel (*_B*)
// 366.    1) Functional Rules
// 369.         - AXI4LITE_ERRS_RRESP_EXOKAY
// 382. 
// 383.  Auxiliary Logic
// 387.    1) Rules for Auxiliary Logic
// 390.         - AXI4LITE_AUX_DATA_WIDTH
// 401. 
// 402.  End of File
// 406.    1) Clear Verilog Defines
// 418.    2) End of module
//----------------------------------------------------------------------------

`timescale 1ns/1ns

//------------------------------------------------------------------------------
// AXI4LITE Standard Defines
//------------------------------------------------------------------------------

`ifndef AXI4LITEPC_OFF

`include "Axi4PC.sv"
 
`ifndef AXI4PC_TYPES
   `include "Axi4PC_defs.v"
`endif

`ifndef AXI4LITEPC_MESSAGES
  `include "Axi4LitePC_message_defs.v"
`endif

`ifndef ARM_AMBA4_PC_MSG_ERR
  `define ARM_AMBA4_PC_MSG_ERR $error
`endif

//------------------------------------------------------------------------------
// INDEX: Module: Axi4LitePC
//------------------------------------------------------------------------------

module Axi4LitePC 
  (
   // Global Signals
   ACLK,
   ARESETn,

   // Write Address Channel
   AWADDR,
   AWPROT,
   AWVALID,
   AWREADY,

   // Write Channel
   WDATA,
   WSTRB,
   WVALID,
   WREADY,

   // Write Response Channel
   BRESP,
   BVALID,
   BREADY,

   // Read Address Channel
   ARADDR,
   ARPROT,
   ARVALID,
   ARREADY,

   // Read Channel
   RDATA,
   RRESP,
   RVALID,
   RREADY

   );

//------------------------------------------------------------------------------
// INDEX:   1) Parameters
//------------------------------------------------------------------------------

  // INDEX:        - Configurable (user can set)
  // =====
  // Parameters below can be set by the user.

  // Set DATA_WIDTH to the data-bus width required
  parameter DATA_WIDTH = 64;         // data bus width, default = 64-bit

  parameter MAXRBURSTS = 16;

  // Size of CAMs for storing outstanding write bursts, this should match or
  // exceed the number of outstanding write bursts into the slave  interface
  parameter MAXWBURSTS = 16;

  // Maximum number of cycles between VALID -> READY high before a warning is
  // generated
  parameter MAXWAITS = 16;

  // Recommended Rules Enable
  parameter RecommendOn   = 1'b1;   // enable/disable reporting of all  AXI4LITE_REC*_* rules
  parameter RecMaxWaitOn  = 1'b1;   // enable/disable reporting of just AXI4LITE_REC*_MAX_WAIT rules

  // Set ADDR_WIDTH to the address-bus width required
  parameter ADDR_WIDTH = 32;        // address bus width, default = 32-bit


  // INDEX:        - Calculated (user should not override)
  // =====
  // Do not override the following parameters: they must be calculated exactly
  // as shown below
  localparam DATA_MAX   = DATA_WIDTH-1;              // data max index
  localparam ADDR_MAX   = ADDR_WIDTH-1;              // address max index
  localparam STRB_WIDTH = DATA_WIDTH/8;              // WSTRB width
  localparam STRB_MAX   = STRB_WIDTH-1;              // WSTRB max index

//------------------------------------------------------------------------------
// INDEX:   2) Inputs (no outputs)
//------------------------------------------------------------------------------

  // INDEX:        - Global Signals
  // =====
  input                ACLK;        // AXI Clock
  input                ARESETn;     // AXI Reset

  // INDEX:        - Write Address Channel
  // =====
  input   [ADDR_MAX:0] AWADDR;
  input          [2:0] AWPROT;
  input                AWVALID;
  input                AWREADY;

  // INDEX:        - Write Data Channel
  // =====
  input                WVALID;
  input                WREADY;
  input   [DATA_MAX:0] WDATA;
  input   [STRB_MAX:0] WSTRB;

  // INDEX:        - Write Response Channel
  // =====
  input          [1:0] BRESP;
  input                BVALID;
  input                BREADY;

  // INDEX:        - Read Address Channel
  // =====
  input   [ADDR_MAX:0] ARADDR;
  input          [2:0] ARPROT;
  input                ARVALID;
  input                ARREADY;

  // INDEX:        - Read Data Channel
  // =====
  input   [DATA_MAX:0] RDATA;
  input          [1:0] RRESP;
  input                RVALID;
  input                RREADY;

//------------------------------------------------------------------------------
// INDEX:   3) Wire and Reg Declarations
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:          AXI4PC INSTANTIATION
//------------------------------------------------------------------------------

Axi4PC #(   
   .DATA_WIDTH   (DATA_WIDTH),
   .ADDR_WIDTH   (ADDR_WIDTH),
   .WID_WIDTH    (1),
   .RID_WIDTH    (1),
   .AWUSER_WIDTH (1), 
   .WUSER_WIDTH  (1),  
   .BUSER_WIDTH  (1),
   .ARUSER_WIDTH (1),
   .RUSER_WIDTH  (1),
   .MAXRBURSTS   (MAXRBURSTS),
   .MAXWBURSTS   (MAXWBURSTS),
   .MAXWAITS     (MAXWAITS),
   .RecommendOn  (RecommendOn),
   .RecMaxWaitOn (RecMaxWaitOn)
        ) 
uAxi4PC 
  (
   // Global Signals
   .ACLK      (ACLK),
   .ARESETn   (ARESETn),

   // .Write  (Write Address Channel
   .AWID      (1'b0),
   .AWADDR    (AWADDR),
   .AWLEN     (8'b00000000),
   .AWSIZE    (DATA_WIDTH == 32 ? 3'b010 : 3'b011),
   .AWBURST   (2'b00),
   .AWLOCK    (1'b0),
   .AWCACHE   (4'b0000),
   .AWPROT    (AWPROT),
   .AWQOS     (4'b0000),
   .AWREGION  (4'b0000),
   .AWUSER    (1'b0),
   .AWVALID   (AWVALID),
   .AWREADY   (AWREADY),

   // .Write  (Write Channel
   .WLAST     (1'b1),
   .WDATA     (WDATA),
   .WSTRB     (WSTRB),
   .WUSER     (1'b0),
   .WVALID    (WVALID),
   .WREADY    (WREADY),

   // .Write  (Write Response Channel
   .BID       (1'b0),
   .BRESP     (BRESP),
   .BUSER     (1'b0),
   .BVALID    (BVALID),
   .BREADY    (BREADY),

   // .Read  (Read Address Channel
   .ARID      (1'b0),
   .ARADDR    (ARADDR),
   .ARLEN     (8'b00000000),
   .ARSIZE    (DATA_WIDTH == 32 ? 3'b010 : 3'b011),
   .ARBURST   (2'b00),
   .ARLOCK    (1'b0),
   .ARCACHE   (4'b0000),
   .ARPROT    (ARPROT),
   .ARQOS     (4'b0000),
   .ARREGION  (4'b0000),
   .ARUSER    (1'b0),
   .ARVALID   (ARVALID),
   .ARREADY   (ARREADY),

   // .Read  (Read Channel
   .RID       (1'b0),
   .RLAST     (1'b1),
   .RDATA     (RDATA),
   .RRESP     (RRESP),
   .RUSER     (1'b0),
   .RVALID    (RVALID),
   .RREADY    (RREADY),

   // .Low  (Low power interface
   .CACTIVE   (1'b1),
   .CSYSREQ   (1'b1),
   .CSYSACK   (1'b1)
   );

//------------------------------------------------------------------------------
// INDEX:   4) Verilog Defines
//------------------------------------------------------------------------------

  // INDEX:        - Clock and Reset
  // =====
  // Can be overridden by user for a clock enable.
  //
  // Can also be used to clock SVA on negedge (to avoid race hazards with
  // auxiliary logic) by compiling with the override:
  //
  //   +define+AXI4_SVA_CLK=~ACLK
  // 
  // SVA: Assertions

  `ifdef AXI4_SVA_CLK
  `else
     `define AXI4_SVA_CLK ACLK
  `endif
 
  `ifdef AXI4_SVA_RSTn
  `else
     `define AXI4_SVA_RSTn ARESETn
  `endif

//------------------------------------------------------------------------------
// INDEX:   5) Initialize simulation
//------------------------------------------------------------------------------

  initial
    begin

       // INDEX:        - Indicate version and release state of Axi4LitePC
       // =====
       $display("AXI4LITE_INFO: Running Axi4LitePC $State");

    end

//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI4LITE Rules: Read Data Channel (*_R*)
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4LITE_ERRS_BRESP_EXOKAY
  // =====
  property AXI4LITE_ERRS_BRESP_EXOKAY;
    @(posedge `AXI4_SVA_CLK)
        !($isunknown({BVALID,BRESP})) &
        BVALID
        |-> BRESP != `AXI4PC_RESP_EXOKAY;
  endproperty
  axi4lite_errs_bresp_exokay: assert property (AXI4LITE_ERRS_BRESP_EXOKAY) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_AXI4LITE_BRESP_EXOKAY);


//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI4LITE Rules: Write Response Channel (*_B*)
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4LITE_ERRS_RRESP_EXOKAY
  // =====
  property AXI4LITE_ERRS_RRESP_EXOKAY;
    @(posedge `AXI4_SVA_CLK)
        !($isunknown({RVALID,RRESP})) &
        RVALID
        |-> RRESP != `AXI4PC_RESP_EXOKAY;
  endproperty
  axi4lite_errs_rresp_exokay: assert property (AXI4LITE_ERRS_RRESP_EXOKAY) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_AXI4LITE_RRESP_EXOKAY);


//------------------------------------------------------------------------------
// INDEX:
// INDEX: Auxiliary Logic
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Rules for Auxiliary Logic
//------------------------------------------------------------------------------

  // INDEX:        - AXI4LITE_AUX_DATA_WIDTH
  // =====
  property AXI4LITE_AUX_DATA_WIDTH;
    @(posedge `AXI4_SVA_CLK)
      (DATA_WIDTH ==   32 ||
       DATA_WIDTH ==   64);
  endproperty
  axi4lite_aux_data_width: assert property (AXI4LITE_AUX_DATA_WIDTH) else
   `ARM_AMBA4_PC_MSG_ERR(`AUX_AXI4LITE_DATA_WIDTH);

//------------------------------------------------------------------------------
// INDEX:
// INDEX: End of File
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Clear Verilog Defines
//------------------------------------------------------------------------------

  // Error and Warning Messages
  `undef ARM_AMBA4_PC_MSG_ERR
  
  // Clock and Reset
  `undef AXI4_SVA_CLK
  `undef AXI4_SVA_RSTn
 
 
//------------------------------------------------------------------------------
// INDEX:   2) End of module
//------------------------------------------------------------------------------

`include "Axi4PC_undefs.v"
`include "Axi4LitePC_message_undefs.v"
endmodule // Axi4LitePC
`endif    //AXI4LITEPC_OFF
