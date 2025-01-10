//============================================================================
//
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
//------------------------------------------------------------------------------
//  Version and Release Control Information:
//
//  File Revision       : 133318
//
//  Date                :  2012-07-09 10:49:37 +0100 (Mon, 09 Jul 2012)
//  
//  Release Information : BP063-VL-70004-r0p1-00rel0
//
//------------------------------------------------------------------------------
//  Purpose             : These are the AXI4-Stream SVA Protocol Assertions
//
//                        Supports bus widths of 32, 64, 128, 256, 512, 1024 bit
//============================================================================

//----------------------------------------------------------------------------
// CONTENTS
// ========
// 117.  Module: Axi4StreamPC
// 139.    1) Parameters
// 142.         - Configurable (user can set)
// 166.         - Calculated (user should not override)
// 184.    2) Inputs (no outputs)
// 187.         - Global Signals
// 193.         - AXI4-Stream Interface
// 206.    3) Wire and Reg Declarations
// 230.    4) Verilog Defines
// 233.         - Clock and Reset
// 266.    4) Initialize simulation
// 272.         - Format for time reporting
// 277.         - Indicate version and release state of Axi4StreamPC
// 282.         - Warn if any/some recommended rules are disabled
// 319. 
// 320.  AXI4STREAM Rules: Stream Interface (*_T*)
// 324.    1) Functional Rules
// 327.         - AXI4STREAM_ERRM_TVALID_RESET
// 339.    2) Handshake Rules
// 342.         - AXI4STREAM_ERRM_TID_STABLE
// 355.         - AXI4STREAM_ERRM_TDEST_STABLE
// 368.         - AXI4STREAM_ERRM_TKEEP_STABLE
// 381.         - AXI4STREAM_ERRM_TDATA_STABLE
// 394.         - AXI4STREAM_ERRM_TLAST_STABLE
// 407.         - AXI4STREAM_ERRM_TSTRB_STABLE
// 420.         - AXI4STREAM_ERRM_TVALID_STABLE
// 432.         - AXI4STREAM_RECS_TREADY_MAX_WAIT 
// 450.         - AXI4STREAM_ERRM_TUSER_STABLE
// 463.         - AXI4STREAM_ERRM_TKEEP_TSTRB
// 475.         - AXI4STREAM_ERRM_STREAM_ALL_DONE_EOS 
// 495.    3) X-Propagation Rules
// 501.         - AXI4STREAM_ERRM_TID_X
// 512.         - AXI4STREAM_ERRM_TDEST_X
// 523.         - AXI4STREAM_ERRM_TKEEP_X
// 534.         - AXI4STREAM_ERRM_TDATA_X
// 545.         - AXI4STREAM_ERRM_TLAST_X
// 556.         - AXI4STREAM_ERRM_TSTRB_X
// 567.         - AXI4STREAM_ERRM_TVALID_X
// 578.         - AXI4STREAM_ERRS_TREADY_X
// 589.         - AXI4STREAM_ERRM_TUSER_X
// 603.    4) Zero Width Stability Rules
// 606.         - AXI4STREAM_ERRM_TDATA_TIEOFF
// 619.         - AXI4STREAM_ERRM_TKEEP_TIEOFF
// 632.         - AXI4STREAM_ERRM_TSTRB_TIEOFF
// 645.         - AXI4STREAM_ERRM_TID_TIEOFF
// 658.         - AXI4STREAM_ERRM_TDEST_TIEOFF
// 671.         - AXI4STREAM_ERRM_TUSER_TIEOFF
// 684.    5) Auxiliary Logic Rules
// 688.         - AXI4STREAM_AUXM_TID_TDEST_WIDTH
// 699. 
// 700.  Auxiliary Logic
// 704.    1) Stream Tracking Logic and Functions
// 708.         a) StreamInUse array
// 733.         b) ActiveStreams function
// 745.    2) Combinatorial Logic
// 749.         a) Masks
// 752.            - TdataMask
// 764. 
// 765.  End of File
// 769.    1) Clear Verilog Defines
// 787.    2) End of module
//----------------------------------------------------------------------------

`timescale 1ns/1ns

//------------------------------------------------------------------------------
// AXI4STREAM Standard Defines
//------------------------------------------------------------------------------

`ifndef AXI4STREAMPC_OFF

`ifndef AXI4STREAMPC_MESSAGES
  `include "Axi4StreamPC_message_defs.v"
`endif

`ifndef ARM_AMBA4_PC_MSG_ERR
  `define ARM_AMBA4_PC_MSG_ERR $error
`endif

`ifndef ARM_AMBA4_PC_MSG_WARN
  `define ARM_AMBA4_PC_MSG_WARN $warning
`endif

//------------------------------------------------------------------------------
// INDEX: Module: Axi4StreamPC
//------------------------------------------------------------------------------
module Axi4StreamPC 
  (
   // Global Signals
   ACLK,
   ARESETn,

   // Streaming Interface
   TDATA,
   TSTRB,
   TKEEP,
   TLAST,
   TID,
   TDEST,
   TUSER,
   TVALID,
   TREADY

   );

//------------------------------------------------------------------------------
// INDEX:   1) Parameters
//------------------------------------------------------------------------------

  // INDEX:        - Configurable (user can set)
  // =====
  // Parameters below can be set by the user.

  // Set DATA_WIDTH to the data-bus width required
  parameter DATA_WIDTH_BYTES = 4;         // data bus width, default = 64-bit
  parameter DEST_WIDTH = 4;               // TDEST width, default = 4-bit

  // Select the number of ID bits required
  parameter ID_WIDTH = 4;                 // (T)ID width

  // Select the size of the USER buses, default = 32-bit
  parameter USER_WIDTH  = 32;            // width of the user sideband field

  // Maximum number of cycles between VALID -> READY high before a warning is
  // generated
  parameter MAXWAITS = 16;

  // Recommended Rules Enable
  // enable/disable reporting of all  AXI4STREAM_REC*_* rules
  parameter RecommendOn   = 1'b1; 
  // enable/disable reporting of just AXI4STREAM_REC*_MAX_WAIT rules        
  parameter RecMaxWaitOn  = 1'b1;         

  // INDEX:        - Calculated (user should not override)
  // =====
  // Do not override the following parameters: they must be calculated exactly
  // as shown below
  // data max index
  localparam    DATA_MAX = DATA_WIDTH_BYTES ? (DATA_WIDTH_BYTES*8)-1:0; 
  localparam    DEST_MAX = DEST_WIDTH ? DEST_WIDTH-1:0;    // dest max index             
  localparam  STRB_WIDTH = DATA_WIDTH_BYTES;               // TSTRB width
  localparam    STRB_MAX = STRB_WIDTH ? STRB_WIDTH-1:0;    // TSTRB max index
  localparam    KEEP_MAX = STRB_WIDTH ? STRB_WIDTH-1:0;    // TKEEP max index
  localparam      ID_MAX = ID_WIDTH ? ID_WIDTH-1:0;        // ID max index
  localparam   TUSER_MAX = USER_WIDTH? USER_WIDTH-1:0;   // TUSER  max index
  
  // Size of array for storing in use id/dest combinations
  localparam      ID_VAL_MAX =  (1 << (ID_WIDTH))   -1;    
  localparam    DEST_VAL_MAX =  (1 << (DEST_WIDTH)) -1;                 

//------------------------------------------------------------------------------
// INDEX:   2) Inputs (no outputs)
//------------------------------------------------------------------------------

  // INDEX:        - Global Signals
  // =====
  input                ACLK;        // AXI Clock
  input                ARESETn;     // AXI Reset


  // INDEX:        - AXI4-Stream Interface
  // =====
  input   [DATA_MAX:0] TDATA;
  input   [STRB_MAX:0] TSTRB;
  input   [KEEP_MAX:0] TKEEP;
  input                TLAST;
  input     [ID_MAX:0] TID;
  input   [DEST_MAX:0] TDEST;
  input  [TUSER_MAX:0] TUSER;
  input                TVALID;
  input                TREADY;

//------------------------------------------------------------------------------
// INDEX:   3) Wire and Reg Declarations
//------------------------------------------------------------------------------

  // User signal definitions are defined as weak pull-down in the case
  // that they are unconnected.
  tri0    [DATA_MAX:0] TDATA;
  tri0    [STRB_MAX:0] TSTRB;
  tri0    [KEEP_MAX:0] TKEEP;
  tri0      [ID_MAX:0] TID;
  tri0    [DEST_MAX:0] TDEST;
  tri0   [TUSER_MAX:0] TUSER;

`ifdef AXI4STREAM_END_OF_SIMULATION
  // Array holding one bit for each possible stream indicating if it is active
  reg                  StreamInUse [ID_VAL_MAX:0][DEST_VAL_MAX:0];
`endif

  // signals for Data Checking
  reg     [DATA_MAX:0] TdataMask;
  
  reg                  i_RecommendOn;
  reg                  i_RecMaxWaitOn;
 
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

  // AUX: Auxiliary Logic
  `ifdef AXI4_AUX_CLK
  `else
     `define AXI4_AUX_CLK ACLK
  `endif
  
  `ifdef AXI4_AUX_RSTn
  `else
     `define AXI4_AUX_RSTn ARESETn
  `endif

//------------------------------------------------------------------------------
// INDEX:   4) Initialize simulation
//------------------------------------------------------------------------------

  initial
    begin

      // INDEX:        - Format for time reporting
      // =====
      // Format for time reporting
      $timeformat(-9, 0, " ns", 0);

      // INDEX:        - Indicate version and release state of Axi4StreamPC
      // =====
      $display("AXI4STREAM_INFO: Running AxiStreamPC $State");


      // INDEX:        - Warn if any/some recommended rules are disabled
      // =====
      if (~RecommendOn)
      begin
        // All AXI4STREAM_REC*_* rules disabled
        $display("AXI4STREAM_WARN: All recommended AXI rules have been", 
                 "disabled by the RecommendOn parameter");
      end
      else if (~RecMaxWaitOn)
      begin
        // Just AXI4STREAM_REC*_MAX_WAIT rules disabled
        $display("AXI4STREAM_WARN: All recommended MAX_WAIT rules have", 
                 "been disabled by the RecMaxWaitOn parameter");
      end

      if (RecommendOn)
        i_RecommendOn = 1'b1;
      else
        i_RecommendOn = 1'b0;

      if (RecMaxWaitOn)
        i_RecMaxWaitOn = 1'b1;
      else
        i_RecMaxWaitOn = 1'b0;

`ifdef AXI4STREAM_END_OF_SIMULATION
      // Initialise StreamInUse array 
      begin
        for (int i = 0; i <= ID_VAL_MAX; i++)
          for (int j = 0; j <= DEST_VAL_MAX; j++)
            StreamInUse[i][j] = 1'b0;
      end
`endif

   end

//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI4STREAM Rules: Stream Interface (*_T*)
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4STREAM_ERRM_TVALID_RESET
  // =====
  property AXI4STREAM_ERRM_TVALID_RESET;
    @(posedge `AXI4_SVA_CLK)
      !(`AXI4_SVA_RSTn) & !($isunknown(`AXI4_SVA_RSTn))
      ##1   `AXI4_SVA_RSTn
      |-> !TVALID;
  endproperty
  axi4stream_errm_tvalid_reset: assert property (AXI4STREAM_ERRM_TVALID_RESET) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TVALID_RESET);

//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4STREAM_ERRM_TID_STABLE
  // =====
  property AXI4STREAM_ERRM_TID_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({TVALID,TREADY,TID})) &
      `AXI4_SVA_RSTn & TVALID & !TREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(TID);
  endproperty
  axi4stream_errm_tid_stable: assert property (AXI4STREAM_ERRM_TID_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TID_STABLE);


  // INDEX:        - AXI4STREAM_ERRM_TDEST_STABLE
  // =====
  property AXI4STREAM_ERRM_TDEST_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({TVALID,TREADY,TDEST})) &
      `AXI4_SVA_RSTn & TVALID & !TREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(TDEST);
  endproperty
  axi4stream_errm_tdest_stable: assert property (AXI4STREAM_ERRM_TDEST_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TDEST_STABLE);
 

  // INDEX:        - AXI4STREAM_ERRM_TKEEP_STABLE
  // =====
  property AXI4STREAM_ERRM_TKEEP_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({TVALID,TREADY,TKEEP})) &
      `AXI4_SVA_RSTn & TVALID & !TREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(TKEEP);
  endproperty
  axi4stream_errm_tkeep_stable: assert property (AXI4STREAM_ERRM_TKEEP_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TKEEP_STABLE);
 

  // INDEX:        - AXI4STREAM_ERRM_TDATA_STABLE
  // =====
  property AXI4STREAM_ERRM_TDATA_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({TVALID,TREADY,TDATA})) &
      `AXI4_SVA_RSTn & TVALID & !TREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(TDATA & TdataMask);
  endproperty
  axi4stream_errm_tdata_stable: assert property (AXI4STREAM_ERRM_TDATA_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TDATA_STABLE);


  // INDEX:        - AXI4STREAM_ERRM_TLAST_STABLE
  // =====
  property AXI4STREAM_ERRM_TLAST_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({TVALID,TREADY,TLAST})) &
      `AXI4_SVA_RSTn & TVALID & !TREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(TLAST);
  endproperty
  axi4stream_errm_tlast_stable: assert property (AXI4STREAM_ERRM_TLAST_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TLAST_STABLE);


  // INDEX:        - AXI4STREAM_ERRM_TSTRB_STABLE
  // =====
  property AXI4STREAM_ERRM_TSTRB_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({TVALID,TREADY,TSTRB})) &
      `AXI4_SVA_RSTn & TVALID & !TREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(TSTRB);
  endproperty
  axi4stream_errm_tstrb_stable: assert property (AXI4STREAM_ERRM_TSTRB_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TSTRB_STABLE);


  // INDEX:        - AXI4STREAM_ERRM_TVALID_STABLE
  // =====
  property AXI4STREAM_ERRM_TVALID_STABLE;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & TVALID & !TREADY & !($isunknown({TVALID,TREADY}))
      ##1 `AXI4_SVA_RSTn
      |-> TVALID;
  endproperty
  axi4stream_errm_tvalid_stable: assert property (AXI4STREAM_ERRM_TVALID_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TVALID_STABLE);


  // INDEX:        - AXI4STREAM_RECS_TREADY_MAX_WAIT 
  // =====
  // Note: this rule does not error if VALID goes low (breaking VALID_STABLE rule)
  property   AXI4STREAM_RECS_TREADY_MAX_WAIT;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown({TVALID,TREADY})) &
      // Parameter that can disable all AXI4STREAM_REC*_* rules
      i_RecommendOn &  
      // Parameter that can disable just AXI4STREAM_REC*_MAX_WAIT rules
      i_RecMaxWaitOn & 
      ( TVALID & !TREADY)  // READY=1 within MAXWAITS cycles (or VALID=0)
      |-> ##[1:MAXWAITS] (!TVALID |  TREADY); 
  endproperty
  axi4stream_recs_tready_max_wait: assert property 
  (AXI4STREAM_RECS_TREADY_MAX_WAIT) else
   `ARM_AMBA4_PC_MSG_WARN(`RECS_TREADY_MAX_WAIT);


  // INDEX:        - AXI4STREAM_ERRM_TUSER_STABLE
  // =====
  property AXI4STREAM_ERRM_TUSER_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({TVALID,TREADY,TUSER})) &
      `AXI4_SVA_RSTn & TVALID & !TREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(TUSER);
  endproperty
  axi4stream_errm_tuser_stable: assert property (AXI4STREAM_ERRM_TUSER_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TUSER_STABLE);


  // INDEX:        - AXI4STREAM_ERRM_TKEEP_TSTRB
  // =====
  property AXI4STREAM_ERRM_TKEEP_TSTRB;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({TVALID,TKEEP,TSTRB})) &
      `AXI4_SVA_RSTn & TVALID
      |-> ~(|(~TKEEP & TSTRB));
  endproperty
  axi4stream_errm_tkeep_tstrb: assert property (AXI4STREAM_ERRM_TKEEP_TSTRB) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TKEEP_TSTRB);


  // INDEX:        - AXI4STREAM_ERRM_STREAM_ALL_DONE_EOS 
  // =====
  // EOS: End-Of-Simulation check (not suitable for formal proofs).
  // Use +define+AXI4STREAM_END_OF_SIMULATION=tb.EOS_signal when compiling.

`ifdef AXI4STREAM_END_OF_SIMULATION
  property AXI4STREAM_ERRM_STREAM_ALL_DONE_EOS;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(`AXI4STREAM_END_OF_SIMULATION)) &
      `AXI4_SVA_RSTn      
      ##1 `AXI4_SVA_RSTn & $rose(`AXI4STREAM_END_OF_SIMULATION)
      |-> (ActiveStreams() == 1'b0);
  endproperty
  axi4stream_errm_stream_all_done_eos: assert property 
  (AXI4STREAM_ERRM_STREAM_ALL_DONE_EOS) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_STREAM_ALL_DONE_EOS);
`endif


//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------

`ifdef AXI4STREAM_XCHECK_OFF
`else  // X-Checking on by default

  // INDEX:        - AXI4STREAM_ERRM_TID_X
  // =====
  property AXI4STREAM_ERRM_TID_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & TVALID
      |-> ! $isunknown(TID);
  endproperty
  axi4stream_errm_tid_x: assert property (AXI4STREAM_ERRM_TID_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TID_X);
 

  // INDEX:        - AXI4STREAM_ERRM_TDEST_X
  // =====
  property AXI4STREAM_ERRM_TDEST_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & TVALID
      |-> ! $isunknown(TDEST);
  endproperty
  axi4stream_errm_tdest_x: assert property (AXI4STREAM_ERRM_TDEST_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TDEST_X);


  // INDEX:        - AXI4STREAM_ERRM_TKEEP_X
  // =====
  property AXI4STREAM_ERRM_TKEEP_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & TVALID
      |-> ! $isunknown(TKEEP);
  endproperty
  axi4stream_errm_tkeep_x: assert property (AXI4STREAM_ERRM_TKEEP_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TKEEP_X);


  // INDEX:        - AXI4STREAM_ERRM_TDATA_X
  // =====
  property AXI4STREAM_ERRM_TDATA_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & TVALID & !($isunknown(TdataMask))
      |-> ! $isunknown(TDATA & TdataMask);
  endproperty
  axi4stream_errm_tdata_x: assert property (AXI4STREAM_ERRM_TDATA_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TDATA_X);


  // INDEX:        - AXI4STREAM_ERRM_TLAST_X
  // =====
  property AXI4STREAM_ERRM_TLAST_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & TVALID
      |-> ! $isunknown(TLAST);
  endproperty
  axi4stream_errm_tlast_x: assert property (AXI4STREAM_ERRM_TLAST_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TLAST_X);


  // INDEX:        - AXI4STREAM_ERRM_TSTRB_X
  // =====
  property AXI4STREAM_ERRM_TSTRB_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & TVALID
      |-> ! $isunknown(TSTRB);
  endproperty
  axi4stream_errm_tstrb_x: assert property (AXI4STREAM_ERRM_TSTRB_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TSTRB_X);


  // INDEX:        - AXI4STREAM_ERRM_TVALID_X
  // =====
  property AXI4STREAM_ERRM_TVALID_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(TVALID);
  endproperty
  axi4stream_errm_tvalid_x: assert property (AXI4STREAM_ERRM_TVALID_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TVALID_X);


  // INDEX:        - AXI4STREAM_ERRS_TREADY_X
  // =====
  property AXI4STREAM_ERRS_TREADY_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(TREADY);
  endproperty
  axi4stream_errs_tready_x: assert property (AXI4STREAM_ERRS_TREADY_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_TREADY_X);


  // INDEX:        - AXI4STREAM_ERRM_TUSER_X
  // =====
  property AXI4STREAM_ERRM_TUSER_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & TVALID
      |-> ! $isunknown(TUSER);
  endproperty
  axi4stream_errm_tuser_x: assert property (AXI4STREAM_ERRM_TUSER_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TUSER_X);

`endif // AXI4STREAM_XCHECK_OFF


//------------------------------------------------------------------------------
// INDEX:   4) Zero Width Stability Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4STREAM_ERRM_TDATA_TIEOFF
  // =====
  property AXI4STREAM_ERRM_TDATA_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(TDATA)) &
      `AXI4_SVA_RSTn &
      (DATA_WIDTH_BYTES == 0) 
      |-> $stable(TDATA);
  endproperty
  axi4stream_errm_tdata_tieoff: assert property (AXI4STREAM_ERRM_TDATA_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TDATA_TIEOFF);


  // INDEX:        - AXI4STREAM_ERRM_TKEEP_TIEOFF
  // =====
  property AXI4STREAM_ERRM_TKEEP_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(TKEEP)) &
      `AXI4_SVA_RSTn &
      (DATA_WIDTH_BYTES == 0) 
      |-> $stable(TKEEP);
  endproperty
  axi4stream_errm_tkeep_tieoff: assert property (AXI4STREAM_ERRM_TKEEP_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TKEEP_TIEOFF);

  
  // INDEX:        - AXI4STREAM_ERRM_TSTRB_TIEOFF
  // =====
  property AXI4STREAM_ERRM_TSTRB_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(TSTRB)) &
      `AXI4_SVA_RSTn &
      (DATA_WIDTH_BYTES == 0) 
      |-> $stable(TSTRB);
  endproperty
  axi4stream_errm_tstrb_tieoff: assert property (AXI4STREAM_ERRM_TSTRB_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TSTRB_TIEOFF);


  // INDEX:        - AXI4STREAM_ERRM_TID_TIEOFF
  // =====
  property AXI4STREAM_ERRM_TID_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(TID)) &
      `AXI4_SVA_RSTn &
      (ID_WIDTH == 0) 
      |-> $stable(TID);
  endproperty
  axi4stream_errm_tid_tieoff: assert property (AXI4STREAM_ERRM_TID_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TID_TIEOFF);


  // INDEX:        - AXI4STREAM_ERRM_TDEST_TIEOFF
  // =====
  property AXI4STREAM_ERRM_TDEST_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(TDEST)) &
      `AXI4_SVA_RSTn &
      (DEST_WIDTH == 0) 
      |-> $stable(TDEST);
  endproperty
  axi4stream_errm_tdest_tieoff: assert property (AXI4STREAM_ERRM_TDEST_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TDEST_TIEOFF);


  // INDEX:        - AXI4STREAM_ERRM_TUSER_TIEOFF
  // =====
  property AXI4STREAM_ERRM_TUSER_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(TUSER)) &
      `AXI4_SVA_RSTn &
      (USER_WIDTH == 0) 
      |-> $stable(TUSER);
  endproperty
  axi4stream_errm_tuser_tieoff: assert property (AXI4STREAM_ERRM_TUSER_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_TUSER_TIEOFF);

//------------------------------------------------------------------------------
// INDEX:   5) Auxiliary Logic Rules
//------------------------------------------------------------------------------

`ifdef AXI4STREAM_END_OF_SIMULATION
  // INDEX:        - AXI4STREAM_AUXM_TID_TDEST_WIDTH
  // =====
  property AXI4STREAM_AUXM_TID_TDEST_WIDTH;
    @(posedge `AXI4_SVA_CLK)
      (ID_WIDTH+DEST_WIDTH <= 24 );
  endproperty
  axi4stream_errm_tid_tdest_width: assert property (AXI4STREAM_AUXM_TID_TDEST_WIDTH) else
   `ARM_AMBA4_PC_MSG_ERR(`AUXM_TID_TDEST_WIDTH);
`endif

//------------------------------------------------------------------------------
// INDEX:
// INDEX: Auxiliary Logic
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Stream Tracking Logic and Functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:        a) StreamInUse array
//------------------------------------------------------------------------------

`ifdef AXI4STREAM_END_OF_SIMULATION
  always @(negedge `AXI4_AUX_RSTn or posedge `AXI4_AUX_CLK)
  begin
    if (!`AXI4_AUX_RSTn)
    begin
      for (int i = 0; i <= ID_VAL_MAX; i++)
        for (int j = 0; j <= DEST_VAL_MAX; j++)
          StreamInUse[i][j] = 1'b0;
    end
    else
    begin
      if (TVALID)
      begin
        if (TLAST & TREADY)
          StreamInUse[TID][TDEST] = 1'b0;
        else
          StreamInUse[TID][TDEST] = 1'b1;
      end // TVALID
    end
  end
  
//------------------------------------------------------------------------------
// INDEX:        b) ActiveStreams function
//------------------------------------------------------------------------------
  function logic ActiveStreams;
    ActiveStreams = 1'b0;
    for (int i = 0; i <= ID_VAL_MAX; i++)
      for (int j = 0; j <= DEST_VAL_MAX; j++)
        if (StreamInUse[i][j] == 1'b1)
          ActiveStreams = 1'b1;
  endfunction 
`endif

//------------------------------------------------------------------------------
// INDEX:   2) Combinatorial Logic
//------------------------------------------------------------------------------

//----------------------------------------------------------------------------
// INDEX:        a) Masks
//----------------------------------------------------------------------------

// INDEX:           - TdataMask
// =====
  always @(TSTRB)
  begin : p_TdataMaskComb
    integer i;  // data byte loop counter
    integer j;  // data bit loop counter

    for (i = 0; i < STRB_WIDTH; i = i + 1)
      for (j = i * 8; j <= (i * 8) + 7; j = j + 1)
        TdataMask[j] = TSTRB[i];
  end
//------------------------------------------------------------------------------
// INDEX:
// INDEX: End of File
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Clear Verilog Defines
//------------------------------------------------------------------------------

  // Error and Warning Messages
  `undef ARM_AMBA4_PC_MSG_ERR
  `undef ARM_AMBA4_PC_MSG_WARN

  // Clock and Reset
  `undef AXI4_AUX_CLK
  `undef AXI4_SVA_CLK
  `undef AXI4_AUX_RSTn
  `undef AXI4_SVA_RSTn  

  // Others
  `undef AXI4STREAM_END_OF_SIMULATION
  `undef AXI4STREAM_XCHECK_OFF

//------------------------------------------------------------------------------
// INDEX:   2) End of module
//------------------------------------------------------------------------------

`include "Axi4StreamPC_message_undefs.v"

endmodule // Axi4PC
`endif    // AXI4STREAMPC_OFF
