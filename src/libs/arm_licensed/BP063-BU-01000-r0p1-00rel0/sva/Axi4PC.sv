
//============================================================================
//  The confidential and proprietary information contained in this file may
//  only be used by a person authorised under and to the extent permitted
//  by a subsisting licensing agreement from ARM Limited.
//  
//                 (C) COPYRIGHT 2010-2012 ARM Limited.
//                        ALL RIGHTS RESERVED
// 
//  This entire notice must be reproduced on all copies of this file
//  and copies of this file may only be made by a person if such person is
//  permitted to do so under the terms of a subsisting license agreement
//  from ARM Limited.
//
//----------------------------------------------------------------------------
//  Version and Release Control Information:
//
//  File Revision       : 132591
//
//  Date                :  2012-06-27 11:24:12 +0100 (Wed, 27 Jun 2012)
//
//  Release Information : BP063-VL-70004-r0p1-00rel0
//
//----------------------------------------------------------------------------
//  Purpose             : These are the AXI4 SVA Protocol Assertions and
//                        supporting auxiliary code.
//                          
//                        Supports bus widths of 32, 64, 128, 256, 512, 1024 
//                        bit
//                        Supports a single outstanding exclusive read per ID
//============================================================================

//----------------------------------------------------------------------------
// CONTENTS
// ========
//  315.  Module: Axi4PC
//  388.    1) Parameters
//  391.         - Configurable (user can set)
//  438.         - Calculated (user should not override)
//  991.    2) Inputs (no outputs)
//  994.         - Global Signals
//  999.         - Write Address Channel
// 1015.         - Write Data Channel
// 1024.         - Write Response Channel
// 1032.         - Read Address Channel
// 1048.         - Read Data Channel
// 1058.         - Low Power Interface
// 1065.    3) Wire and Reg Declarations
// 1159.    4) Verilog Defines
// 1162.         - Clock and Reset
// 1194.    5) Initialize simulation
// 1199.         - Format for time reporting
// 1204.         - Indicate version and release state of Axi4PC
// 1209.         - Warn if any/some recommended rules are disabled
// 1221. 
// 1222.  AXI4 Rules: Write Address Channel (*_AW*)
// 1226.    1) Functional Rules
// 1229.         - AXI4_ERRM_AWADDR_BOUNDARY
// 1253.         - AXI4_ERRM_AWADDR_WRAP_ALIGN
// 1265.         - AXI4_ERRM_AWBURST
// 1277.         - AXI4_ERRM_AWLEN_LOCK
// 1289.         - AXI4_ERRM_AWCACHE
// 1301.         - AXI4_ERRM_AWLEN_FIXED
// 1313.         - AXI4_ERRM_AWLEN_WRAP
// 1328.         - AXI4_ERRM_AWSIZE
// 1342.         - AXI4_ERRM_AWVALID_RESET
// 1354.    2) Handshake Rules
// 1357.         - AXI4_ERRM_AWADDR_STABLE
// 1370.         - AXI4_ERRM_AWBURST_STABLE
// 1383.         - AXI4_ERRM_AWCACHE_STABLE
// 1396.         - AXI4_ERRM_AWID_STABLE
// 1409.         - AXI4_ERRM_AWLEN_STABLE
// 1422.         - AXI4_ERRM_AWLOCK_STABLE
// 1435.         - AXI4_ERRM_AWPROT_STABLE
// 1448.         - AXI4_ERRM_AWSIZE_STABLE
// 1461.         - AXI4_ERRM_AWQOS_STABLE
// 1474.         - AXI4_ERRM_AWREGION_STABLE
// 1487.         - AXI4_ERRM_AWVALID_STABLE
// 1499.         - AXI4_RECS_AWREADY_MAX_WAIT
// 1514.    3) X-Propagation Rules
// 1521.         - AXI4_ERRM_AWADDR_X
// 1532.         - AXI4_ERRM_AWBURST_X
// 1543.         - AXI4_ERRM_AWCACHE_X
// 1554.         - AXI4_ERRM_AWID_X
// 1565.         - AXI4_ERRM_AWLEN_X
// 1576.         - AXI4_ERRM_AWLOCK_X
// 1587.         - AXI4_ERRM_AWPROT_X
// 1598.         - AXI4_ERRM_AWSIZE_X
// 1609.         - AXI4_ERRM_AWQOS_X
// 1620.         - AXI4_ERRM_AWREGION_X
// 1631.         - AXI4_ERRM_AWVALID_X
// 1642.         - AXI4_ERRS_AWREADY_X
// 1655. 
// 1656.  AXI4 Rules: Write Data Channel (*_W*)
// 1660.    1) Functional Rules
// 1669.         - AXI4_ERRM_WDATA_NUM_PROP1
// 1680.         - AXI4_ERRM_WDATA_NUM_PROP2
// 1691.         - AXI4_ERRM_WDATA_NUM_PROP3
// 1702.         - AXI4_ERRM_WDATA_NUM_PROP4
// 1713.         - AXI4_ERRM_WDATA_NUM_PROP5
// 1724.         - AXI4_ERRM_WSTRB
// 1738.         - AXI4_ERRM_WVALID_RESET
// 1750.    2) Handshake Rules
// 1753.         - AXI4_ERRM_WDATA_STABLE
// 1766.         - AXI4_ERRM_WLAST_STABLE
// 1779.         - AXI4_ERRM_WSTRB_STABLE
// 1792.         - AXI4_ERRM_WVALID_STABLE
// 1804.         - AXI4_RECS_WREADY_MAX_WAIT 
// 1819.    3) X-Propagation Rules
// 1826.         - AXI4_ERRM_WDATA_X
// 1837.         - AXI4_ERRM_WLAST_X
// 1848.         - AXI4_ERRM_WSTRB_X
// 1859.         - AXI4_ERRM_WVALID_X
// 1870.         - AXI4_ERRS_WREADY_X
// 1884. 
// 1885.  AXI4 Rules: Write Response Channel (*_B*)
// 1889.    1) Functional Rules
// 1893.         - AXI4_ERRS_BRESP_WLAST
// 1907.         - AXI4_ERRS_BRESP_EXOKAY
// 1920.         - AXI4_ERRS_BVALID_RESET
// 1932.         - AXI4_ERRS_BRESP_AW 
// 1944.    2) Handshake Rules
// 1947.         - AXI4_ERRS_BID_STABLE
// 1960.         - AXI4_ERRS_BRESP_STABLE
// 1973.         - AXI4_ERRS_BVALID_STABLE
// 1985.         - AXI4_RECM_BREADY_MAX_WAIT 
// 2000.    3) X-Propagation Rules
// 2007.         - AXI4_ERRM_BREADY_X
// 2018.         - AXI4_ERRS_BID_X
// 2029.         - AXI4_ERRS_BRESP_X
// 2040.         - AXI4_ERRS_BVALID_X
// 2054. 
// 2055.  AXI4 Rules: Read Address Channel (*_AR*)
// 2059.    1) Functional Rules
// 2062.         - AXI4_ERRM_ARADDR_BOUNDARY
// 2086.         - AXI4_ERRM_ARADDR_WRAP_ALIGN
// 2098.         - AXI4_ERRM_ARBURST
// 2110.         - AXI4_ERRM_ARLEN_LOCK
// 2122.         - AXI4_ERRM_ARCACHE
// 2134.         - AXI4_ERRM_ARLEN_FIXED
// 2146.         - AXI4_ERRM_ARLEN_WRAP
// 2164.         - AXI4_ERRM_ARSIZE
// 2176.         - AXI4_ERRM_ARVALID_RESET
// 2188.    2) Handshake Rules
// 2191.         - AXI4_ERRM_ARADDR_STABLE
// 2204.         - AXI4_ERRM_ARBURST_STABLE
// 2217.         - AXI4_ERRM_ARCACHE_STABLE
// 2230.         - AXI4_ERRM_ARID_STABLE
// 2243.         - AXI4_ERRM_ARLEN_STABLE
// 2256.         - AXI4_ERRM_ARLOCK_STABLE
// 2269.         - AXI4_ERRM_ARPROT_STABLE
// 2282.         - AXI4_ERRM_ARSIZE_STABLE
// 2295.         - AXI4_ERRM_ARQOS_STABLE
// 2308.         - AXI4_ERRM_ARREGION_STABLE
// 2321.         - AXI4_ERRM_ARVALID_STABLE
// 2333.         - AXI4_RECS_ARREADY_MAX_WAIT 
// 2348.    3) X-Propagation Rules
// 2355.         - AXI4_ERRM_ARADDR_X
// 2366.         - AXI4_ERRM_ARBURST_X
// 2377.         - AXI4_ERRM_ARCACHE_X
// 2388.         - AXI4_ERRM_ARID_X
// 2399.         - AXI4_ERRM_ARLEN_X
// 2410.         - AXI4_ERRM_ARLOCK_X
// 2421.         - AXI4_ERRM_ARPROT_X
// 2432.         - AXI4_ERRM_ARSIZE_X
// 2443.         - AXI4_ERRM_ARQOS_X
// 2454.         - AXI4_ERRM_ARREGION_X
// 2465.         - AXI4_ERRM_ARVALID_X
// 2476.         - AXI4_ERRS_ARREADY_X
// 2489. 
// 2490.  AXI4 Rules: Read Data Channel (*_R*)
// 2494.    1) Functional Rules
// 2497.         - AXI4_ERRS_RDATA_NUM
// 2510.         - AXI4_ERRS_RID
// 2523.         - AXI4_ERRS_RRESP_EXOKAY
// 2535.         - AXI4_ERRS_RVALID_RESET
// 2547.    2) Handshake Rules
// 2550.         - AXI4_ERRS_RDATA_STABLE
// 2563.         - AXI4_ERRS_RID_STABLE
// 2576.         - AXI4_ERRS_RLAST_STABLE
// 2589.         - AXI4_ERRS_RRESP_STABLE
// 2602.         - AXI4_ERRS_RVALID_STABLE
// 2614.         - AXI4_RECM_RREADY_MAX_WAIT 
// 2629.    3) X-Propagation Rules
// 2636.         - AXI4_ERRS_RDATA_X
// 2647.         - AXI4_ERRM_RREADY_X
// 2658.         - AXI4_ERRS_RID_X
// 2669.         - AXI4_ERRS_RLAST_X
// 2680.         - AXI4_ERRS_RRESP_X
// 2691.         - AXI4_ERRS_RVALID_X
// 2704. 
// 2705.  AXI4 Rules: Low Power Interface (*_C*)
// 2709.    1) Functional Rules (none for Low Power signals)
// 2713.    2) Handshake Rules (asynchronous to ACLK)
// 2720.         - AXI4_ERRL_CSYSACK_FALL
// 2731.         - AXI4_ERRL_CSYSACK_RISE
// 2742.         - AXI4_ERRL_CSYSREQ_FALL
// 2753.         - AXI4_ERRL_CSYSREQ_RISE
// 2764.    3) X-Propagation Rules
// 2771.         - AXI4_ERRL_CACTIVE_X
// 2782.         - AXI4_ERRL_CSYSACK_X
// 2793.         - AXI4_ERRL_CSYSREQ_X
// 2806. 
// 2807.  AXI Rules: Exclusive Access
// 2814.    1) Functional Rules
// 2817.         - AXI4_ERRM_EXCL_ALIGN
// 2839.         - AXI4_ERRM_EXCL_LEN
// 2857.         - AXI4_RECM_EXCL_MATCH
// 2883.         - AXI4_ERRM_EXCL_MAX
// 2904.         - AXI4_RECM_EXCL_PAIR
// 2921.         - AXI4_RECM_EXCL_R_W
// 2936. 
// 2937.  AXI4 Rules: USER_* Rules (extension to AXI4)
// 2944.    1) Functional Rules (none for USER signals)
// 2948.    2) Handshake Rules
// 2951.         - AXI4_ERRM_AWUSER_STABLE
// 2964.         - AXI4_ERRM_WUSER_STABLE
// 2977.         - AXI4_ERRS_BUSER_STABLE
// 2990.         - AXI4_ERRM_ARUSER_STABLE
// 3003.         - AXI4_ERRS_RUSER_STABLE
// 3016.    3) X-Propagation Rules
// 3022.         - AXI4_ERRM_AWUSER_X
// 3033.         - AXI4_ERRM_WUSER_X
// 3044.         - AXI4_ERRS_BUSER_X
// 3055.         - AXI4_ERRM_ARUSER_X
// 3066.         - AXI4_ERRS_RUSER_X
// 3079.    4) Zero Width Stability Rules
// 3082.         - AXI4_ERRM_AWUSER_TIEOFF
// 3095.         - AXI4_ERRM_WUSER_TIEOFF
// 3108.         - AXI4_ERRS_BUSER_TIEOFF
// 3121.         - AXI4_ERRM_ARUSER_TIEOFF
// 3134.         - AXI4_ERRS_RUSER_TIEOFF
// 3147.         - AXI4_ERRM_AWID_TIEOFF
// 3160.         - AXI4_ERRS_BID_TIEOFF
// 3173.         - AXI4_ERRM_ARID_TIEOFF
// 3186.         - AXI4_ERRS_RID_TIEOFF
// 3199.    5) EOS checks
// 3206.         - AXI4_ERRS_BRESP_ALL_DONE_EOS
// 3214.         - AXI4_ERRS_RLAST_ALL_DONE_EOS
// 3227. 
// 3228.  Auxiliary Logic
// 3232.    1) Rules for Auxiliary Logic
// 3236.       a) Master (AUX*)
// 3239.         - AXI4_AUX_DATA_WIDTH
// 3254.         - AXI4_AUX_ADDR_WIDTH
// 3264.         - AXI4_AUX_EXMON_WIDTH
// 3274.         - AXI4_AUX_MAXRBURSTS
// 3284.         - AXI4_AUX_MAXWBURSTS
// 3294.         - AXI4_AUX_RCAM_OVERFLOW
// 3305.         - AXI4_AUX_RCAM_UNDERFLOW
// 3316.         - AXI4_AUX_WCAM_OVERFLOW
// 3327.         - AXI4_AUX_WCAM_UNDERFLOW
// 3338.         - AXI4_AUX_EXCL_OVERFLOW
// 3349.    2) Combinatorial Logic
// 3353.       a) Masks
// 3356.            - AlignMaskR
// 3378.            - AlignMaskW
// 3400.            - ExclMask
// 3408.            - WdataMask
// 3421.            - RdataMask
// 3427.       b) Increments
// 3430.            - ArAddrIncr
// 3438.            - AwAddrIncr
// 3447.       c) Conversions
// 3450.            - ArLenInBytes
// 3459.            - ArSizeInBits
// 3467.            - AwSizeInBits
// 3476.       d) Other
// 3479.            - ArExclPending
// 3485.            - ArLenPending
// 3490.            - ArCountPending
// 3496.    3) EXCL Accesses
// 3499.         - Exclusive Access ID Lookup
// 3627.         - Exclusive Access Storage
// 3688.    4) Content addressable memories (CAMs)
// 3691.         - Read CAMSs (CAM+Shift)
// 3931.         - Write CAMs (CAM+Shift)
// 4326.    5) Verilog Functions
// 4328.         - function integer clogb2 (input integer n)
// 4339.         - CheckBurst
// 4679.         - CheckStrb
// 4717.         - ReadDataMask
// 4737.         - ByteShift
// 4832.         - ByteCount
// 4880.  End of File
// 4883.    1) Clear Verilog Defines
// 4897.    2) End of module
//----------------------------------------------------------------------------


//------------------------------------------------------------------------------
// AXI4 definitions
//------------------------------------------------------------------------------

`ifndef AXI4PC_OFF


`ifndef AXI4PC_TYPES
  `include "Axi4PC_defs.v"
`endif

`ifndef AXI4PC_MESSAGES
  `include "Axi4PC_message_defs.v"
`endif

`ifndef ARM_AMBA4_PC_MSG_ERR
  `define ARM_AMBA4_PC_MSG_ERR $error
`endif

`ifndef ARM_AMBA4_PC_MSG_WARN
  `define ARM_AMBA4_PC_MSG_WARN $warning
`endif

//------------------------------------------------------------------------------
// INDEX: Module: Axi4PC
//------------------------------------------------------------------------------

`ifndef AXI4PC

module Axi4PC 
  (
   // Global Signals
   ACLK,
   ARESETn,

   // Write Address Channel
   AWID,
   AWADDR,
   AWLEN,
   AWSIZE,
   AWBURST,
   AWLOCK,
   AWCACHE,
   AWPROT,
   AWQOS,
   AWREGION,
   AWUSER,
   AWVALID,
   AWREADY,

   // Write Channel
   WLAST,
   WDATA,
   WSTRB,
   WUSER,
   WVALID,
   WREADY,

   // Write Response Channel
   BID,
   BRESP,
   BUSER,
   BVALID,
   BREADY,

   // Read Address Channel
   ARID,
   ARADDR,
   ARLEN,
   ARSIZE,
   ARBURST,
   ARLOCK,
   ARCACHE,
   ARPROT,
   ARQOS,
   ARREGION,
   ARUSER,
   ARVALID,
   ARREADY,

   // Read Channel
   RID,
   RLAST,
   RDATA,
   RRESP,
   RUSER,
   RVALID,
   RREADY,

   // Low power interface
   CACTIVE,
   CSYSREQ,
   CSYSACK
   );

  `define AXI4PC
//------------------------------------------------------------------------------
// INDEX:   1) Parameters
//------------------------------------------------------------------------------

  // INDEX:        - Configurable (user can set)
  // =====
  // Parameters below can be set by the user.

  // Set DATA_WIDTH to the data-bus width required
  parameter DATA_WIDTH = 64;         // data bus width, default = 64-bit

  // Select the number of channel ID bits required
  parameter WID_WIDTH = 4;            // (A|W|R|B)ID width
  parameter RID_WIDTH = 4;            // (A|W|R|B)ID width

  // Select the size of the USER buses, default = 32-bit
  parameter AWUSER_WIDTH = 32;       // width of the user AW sideband field
  parameter WUSER_WIDTH  = 32;       // width of the user W  sideband field
  parameter BUSER_WIDTH  = 32;       // width of the user B  sideband field
  parameter ARUSER_WIDTH = 32;       // width of the user AR sideband field
  parameter RUSER_WIDTH  = 32;       // width of the user R  sideband field

  // Size of CAMs for storing outstanding read bursts, this should match or
  // exceed the number of outstanding read addresses accepted into the slave
  // interface
  parameter MAXRBURSTS = 16;

  // Size of CAMs for storing outstanding write bursts, this should match or
  // exceed the number of outstanding write bursts into the slave  interface
  parameter MAXWBURSTS = 16;

  // Maximum number of cycles between VALID -> READY high before a warning is
  // generated
  parameter MAXWAITS = 16;

  // Recommended Rules Enable
  // enable/disable reporting of all  AXI4_REC*_* rules
  parameter RecommendOn   = 1'b1;   
  // enable/disable reporting of just AXI4_REC*_MAX_WAIT rules
  parameter RecMaxWaitOn  = 1'b1;   


  // Set the protocol - used to disable some AXI4 checks for ACE
  parameter PROTOCOL = `AXI4PC_AMBA_AXI4;

  // Set ADDR_WIDTH to the address-bus width required
  parameter ADDR_WIDTH = 32;        // address bus width, default = 32-bit

  // Set EXMON_WIDTH to the exclusive access monitor width required
  parameter EXMON_WIDTH = 4;        // exclusive access width, default = 4-bit

  // INDEX:        - Calculated (user should not override)
  // =====
  // Do not override the following parameters: they must be calculated exactly
  // as shown below
  localparam DATA_MAX   = DATA_WIDTH-1;              // data max index
  localparam ADDR_MAX   = ADDR_WIDTH-1;              // address max index
  localparam STRB_WIDTH = DATA_WIDTH/8;              // WSTRB width
  localparam STRB_MAX   = STRB_WIDTH-1;              // WSTRB max index
  localparam STRB_1     = {{STRB_MAX{1'b0}}, 1'b1};  // value 1 in strobe width
  localparam ID_MAX_R   = RID_WIDTH? RID_WIDTH-1:0;    // ID max index
  localparam ID_MAX_W   = WID_WIDTH? WID_WIDTH-1:0;    // ID max index
  localparam ID_MAX     = ID_MAX_W > ID_MAX_R ? ID_MAX_W : ID_MAX_R;    // ID max index
  localparam EXMON_MAX  = EXMON_WIDTH-1;             // EXMON max index
  localparam EXMON_HI   = {EXMON_WIDTH{1'b1}};       // EXMON max value

  localparam AWUSER_MAX = AWUSER_WIDTH ? AWUSER_WIDTH-1:0; // AWUSER max index
  localparam WUSER_MAX  = WUSER_WIDTH ? WUSER_WIDTH-1:0;   // WUSER  max index
  localparam BUSER_MAX  = BUSER_WIDTH ? BUSER_WIDTH-1:0;   // BUSER  max index
  localparam ARUSER_MAX = ARUSER_WIDTH ? ARUSER_WIDTH-1:0; // ARUSER max index
  localparam RUSER_MAX  = RUSER_WIDTH ? RUSER_WIDTH-1:0;   // RUSER  max index


  // FLAG LO/HI STRB256..STRB1 ID BURST ASIZE ALEN EXCL ADDR[6:0]
  localparam ADDRLO   = 0;                 // ADDRLO   =   0
  localparam ADDRHI   = 6;                 // ADDRHI   =   6
  localparam EXCL     = ADDRHI + 1;        // Transaction is exclusive 7
  localparam ALENLO   = EXCL + 1;          // ALENLO   =   8
  localparam ALENHI   = ALENLO + 7;        // ALENHI   =  15
  localparam ASIZELO  = ALENHI + 1;        // ASIZELO  =  16
  localparam ASIZEHI  = ASIZELO + 2;       // ASIZEHI  =  18
  localparam BURSTLO  = ASIZEHI + 1;       // BURSTLO  =  19
  localparam BURSTHI  = BURSTLO + 1;       // BURSTHI  =  20
  localparam IDLO     = BURSTHI + 1;       // IDLO     =  21
  localparam IDHI     = IDLO+ID_MAX;       
  localparam STRB1LO  = IDHI +1;        
  localparam STRB1HI  = STRB1LO+STRB_MAX;  
  localparam STRB2LO  = STRB1HI+1;         
  localparam STRB2HI  = STRB2LO+STRB_MAX;  
  localparam STRB3LO  = STRB2HI+1;         
  localparam STRB3HI  = STRB3LO+STRB_MAX;  
  localparam STRB4LO  = STRB3HI+1;         
  localparam STRB4HI  = STRB4LO+STRB_MAX;  
  localparam STRB5LO  = STRB4HI+1;         
  localparam STRB5HI  = STRB5LO+STRB_MAX;  
  localparam STRB6LO  = STRB5HI+1;         
  localparam STRB6HI  = STRB6LO+STRB_MAX;  
  localparam STRB7LO  = STRB6HI+1;         
  localparam STRB7HI  = STRB7LO+STRB_MAX;  
  localparam STRB8LO  = STRB7HI+1;         
  localparam STRB8HI  = STRB8LO+STRB_MAX;  
  localparam STRB9LO  = STRB8HI+1;         
  localparam STRB9HI  = STRB9LO+STRB_MAX;  
  localparam STRB10LO = STRB9HI+1;         
  localparam STRB10HI = STRB10LO+STRB_MAX; 
  localparam STRB11LO = STRB10HI+1;        
  localparam STRB11HI = STRB11LO+STRB_MAX; 
  localparam STRB12LO = STRB11HI+1;        
  localparam STRB12HI = STRB12LO+STRB_MAX; 
  localparam STRB13LO = STRB12HI+1;        
  localparam STRB13HI = STRB13LO+STRB_MAX; 
  localparam STRB14LO = STRB13HI+1;        
  localparam STRB14HI = STRB14LO+STRB_MAX; 
  localparam STRB15LO = STRB14HI+1;        
  localparam STRB15HI = STRB15LO+STRB_MAX; 
  localparam STRB16LO = STRB15HI+1;        
  localparam STRB16HI = STRB16LO+STRB_MAX; 
  localparam STRB17LO =  STRB16HI+1;        
  localparam STRB17HI =  STRB17LO+STRB_MAX; 
  localparam STRB18LO =  STRB17HI+1;        
  localparam STRB18HI =  STRB18LO+STRB_MAX; 
  localparam STRB19LO =  STRB18HI+1;        
  localparam STRB19HI =  STRB19LO+STRB_MAX; 
  localparam STRB20LO =  STRB19HI+1;        
  localparam STRB20HI =  STRB20LO+STRB_MAX; 
  localparam STRB21LO =  STRB20HI+1;        
  localparam STRB21HI =  STRB21LO+STRB_MAX; 
  localparam STRB22LO =  STRB21HI+1;        
  localparam STRB22HI =  STRB22LO+STRB_MAX; 
  localparam STRB23LO =  STRB22HI+1;        
  localparam STRB23HI =  STRB23LO+STRB_MAX; 
  localparam STRB24LO =  STRB23HI+1;        
  localparam STRB24HI =  STRB24LO+STRB_MAX; 
  localparam STRB25LO =  STRB24HI+1;        
  localparam STRB25HI =  STRB25LO+STRB_MAX; 
  localparam STRB26LO =  STRB25HI+1;        
  localparam STRB26HI =  STRB26LO+STRB_MAX;
  localparam STRB27LO =  STRB26HI+1;        
  localparam STRB27HI =  STRB27LO+STRB_MAX; 
  localparam STRB28LO =  STRB27HI+1;        
  localparam STRB28HI =  STRB28LO+STRB_MAX; 
  localparam STRB29LO =  STRB28HI+1;        
  localparam STRB29HI =  STRB29LO+STRB_MAX; 
  localparam STRB30LO =  STRB29HI+1;        
  localparam STRB30HI =  STRB30LO+STRB_MAX; 
  localparam STRB31LO =  STRB30HI+1;        
  localparam STRB31HI =  STRB31LO+STRB_MAX; 
  localparam STRB32LO =  STRB31HI+1;        
  localparam STRB32HI =  STRB32LO+STRB_MAX; 
  localparam STRB33LO =  STRB32HI+1;        
  localparam STRB33HI =  STRB33LO+STRB_MAX; 
  localparam STRB34LO =  STRB33HI+1;        
  localparam STRB34HI =  STRB34LO+STRB_MAX; 
  localparam STRB35LO =  STRB34HI+1;        
  localparam STRB35HI =  STRB35LO+STRB_MAX; 
  localparam STRB36LO =  STRB35HI+1;        
  localparam STRB36HI =  STRB36LO+STRB_MAX; 
  localparam STRB37LO =  STRB36HI+1;        
  localparam STRB37HI =  STRB37LO+STRB_MAX; 
  localparam STRB38LO =  STRB37HI+1;        
  localparam STRB38HI =  STRB38LO+STRB_MAX; 
  localparam STRB39LO =  STRB38HI+1;        
  localparam STRB39HI =  STRB39LO+STRB_MAX; 
  localparam STRB40LO =  STRB39HI+1;        
  localparam STRB40HI =  STRB40LO+STRB_MAX; 
  localparam STRB41LO =  STRB40HI+1;        
  localparam STRB41HI =  STRB41LO+STRB_MAX; 
  localparam STRB42LO =  STRB41HI+1;        
  localparam STRB42HI =  STRB42LO+STRB_MAX; 
  localparam STRB43LO =  STRB42HI+1;        
  localparam STRB43HI =  STRB43LO+STRB_MAX; 
  localparam STRB44LO =  STRB43HI+1;        
  localparam STRB44HI =  STRB44LO+STRB_MAX; 
  localparam STRB45LO =  STRB44HI+1;        
  localparam STRB45HI =  STRB45LO+STRB_MAX; 
  localparam STRB46LO =  STRB45HI+1;        
  localparam STRB46HI =  STRB46LO+STRB_MAX; 
  localparam STRB47LO =  STRB46HI+1;        
  localparam STRB47HI =  STRB47LO+STRB_MAX; 
  localparam STRB48LO =  STRB47HI+1;        
  localparam STRB48HI =  STRB48LO+STRB_MAX; 
  localparam STRB49LO =  STRB48HI+1;        
  localparam STRB49HI =  STRB49LO+STRB_MAX; 
  localparam STRB50LO =  STRB49HI+1;        
  localparam STRB50HI =  STRB50LO+STRB_MAX; 
  localparam STRB51LO =  STRB50HI+1;        
  localparam STRB51HI =  STRB51LO+STRB_MAX; 
  localparam STRB52LO =  STRB51HI+1;        
  localparam STRB52HI =  STRB52LO+STRB_MAX; 
  localparam STRB53LO =  STRB52HI+1;        
  localparam STRB53HI =  STRB53LO+STRB_MAX; 
  localparam STRB54LO =  STRB53HI+1;        
  localparam STRB54HI =  STRB54LO+STRB_MAX; 
  localparam STRB55LO =  STRB54HI+1;        
  localparam STRB55HI =  STRB55LO+STRB_MAX; 
  localparam STRB56LO =  STRB55HI+1;        
  localparam STRB56HI =  STRB56LO+STRB_MAX; 
  localparam STRB57LO =  STRB56HI+1;        
  localparam STRB57HI =  STRB57LO+STRB_MAX; 
  localparam STRB58LO =  STRB57HI+1;        
  localparam STRB58HI =  STRB58LO+STRB_MAX; 
  localparam STRB59LO =  STRB58HI+1;        
  localparam STRB59HI =  STRB59LO+STRB_MAX; 
  localparam STRB60LO =  STRB59HI+1;        
  localparam STRB60HI =  STRB60LO+STRB_MAX; 
  localparam STRB61LO =  STRB60HI+1;        
  localparam STRB61HI =  STRB61LO+STRB_MAX; 
  localparam STRB62LO =  STRB61HI+1;        
  localparam STRB62HI =  STRB62LO+STRB_MAX; 
  localparam STRB63LO =  STRB62HI+1;        
  localparam STRB63HI =  STRB63LO+STRB_MAX; 
  localparam STRB64LO =  STRB63HI+1;        
  localparam STRB64HI =  STRB64LO+STRB_MAX; 
  localparam STRB65LO =  STRB64HI+1;        
  localparam STRB65HI =  STRB65LO+STRB_MAX; 
  localparam STRB66LO =  STRB65HI+1;        
  localparam STRB66HI =  STRB66LO+STRB_MAX; 
  localparam STRB67LO =  STRB66HI+1;        
  localparam STRB67HI =  STRB67LO+STRB_MAX; 
  localparam STRB68LO =  STRB67HI+1;        
  localparam STRB68HI =  STRB68LO+STRB_MAX; 
  localparam STRB69LO =  STRB68HI+1;        
  localparam STRB69HI =  STRB69LO+STRB_MAX; 
  localparam STRB70LO =  STRB69HI+1;        
  localparam STRB70HI =  STRB70LO+STRB_MAX; 
  localparam STRB71LO =  STRB70HI+1;        
  localparam STRB71HI =  STRB71LO+STRB_MAX; 
  localparam STRB72LO =  STRB71HI+1;        
  localparam STRB72HI =  STRB72LO+STRB_MAX; 
  localparam STRB73LO =  STRB72HI+1;        
  localparam STRB73HI =  STRB73LO+STRB_MAX; 
  localparam STRB74LO =  STRB73HI+1;        
  localparam STRB74HI =  STRB74LO+STRB_MAX; 
  localparam STRB75LO =  STRB74HI+1;        
  localparam STRB75HI =  STRB75LO+STRB_MAX; 
  localparam STRB76LO =  STRB75HI+1;        
  localparam STRB76HI =  STRB76LO+STRB_MAX; 
  localparam STRB77LO =  STRB76HI+1;        
  localparam STRB77HI =  STRB77LO+STRB_MAX; 
  localparam STRB78LO =  STRB77HI+1;        
  localparam STRB78HI =  STRB78LO+STRB_MAX; 
  localparam STRB79LO =  STRB78HI+1;        
  localparam STRB79HI =  STRB79LO+STRB_MAX; 
  localparam STRB80LO =  STRB79HI+1;        
  localparam STRB80HI =  STRB80LO+STRB_MAX; 
  localparam STRB81LO =  STRB80HI+1;        
  localparam STRB81HI =  STRB81LO+STRB_MAX; 
  localparam STRB82LO =  STRB81HI+1;        
  localparam STRB82HI =  STRB82LO+STRB_MAX; 
  localparam STRB83LO =  STRB82HI+1;        
  localparam STRB83HI =  STRB83LO+STRB_MAX; 
  localparam STRB84LO =  STRB83HI+1;        
  localparam STRB84HI =  STRB84LO+STRB_MAX; 
  localparam STRB85LO =  STRB84HI+1;        
  localparam STRB85HI =  STRB85LO+STRB_MAX; 
  localparam STRB86LO =  STRB85HI+1;        
  localparam STRB86HI =  STRB86LO+STRB_MAX; 
  localparam STRB87LO =  STRB86HI+1;        
  localparam STRB87HI =  STRB87LO+STRB_MAX; 
  localparam STRB88LO =  STRB87HI+1;        
  localparam STRB88HI =  STRB88LO+STRB_MAX; 
  localparam STRB89LO =  STRB88HI+1;        
  localparam STRB89HI =  STRB89LO+STRB_MAX; 
  localparam STRB90LO =  STRB89HI+1;        
  localparam STRB90HI =  STRB90LO+STRB_MAX; 
  localparam STRB91LO =  STRB90HI+1;        
  localparam STRB91HI =  STRB91LO+STRB_MAX; 
  localparam STRB92LO =  STRB91HI+1;        
  localparam STRB92HI =  STRB92LO+STRB_MAX; 
  localparam STRB93LO =  STRB92HI+1;        
  localparam STRB93HI =  STRB93LO+STRB_MAX; 
  localparam STRB94LO =  STRB93HI+1;        
  localparam STRB94HI =  STRB94LO+STRB_MAX; 
  localparam STRB95LO =  STRB94HI+1;        
  localparam STRB95HI =  STRB95LO+STRB_MAX; 
  localparam STRB96LO =  STRB95HI+1;        
  localparam STRB96HI =  STRB96LO+STRB_MAX; 
  localparam STRB97LO =  STRB96HI+1;        
  localparam STRB97HI =  STRB97LO+STRB_MAX; 
  localparam STRB98LO =  STRB97HI+1;        
  localparam STRB98HI =  STRB98LO+STRB_MAX; 
  localparam STRB99LO =  STRB98HI+1;        
  localparam STRB99HI =  STRB99LO+STRB_MAX; 
  localparam STRB100LO = STRB99HI+1;        
  localparam STRB100HI = STRB100LO+STRB_MAX;
  localparam STRB101LO = STRB100HI+1;       
  localparam STRB101HI = STRB101LO+STRB_MAX;
  localparam STRB102LO = STRB101HI+1;       
  localparam STRB102HI = STRB102LO+STRB_MAX;
  localparam STRB103LO = STRB102HI+1;       
  localparam STRB103HI = STRB103LO+STRB_MAX;
  localparam STRB104LO = STRB103HI+1;       
  localparam STRB104HI = STRB104LO+STRB_MAX;
  localparam STRB105LO = STRB104HI+1;       
  localparam STRB105HI = STRB105LO+STRB_MAX;
  localparam STRB106LO = STRB105HI+1;       
  localparam STRB106HI = STRB106LO+STRB_MAX;
  localparam STRB107LO = STRB106HI+1;       
  localparam STRB107HI = STRB107LO+STRB_MAX;
  localparam STRB108LO = STRB107HI+1;       
  localparam STRB108HI = STRB108LO+STRB_MAX;
  localparam STRB109LO = STRB108HI+1;       
  localparam STRB109HI = STRB109LO+STRB_MAX;
  localparam STRB110LO = STRB109HI+1;       
  localparam STRB110HI = STRB110LO+STRB_MAX;
  localparam STRB111LO = STRB110HI+1;       
  localparam STRB111HI = STRB111LO+STRB_MAX;
  localparam STRB112LO = STRB111HI+1;       
  localparam STRB112HI = STRB112LO+STRB_MAX;
  localparam STRB113LO = STRB112HI+1;       
  localparam STRB113HI = STRB113LO+STRB_MAX;
  localparam STRB114LO = STRB113HI+1;       
  localparam STRB114HI = STRB114LO+STRB_MAX;
  localparam STRB115LO = STRB114HI+1;       
  localparam STRB115HI = STRB115LO+STRB_MAX;
  localparam STRB116LO = STRB115HI+1;       
  localparam STRB116HI = STRB116LO+STRB_MAX;
  localparam STRB117LO = STRB116HI+1;       
  localparam STRB117HI = STRB117LO+STRB_MAX;
  localparam STRB118LO = STRB117HI+1;       
  localparam STRB118HI = STRB118LO+STRB_MAX;
  localparam STRB119LO = STRB118HI+1;       
  localparam STRB119HI = STRB119LO+STRB_MAX;
  localparam STRB120LO = STRB119HI+1;       
  localparam STRB120HI = STRB120LO+STRB_MAX;
  localparam STRB121LO = STRB120HI+1;       
  localparam STRB121HI = STRB121LO+STRB_MAX;
  localparam STRB122LO = STRB121HI+1;       
  localparam STRB122HI = STRB122LO+STRB_MAX;
  localparam STRB123LO = STRB122HI+1;       
  localparam STRB123HI = STRB123LO+STRB_MAX;
  localparam STRB124LO = STRB123HI+1;       
  localparam STRB124HI = STRB124LO+STRB_MAX;
  localparam STRB125LO = STRB124HI+1;       
  localparam STRB125HI = STRB125LO+STRB_MAX;
  localparam STRB126LO = STRB125HI+1;       
  localparam STRB126HI = STRB126LO+STRB_MAX;
  localparam STRB127LO = STRB126HI+1;       
  localparam STRB127HI = STRB127LO+STRB_MAX;
  localparam STRB128LO = STRB127HI+1;       
  localparam STRB128HI = STRB128LO+STRB_MAX;
  localparam STRB129LO = STRB128HI+1;       
  localparam STRB129HI = STRB129LO+STRB_MAX;
  localparam STRB130LO = STRB129HI+1;       
  localparam STRB130HI = STRB130LO+STRB_MAX;
  localparam STRB131LO = STRB130HI+1;       
  localparam STRB131HI = STRB131LO+STRB_MAX;
  localparam STRB132LO = STRB131HI+1;       
  localparam STRB132HI = STRB132LO+STRB_MAX;
  localparam STRB133LO = STRB132HI+1;       
  localparam STRB133HI = STRB133LO+STRB_MAX;
  localparam STRB134LO = STRB133HI+1;       
  localparam STRB134HI = STRB134LO+STRB_MAX;
  localparam STRB135LO = STRB134HI+1;       
  localparam STRB135HI = STRB135LO+STRB_MAX;
  localparam STRB136LO = STRB135HI+1;       
  localparam STRB136HI = STRB136LO+STRB_MAX;
  localparam STRB137LO = STRB136HI+1;       
  localparam STRB137HI = STRB137LO+STRB_MAX;
  localparam STRB138LO = STRB137HI+1;       
  localparam STRB138HI = STRB138LO+STRB_MAX;
  localparam STRB139LO = STRB138HI+1;       
  localparam STRB139HI = STRB139LO+STRB_MAX;
  localparam STRB140LO = STRB139HI+1;       
  localparam STRB140HI = STRB140LO+STRB_MAX;
  localparam STRB141LO = STRB140HI+1;       
  localparam STRB141HI = STRB141LO+STRB_MAX;
  localparam STRB142LO = STRB141HI+1;       
  localparam STRB142HI = STRB142LO+STRB_MAX;
  localparam STRB143LO = STRB142HI+1;       
  localparam STRB143HI = STRB143LO+STRB_MAX;
  localparam STRB144LO = STRB143HI+1;       
  localparam STRB144HI = STRB144LO+STRB_MAX;
  localparam STRB145LO = STRB144HI+1;       
  localparam STRB145HI = STRB145LO+STRB_MAX;
  localparam STRB146LO = STRB145HI+1;       
  localparam STRB146HI = STRB146LO+STRB_MAX;
  localparam STRB147LO = STRB146HI+1;       
  localparam STRB147HI = STRB147LO+STRB_MAX;
  localparam STRB148LO = STRB147HI+1;       
  localparam STRB148HI = STRB148LO+STRB_MAX;
  localparam STRB149LO = STRB148HI+1;       
  localparam STRB149HI = STRB149LO+STRB_MAX;
  localparam STRB150LO = STRB149HI+1;       
  localparam STRB150HI = STRB150LO+STRB_MAX;
  localparam STRB151LO = STRB150HI+1;       
  localparam STRB151HI = STRB151LO+STRB_MAX;
  localparam STRB152LO = STRB151HI+1;       
  localparam STRB152HI = STRB152LO+STRB_MAX;
  localparam STRB153LO = STRB152HI+1;       
  localparam STRB153HI = STRB153LO+STRB_MAX;
  localparam STRB154LO = STRB153HI+1;       
  localparam STRB154HI = STRB154LO+STRB_MAX;
  localparam STRB155LO = STRB154HI+1;       
  localparam STRB155HI = STRB155LO+STRB_MAX;
  localparam STRB156LO = STRB155HI+1;       
  localparam STRB156HI = STRB156LO+STRB_MAX;
  localparam STRB157LO = STRB156HI+1;       
  localparam STRB157HI = STRB157LO+STRB_MAX;
  localparam STRB158LO = STRB157HI+1;       
  localparam STRB158HI = STRB158LO+STRB_MAX;
  localparam STRB159LO = STRB158HI+1;       
  localparam STRB159HI = STRB159LO+STRB_MAX;
  localparam STRB160LO = STRB159HI+1;       
  localparam STRB160HI = STRB160LO+STRB_MAX;
  localparam STRB161LO = STRB160HI+1;       
  localparam STRB161HI = STRB161LO+STRB_MAX;
  localparam STRB162LO = STRB161HI+1;       
  localparam STRB162HI = STRB162LO+STRB_MAX;
  localparam STRB163LO = STRB162HI+1;       
  localparam STRB163HI = STRB163LO+STRB_MAX;
  localparam STRB164LO = STRB163HI+1;       
  localparam STRB164HI = STRB164LO+STRB_MAX;
  localparam STRB165LO = STRB164HI+1;       
  localparam STRB165HI = STRB165LO+STRB_MAX;
  localparam STRB166LO = STRB165HI+1;       
  localparam STRB166HI = STRB166LO+STRB_MAX;
  localparam STRB167LO = STRB166HI+1;       
  localparam STRB167HI = STRB167LO+STRB_MAX;
  localparam STRB168LO = STRB167HI+1;       
  localparam STRB168HI = STRB168LO+STRB_MAX;
  localparam STRB169LO = STRB168HI+1;       
  localparam STRB169HI = STRB169LO+STRB_MAX;
  localparam STRB170LO = STRB169HI+1;       
  localparam STRB170HI = STRB170LO+STRB_MAX;
  localparam STRB171LO = STRB170HI+1;       
  localparam STRB171HI = STRB171LO+STRB_MAX;
  localparam STRB172LO = STRB171HI+1;       
  localparam STRB172HI = STRB172LO+STRB_MAX;
  localparam STRB173LO = STRB172HI+1;       
  localparam STRB173HI = STRB173LO+STRB_MAX;
  localparam STRB174LO = STRB173HI+1;       
  localparam STRB174HI = STRB174LO+STRB_MAX;
  localparam STRB175LO = STRB174HI+1;       
  localparam STRB175HI = STRB175LO+STRB_MAX;
  localparam STRB176LO = STRB175HI+1;       
  localparam STRB176HI = STRB176LO+STRB_MAX;
  localparam STRB177LO = STRB176HI+1;       
  localparam STRB177HI = STRB177LO+STRB_MAX;
  localparam STRB178LO = STRB177HI+1;       
  localparam STRB178HI = STRB178LO+STRB_MAX;
  localparam STRB179LO = STRB178HI+1;       
  localparam STRB179HI = STRB179LO+STRB_MAX;
  localparam STRB180LO = STRB179HI+1;       
  localparam STRB180HI = STRB180LO+STRB_MAX;
  localparam STRB181LO = STRB180HI+1;       
  localparam STRB181HI = STRB181LO+STRB_MAX;
  localparam STRB182LO = STRB181HI+1;       
  localparam STRB182HI = STRB182LO+STRB_MAX;
  localparam STRB183LO = STRB182HI+1;       
  localparam STRB183HI = STRB183LO+STRB_MAX;
  localparam STRB184LO = STRB183HI+1;       
  localparam STRB184HI = STRB184LO+STRB_MAX;
  localparam STRB185LO = STRB184HI+1;       
  localparam STRB185HI = STRB185LO+STRB_MAX;
  localparam STRB186LO = STRB185HI+1;       
  localparam STRB186HI = STRB186LO+STRB_MAX;
  localparam STRB187LO = STRB186HI+1;       
  localparam STRB187HI = STRB187LO+STRB_MAX;
  localparam STRB188LO = STRB187HI+1;       
  localparam STRB188HI = STRB188LO+STRB_MAX;
  localparam STRB189LO = STRB188HI+1;       
  localparam STRB189HI = STRB189LO+STRB_MAX;
  localparam STRB190LO = STRB189HI+1;       
  localparam STRB190HI = STRB190LO+STRB_MAX;
  localparam STRB191LO = STRB190HI+1;       
  localparam STRB191HI = STRB191LO+STRB_MAX;
  localparam STRB192LO = STRB191HI+1;       
  localparam STRB192HI = STRB192LO+STRB_MAX;
  localparam STRB193LO = STRB192HI+1;       
  localparam STRB193HI = STRB193LO+STRB_MAX;
  localparam STRB194LO = STRB193HI+1;       
  localparam STRB194HI = STRB194LO+STRB_MAX;
  localparam STRB195LO = STRB194HI+1;       
  localparam STRB195HI = STRB195LO+STRB_MAX;
  localparam STRB196LO = STRB195HI+1;       
  localparam STRB196HI = STRB196LO+STRB_MAX;
  localparam STRB197LO = STRB196HI+1;       
  localparam STRB197HI = STRB197LO+STRB_MAX;
  localparam STRB198LO = STRB197HI+1;       
  localparam STRB198HI = STRB198LO+STRB_MAX;
  localparam STRB199LO = STRB198HI+1;       
  localparam STRB199HI = STRB199LO+STRB_MAX;
  localparam STRB200LO = STRB199HI+1;       
  localparam STRB200HI = STRB200LO+STRB_MAX;
  localparam STRB201LO = STRB200HI+1;       
  localparam STRB201HI = STRB201LO+STRB_MAX;
  localparam STRB202LO = STRB201HI+1;       
  localparam STRB202HI = STRB202LO+STRB_MAX;
  localparam STRB203LO = STRB202HI+1;       
  localparam STRB203HI = STRB203LO+STRB_MAX;
  localparam STRB204LO = STRB203HI+1;       
  localparam STRB204HI = STRB204LO+STRB_MAX;
  localparam STRB205LO = STRB204HI+1;       
  localparam STRB205HI = STRB205LO+STRB_MAX;
  localparam STRB206LO = STRB205HI+1;       
  localparam STRB206HI = STRB206LO+STRB_MAX;
  localparam STRB207LO = STRB206HI+1;       
  localparam STRB207HI = STRB207LO+STRB_MAX;
  localparam STRB208LO = STRB207HI+1;       
  localparam STRB208HI = STRB208LO+STRB_MAX;
  localparam STRB209LO = STRB208HI+1;       
  localparam STRB209HI = STRB209LO+STRB_MAX;
  localparam STRB210LO = STRB209HI+1;       
  localparam STRB210HI = STRB210LO+STRB_MAX;
  localparam STRB211LO = STRB210HI+1;       
  localparam STRB211HI = STRB211LO+STRB_MAX;
  localparam STRB212LO = STRB211HI+1;       
  localparam STRB212HI = STRB212LO+STRB_MAX;
  localparam STRB213LO = STRB212HI+1;       
  localparam STRB213HI = STRB213LO+STRB_MAX;
  localparam STRB214LO = STRB213HI+1;       
  localparam STRB214HI = STRB214LO+STRB_MAX;
  localparam STRB215LO = STRB214HI+1;       
  localparam STRB215HI = STRB215LO+STRB_MAX;
  localparam STRB216LO = STRB215HI+1;       
  localparam STRB216HI = STRB216LO+STRB_MAX;
  localparam STRB217LO = STRB216HI+1;       
  localparam STRB217HI = STRB217LO+STRB_MAX;
  localparam STRB218LO = STRB217HI+1;       
  localparam STRB218HI = STRB218LO+STRB_MAX;
  localparam STRB219LO = STRB218HI+1;       
  localparam STRB219HI = STRB219LO+STRB_MAX;
  localparam STRB220LO = STRB219HI+1;       
  localparam STRB220HI = STRB220LO+STRB_MAX;
  localparam STRB221LO = STRB220HI+1;       
  localparam STRB221HI = STRB221LO+STRB_MAX;
  localparam STRB222LO = STRB221HI+1;       
  localparam STRB222HI = STRB222LO+STRB_MAX;
  localparam STRB223LO = STRB222HI+1;       
  localparam STRB223HI = STRB223LO+STRB_MAX;
  localparam STRB224LO = STRB223HI+1;       
  localparam STRB224HI = STRB224LO+STRB_MAX;
  localparam STRB225LO = STRB224HI+1;       
  localparam STRB225HI = STRB225LO+STRB_MAX;
  localparam STRB226LO = STRB225HI+1;       
  localparam STRB226HI = STRB226LO+STRB_MAX;
  localparam STRB227LO = STRB226HI+1;       
  localparam STRB227HI = STRB227LO+STRB_MAX;
  localparam STRB228LO = STRB227HI+1;       
  localparam STRB228HI = STRB228LO+STRB_MAX;
  localparam STRB229LO = STRB228HI+1;       
  localparam STRB229HI = STRB229LO+STRB_MAX;
  localparam STRB230LO = STRB229HI+1;       
  localparam STRB230HI = STRB230LO+STRB_MAX;
  localparam STRB231LO = STRB230HI+1;       
  localparam STRB231HI = STRB231LO+STRB_MAX;
  localparam STRB232LO = STRB231HI+1;       
  localparam STRB232HI = STRB232LO+STRB_MAX;
  localparam STRB233LO = STRB232HI+1;       
  localparam STRB233HI = STRB233LO+STRB_MAX;
  localparam STRB234LO = STRB233HI+1;       
  localparam STRB234HI = STRB234LO+STRB_MAX;
  localparam STRB235LO = STRB234HI+1;       
  localparam STRB235HI = STRB235LO+STRB_MAX;
  localparam STRB236LO = STRB235HI+1;       
  localparam STRB236HI = STRB236LO+STRB_MAX;
  localparam STRB237LO = STRB236HI+1;       
  localparam STRB237HI = STRB237LO+STRB_MAX;
  localparam STRB238LO = STRB237HI+1;       
  localparam STRB238HI = STRB238LO+STRB_MAX;
  localparam STRB239LO = STRB238HI+1;       
  localparam STRB239HI = STRB239LO+STRB_MAX;
  localparam STRB240LO = STRB239HI+1;       
  localparam STRB240HI = STRB240LO+STRB_MAX;
  localparam STRB241LO = STRB240HI+1;       
  localparam STRB241HI = STRB241LO+STRB_MAX;
  localparam STRB242LO = STRB241HI+1;       
  localparam STRB242HI = STRB242LO+STRB_MAX;
  localparam STRB243LO = STRB242HI+1;       
  localparam STRB243HI = STRB243LO+STRB_MAX;
  localparam STRB244LO = STRB243HI+1;       
  localparam STRB244HI = STRB244LO+STRB_MAX;
  localparam STRB245LO = STRB244HI+1;       
  localparam STRB245HI = STRB245LO+STRB_MAX;
  localparam STRB246LO = STRB245HI+1;       
  localparam STRB246HI = STRB246LO+STRB_MAX;
  localparam STRB247LO = STRB246HI+1;       
  localparam STRB247HI = STRB247LO+STRB_MAX;
  localparam STRB248LO = STRB247HI+1;       
  localparam STRB248HI = STRB248LO+STRB_MAX;
  localparam STRB249LO = STRB248HI+1;       
  localparam STRB249HI = STRB249LO+STRB_MAX;
  localparam STRB250LO = STRB249HI+1;       
  localparam STRB250HI = STRB250LO+STRB_MAX;
  localparam STRB251LO = STRB250HI+1;       
  localparam STRB251HI = STRB251LO+STRB_MAX;
  localparam STRB252LO = STRB251HI+1;       
  localparam STRB252HI = STRB252LO+STRB_MAX;
  localparam STRB253LO = STRB252HI+1;       
  localparam STRB253HI = STRB253LO+STRB_MAX;
  localparam STRB254LO = STRB253HI+1;       
  localparam STRB254HI = STRB254LO+STRB_MAX;
  localparam STRB255LO = STRB254HI+1;       
  localparam STRB255HI = STRB255LO+STRB_MAX;
  localparam STRB256LO = STRB255HI+1;       
  localparam STRB256HI = STRB256LO+STRB_MAX;

  localparam WBURSTMAX = STRB256HI+1; // Write burst register array maximum
  localparam RBURSTMAX = IDHI;        // Read burst register array maximum
  localparam LOG2MAXRBURSTS  = clogb2(MAXRBURSTS);
  localparam LOG2MAXWBURSTS  = clogb2(MAXWBURSTS);

//------------------------------------------------------------------------------
// INDEX:   2) Inputs (no outputs)
//------------------------------------------------------------------------------

  // INDEX:        - Global Signals
  // =====
  input wire                ACLK;        // AXI Clock
  input wire                ARESETn;     // AXI Reset

  // INDEX:        - Write Address Channel
  // =====
  input wire   [ID_MAX_W:0] AWID;
  input wire   [ADDR_MAX:0] AWADDR;
  input wire          [7:0] AWLEN;
  input wire          [2:0] AWSIZE;
  input wire          [1:0] AWBURST;
  input wire          [3:0] AWCACHE;
  input wire          [2:0] AWPROT;
  input wire          [3:0] AWQOS;
  input wire          [3:0] AWREGION;
  input wire                AWLOCK;
  input wire [AWUSER_MAX:0] AWUSER;
  input wire                AWVALID;
  input wire                AWREADY;

  // INDEX:        - Write Data Channel
  // =====
  input wire   [DATA_MAX:0] WDATA;
  input wire   [STRB_MAX:0] WSTRB;
  input wire  [WUSER_MAX:0] WUSER;
  input wire                WLAST;
  input wire                WVALID;
  input wire                WREADY;

  // INDEX:        - Write Response Channel
  // =====
  input wire   [ID_MAX_W:0] BID;
  input wire          [1:0] BRESP;
  input wire  [BUSER_MAX:0] BUSER;
  input wire                BVALID;
  input wire                BREADY;

  // INDEX:        - Read Address Channel
  // =====
  input wire   [ID_MAX_R:0] ARID;
  input wire   [ADDR_MAX:0] ARADDR;
  input wire          [7:0] ARLEN;
  input wire          [2:0] ARSIZE;
  input wire          [1:0] ARBURST;
  input wire          [3:0] ARCACHE;
  input wire          [3:0] ARQOS;
  input wire          [3:0] ARREGION;
  input wire          [2:0] ARPROT;
  input wire                ARLOCK;
  input wire [ARUSER_MAX:0] ARUSER;
  input wire                ARVALID;
  input wire                ARREADY;

  // INDEX:        - Read Data Channel
  // =====
  input wire   [ID_MAX_R:0] RID;
  input wire   [DATA_MAX:0] RDATA;
  input wire          [1:0] RRESP;
  input wire  [RUSER_MAX:0] RUSER;
  input wire                RLAST;
  input wire                RVALID;
  input wire                RREADY;

  // INDEX:        - Low Power Interface
  // =====
  input wire                CACTIVE;
  input wire                CSYSREQ;
  input wire                CSYSACK;

//------------------------------------------------------------------------------
// INDEX:   3) Wire and Reg Declarations
//------------------------------------------------------------------------------

  // Write CAMs
  reg [LOG2MAXWBURSTS:0] WIndex;
  reg  [WBURSTMAX:0] WBurstCam[1:MAXWBURSTS];  // store outstanding write bursts
  reg          [8:0] WCountCam[1:MAXWBURSTS];  // number of write data stored
  reg                WLastCam[1:MAXWBURSTS];   // WLAST handshake for 
                                               // outstanding writes
  reg                WAddrCam[1:MAXWBURSTS];   // flag for write addr hsk
  reg                BRespCam[1:MAXWBURSTS];   // flag for write resp hsk 

  wire [WBURSTMAX:0] CurrentAWInfo;
  wire [WBURSTMAX:0] CurrentWInfo;
  wire [WBURSTMAX:0] CurrentBInfo;


  // Read CAMs
  reg  [RBURSTMAX:0] RBurstCam[1:MAXRBURSTS];
  reg          [8:0] RCountCam[1:MAXRBURSTS];
  reg [LOG2MAXRBURSTS:0] RIndex;
  reg [LOG2MAXRBURSTS:0] RIndexNext;
  wire               RPop;
  wire               RPush;
  wire               nROutstanding;  // flag for an empty RBurstCam
  reg                RIdCamDelta;    // flag indicates that RidCam has changed

  // Protocol error flags
  reg                AWDataNumError1;   // flag to derive WriteDataNumError
  reg                AWDataNumError2;   // flag to derive WriteDataNumError
  reg                AWDataNumError3;   // flag to derive WriteDataNumError
  reg                WDataNumError1;    // flag to derive WriteDataNumError
  reg                WDataNumError2;    // flag to derive WriteDataNumError

  // signals for checking for match in ID CAMs
  reg        [LOG2MAXWBURSTS:0] AIDMatch;
  reg        [LOG2MAXWBURSTS:0] AIDMatch_next;
  reg        [LOG2MAXWBURSTS:0] WIDMatch;
  reg        [LOG2MAXWBURSTS:0] WIDMatch_next;
  reg        [LOG2MAXRBURSTS:0] RidMatch;
  reg        [LOG2MAXWBURSTS:0] BIDMatch;

  reg          [6:0] AlignMaskR; // mask for checking read address alignment
  reg          [6:0] AlignMaskW; // mask for checking write address alignment

  // signals for Address Checking
  reg   [ADDR_MAX:0] ArAddrIncr;
  reg   [ADDR_MAX:0] AwAddrIncr;

  // signals for Data Checking
  wire  [DATA_MAX:0] RdataMask;
  reg   [DATA_MAX:0] WdataMask;
  reg         [10:0] ArSizeInBits;
  reg         [10:0] AwSizeInBits;
  reg         [15:0] ArLenInBytes;
  wire         [8:0] ArLenPending;
  wire         [8:0] ArCountPending;
  wire               ArExclPending;

  // arrays to store exclusive access control info
  reg     [ID_MAX:0] ExclId[EXMON_HI:0];
  reg                ExclIdDelta;
  reg   [EXMON_HI:0] ExclIdValid;
  wire               ExclIdFull;
  wire               ExclIdOverflow;
  reg  [EXMON_MAX:0] ExclIdFreePtr;
  wire [EXMON_MAX:0] ExclIdWrPtr;
  reg  [EXMON_MAX:0] ExclAwId;
  reg                ExclAwMatch;
  reg  [EXMON_MAX:0] ExclArId;
  reg                ExclArMatch;
  reg  [EXMON_MAX:0] ExclRId;
  reg                ExclRMatch;
  reg                ExclReadAddr[EXMON_HI:0]; // tracks excl read addr
  reg                ExclReadData[EXMON_HI:0]; // tracks excl read data
  reg   [ADDR_MAX:0] ExclAddr[EXMON_HI:0];
  reg          [2:0] ExclSize[EXMON_HI:0];
  reg          [7:0] ExclLen[EXMON_HI:0];
  reg          [1:0] ExclBurst[EXMON_HI:0];
  reg          [3:0] ExclCache[EXMON_HI:0];
  reg          [2:0] ExclProt[EXMON_HI:0];
  reg          [3:0] ExclQos[EXMON_HI:0];
  reg          [3:0] ExclRegion[EXMON_HI:0];
  reg [AWUSER_MAX:0] ExclUser[EXMON_HI:0];
  reg         [14:0] ExclMask;   // mask to check alignment of exclusive address


  assign CurrentWInfo = WVALID ? WBurstCam[WIDMatch] : {WBURSTMAX+1{1'b0}};
  assign CurrentBInfo = BVALID ? WBurstCam[BIDMatch] : {WBURSTMAX+1{1'b0}};
  assign CurrentAWInfo = AWVALID ? WBurstCam[AIDMatch] : {WBURSTMAX+1{1'b0}};

  reg AwPop;

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
  // +define+AXI4_SVA_CLK=~ACLK
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
// INDEX:   5) Initialize simulation
//------------------------------------------------------------------------------

  initial
  begin
    // INDEX:        - Format for time reporting
    // =====
    // Format for time reporting
    $timeformat(-9, 0, " ns", 0);

    // INDEX:        - Indicate version and release state of Axi4PC
    // =====
    $display("AXI4PC_INFO: Running Axi4PC version BP063-VL-70004-r0p1-00rel0 (SVA implementation)");


    // INDEX:        - Warn if any/some recommended rules are disabled
    // =====
    if (~RecommendOn)
      // All AXI4_REC*_* rules disabled
      $display("AXI4_WARN: All recommended AXI rules have been disabled by the RecommendOn parameter");
    else if (~RecMaxWaitOn)
      // Just AXI4_REC*_MAX_WAIT rules disabled
      $display("AXI4_WARN: Five recommended MAX_WAIT rules have been disabled by the RecMaxWaitOn parameter");

  end

//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI4 Rules: Write Address Channel (*_AW*)
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4_ERRM_AWADDR_BOUNDARY
  // =====
  // 4kbyte boundary: only bottom twelve bits (11 to 0) can change
  //
  // Only need to check INCR bursts since:
  //
  //   a) FIXED bursts cannot violate the 4kB boundary by definition
  //
  //   b) WRAP bursts always stay within a <4kB region because of the wrap
  //      address boundary.  The biggest WRAP burst possible has length 16,
  //      size 128 bytes (1024 bits), so it can transfer 2048 bytes. The
  //      individual transfer addresses wrap at a 2048 byte address boundary,
  //      and the max data transferred in also 2048 bytes, so a 4kB boundary
  //      can never be broken.
  property AXI4_ERRM_AWADDR_BOUNDARY;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
    !($isunknown({AWVALID,AWBURST,AWADDR})) &
      AWVALID & (AWBURST == `AXI4PC_ABURST_INCR)
      |-> (AwAddrIncr[ADDR_MAX:12] == AWADDR[ADDR_MAX:12]);
  endproperty
  axi4_errm_awaddr_boundary: assert property (AXI4_ERRM_AWADDR_BOUNDARY) else
        `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWADDR_BOUNDARY);


  // INDEX:        - AXI4_ERRM_AWADDR_WRAP_ALIGN
  // =====
  property AXI4_ERRM_AWADDR_WRAP_ALIGN;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({AWVALID,AWBURST,AWADDR})) &
      AWVALID & (AWBURST == `AXI4PC_ABURST_WRAP)
      |-> ((AWADDR[6:0] & AlignMaskW) == AWADDR[6:0]);
  endproperty
  axi4_errm_awaddr_wrap_align: assert property (AXI4_ERRM_AWADDR_WRAP_ALIGN) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWADDR_WRAP_ALIGN);


  // INDEX:        - AXI4_ERRM_AWBURST
  // =====
  property AXI4_ERRM_AWBURST;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({AWVALID,AWBURST})) &
      AWVALID
      |-> (AWBURST != 2'b11);
  endproperty
  axi4_errm_awburst: assert property (AXI4_ERRM_AWBURST) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWBURST);


  // INDEX:        - AXI4_ERRM_AWLEN_LOCK
  // =====
  property AXI4_ERRM_AWLEN_LOCK;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({AWVALID,AWLEN,AWLOCK})) &
      AWVALID & AWLEN > `AXI4PC_ALEN_16
      |-> (AWLOCK != `AXI4PC_ALOCK_EXCL);
  endproperty
  axi4_errm_awlen_lock: assert property (AXI4_ERRM_AWLEN_LOCK) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWLEN_LOCK);


  // INDEX:        - AXI4_ERRM_AWCACHE
  // =====
  property AXI4_ERRM_AWCACHE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({AWVALID,AWCACHE})) &
      AWVALID & ~AWCACHE[1]
      |-> (AWCACHE[3:2] == 2'b00);
  endproperty
  axi4_errm_awcache: assert property (AXI4_ERRM_AWCACHE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWCACHE);


  // INDEX:        - AXI4_ERRM_AWLEN_FIXED
  // =====
  property AXI4_ERRM_AWLEN_FIXED;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({AWVALID,AWLEN,AWBURST})) &
      AWVALID & AWLEN > `AXI4PC_ALEN_16
      |-> (AWBURST != `AXI4PC_ABURST_FIXED);
  endproperty
  axi4_errm_awlen_fixed: assert property (AXI4_ERRM_AWLEN_FIXED) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWLEN_FIXED);


  // INDEX:        - AXI4_ERRM_AWLEN_WRAP
  // =====
  property AXI4_ERRM_AWLEN_WRAP;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({AWVALID,AWBURST,AWLEN})) &
      AWVALID & (AWBURST == `AXI4PC_ABURST_WRAP)
      |-> (AWLEN == `AXI4PC_ALEN_2 ||
           AWLEN == `AXI4PC_ALEN_4 ||
           AWLEN == `AXI4PC_ALEN_8 ||
           AWLEN == `AXI4PC_ALEN_16);
  endproperty
  axi4_errm_awlen_wrap: assert property (AXI4_ERRM_AWLEN_WRAP) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWLEN_WRAP);


  // INDEX:        - AXI4_ERRM_AWSIZE
  // =====
  // Deliberately keeping AwSizeInBits logic outside of assertion, to
  // simplify formal-proofs flow.
  property AXI4_ERRM_AWSIZE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({AWVALID,AWSIZE})) &
      AWVALID
      |-> (AwSizeInBits <= DATA_WIDTH);
  endproperty
  axi4_errm_awsize: assert property (AXI4_ERRM_AWSIZE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWSIZE);


  // INDEX:        - AXI4_ERRM_AWVALID_RESET
  // =====
  property AXI4_ERRM_AWVALID_RESET;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !(`AXI4_SVA_RSTn) & !($isunknown(`AXI4_SVA_RSTn))
      ##1   `AXI4_SVA_RSTn
      |-> !AWVALID;
  endproperty
  axi4_errm_awvalid_reset: assert property (AXI4_ERRM_AWVALID_RESET) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWVALID_RESET);

//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4_ERRM_AWADDR_STABLE
  // =====
  property AXI4_ERRM_AWADDR_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({AWVALID,AWREADY,AWADDR})) &
      `AXI4_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(AWADDR);
  endproperty
  axi4_errm_awaddr_stable: assert property (AXI4_ERRM_AWADDR_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWADDR_STABLE);


  // INDEX:        - AXI4_ERRM_AWBURST_STABLE
  // =====
  property AXI4_ERRM_AWBURST_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({AWVALID,AWREADY,AWBURST})) &
      `AXI4_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(AWBURST);
  endproperty
  axi4_errm_awburst_stable: assert property (AXI4_ERRM_AWBURST_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWBURST_STABLE);


  // INDEX:        - AXI4_ERRM_AWCACHE_STABLE
  // =====
  property AXI4_ERRM_AWCACHE_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({AWVALID,AWREADY,AWCACHE})) &
      `AXI4_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(AWCACHE);
  endproperty
  axi4_errm_awcache_stable: assert property (AXI4_ERRM_AWCACHE_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWCACHE_STABLE);


  // INDEX:        - AXI4_ERRM_AWID_STABLE
  // =====
  property AXI4_ERRM_AWID_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({AWVALID,AWREADY,AWID})) &
      `AXI4_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(AWID);
  endproperty
  axi4_errm_awid_stable: assert property (AXI4_ERRM_AWID_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWID_STABLE);


  // INDEX:        - AXI4_ERRM_AWLEN_STABLE
  // =====
  property AXI4_ERRM_AWLEN_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({AWVALID,AWREADY,AWLEN})) &
      `AXI4_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(AWLEN);
  endproperty
  axi4_errm_awlen_stable: assert property (AXI4_ERRM_AWLEN_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWLEN_STABLE);


  // INDEX:        - AXI4_ERRM_AWLOCK_STABLE
  // =====
  property AXI4_ERRM_AWLOCK_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({AWVALID,AWREADY,AWLOCK})) &
      `AXI4_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(AWLOCK);
  endproperty
  axi4_errm_awlock_stable: assert property (AXI4_ERRM_AWLOCK_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWLOCK_STABLE);


  // INDEX:        - AXI4_ERRM_AWPROT_STABLE
  // =====
  property AXI4_ERRM_AWPROT_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({AWVALID,AWREADY,AWPROT})) &
      `AXI4_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(AWPROT);
  endproperty
  axi4_errm_awprot_stable: assert property (AXI4_ERRM_AWPROT_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWPROT_STABLE);


  // INDEX:        - AXI4_ERRM_AWSIZE_STABLE
  // =====
  property AXI4_ERRM_AWSIZE_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({AWVALID,AWREADY,AWSIZE})) &
      `AXI4_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(AWSIZE);
  endproperty
  axi4_errm_awsize_stable: assert property (AXI4_ERRM_AWSIZE_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWSIZE_STABLE);


  // INDEX:        - AXI4_ERRM_AWQOS_STABLE
  // =====
  property AXI4_ERRM_AWQOS_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({AWVALID,AWREADY,AWQOS})) &
      `AXI4_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(AWQOS);
  endproperty
  axi4_errm_awqos_stable: assert property (AXI4_ERRM_AWQOS_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWQOS_STABLE);


  // INDEX:        - AXI4_ERRM_AWREGION_STABLE
  // =====
  property AXI4_ERRM_AWREGION_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({AWVALID,AWREADY,AWREGION})) &
      `AXI4_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(AWREGION);
  endproperty
  axi4_errm_awregion_stable: assert property (AXI4_ERRM_AWREGION_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWREGION_STABLE);


  // INDEX:        - AXI4_ERRM_AWVALID_STABLE
  // =====
  property AXI4_ERRM_AWVALID_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & AWVALID & !AWREADY & !($isunknown({AWVALID,AWREADY}))
      ##1 `AXI4_SVA_RSTn
      |-> AWVALID;
  endproperty
  axi4_errm_awvalid_stable: assert property (AXI4_ERRM_AWVALID_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWVALID_STABLE);


  // INDEX:        - AXI4_RECS_AWREADY_MAX_WAIT
  // =====
  // Note: this rule does not error if VALID goes low (breaking VALID_STABLE rule)
  property   AXI4_RECS_AWREADY_MAX_WAIT;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & !($isunknown({AWVALID,AWREADY})) &
      RecommendOn  & // Parameter that can disable all AXI4_REC*_* rules
      RecMaxWaitOn & // Parameter that can disable just AXI4_REC*_MAX_WAIT rules
      ( AWVALID & !AWREADY)  // READY=1 within MAXWAITS cycles (or VALID=0)
      |-> ##[1:MAXWAITS] (!AWVALID |  AWREADY); 
  endproperty
  axi4_recs_awready_max_wait: assert property (AXI4_RECS_AWREADY_MAX_WAIT) else
   `ARM_AMBA4_PC_MSG_WARN(`RECS_AWREADY_MAX_WAIT);  

//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------

`ifdef AXI4_XCHECK_OFF
`else  // X-Checking on by default


  // INDEX:        - AXI4_ERRM_AWADDR_X
  // =====
  property AXI4_ERRM_AWADDR_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & AWVALID
      |-> ! $isunknown(AWADDR);
  endproperty
  axi4_errm_awaddr_x: assert property (AXI4_ERRM_AWADDR_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWADDR_X);


  // INDEX:        - AXI4_ERRM_AWBURST_X
  // =====
  property AXI4_ERRM_AWBURST_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & AWVALID
      |-> ! $isunknown(AWBURST);
  endproperty
  axi4_errm_awburst_x: assert property (AXI4_ERRM_AWBURST_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWBURST_X);


  // INDEX:        - AXI4_ERRM_AWCACHE_X
  // =====
  property AXI4_ERRM_AWCACHE_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & AWVALID
      |-> ! $isunknown(AWCACHE);
  endproperty
  axi4_errm_awcache_x: assert property (AXI4_ERRM_AWCACHE_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWCACHE_X);


  // INDEX:        - AXI4_ERRM_AWID_X
  // =====
  property AXI4_ERRM_AWID_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & AWVALID
      |-> ! $isunknown(AWID);
  endproperty
  axi4_errm_awid_x: assert property (AXI4_ERRM_AWID_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWID_X);


  // INDEX:        - AXI4_ERRM_AWLEN_X
  // =====
  property AXI4_ERRM_AWLEN_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & AWVALID
      |-> ! $isunknown(AWLEN);
  endproperty
  axi4_errm_awlen_x: assert property (AXI4_ERRM_AWLEN_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWLEN_X);


  // INDEX:        - AXI4_ERRM_AWLOCK_X
  // =====
  property AXI4_ERRM_AWLOCK_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & AWVALID
      |-> ! $isunknown(AWLOCK);
  endproperty
  axi4_errm_awlock_x: assert property (AXI4_ERRM_AWLOCK_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWLOCK_X);


  // INDEX:        - AXI4_ERRM_AWPROT_X
  // =====
  property AXI4_ERRM_AWPROT_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & AWVALID
      |-> ! $isunknown(AWPROT);
  endproperty
  axi4_errm_awprot_x: assert property (AXI4_ERRM_AWPROT_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWPROT_X);


  // INDEX:        - AXI4_ERRM_AWSIZE_X
  // =====
  property AXI4_ERRM_AWSIZE_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & AWVALID
      |-> ! $isunknown(AWSIZE);
  endproperty
  axi4_errm_awsize_x: assert property (AXI4_ERRM_AWSIZE_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWSIZE_X);


  // INDEX:        - AXI4_ERRM_AWQOS_X
  // =====
  property AXI4_ERRM_AWQOS_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & AWVALID
      |-> ! $isunknown(AWQOS);
  endproperty
  axi4_errm_awqos_x: assert property (AXI4_ERRM_AWQOS_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWQOS_X);


  // INDEX:        - AXI4_ERRM_AWREGION_X
  // =====
  property AXI4_ERRM_AWREGION_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & AWVALID
      |-> ! $isunknown(AWREGION);
  endproperty
  axi4_errm_awregion_x: assert property (AXI4_ERRM_AWREGION_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWREGION_X);


  // INDEX:        - AXI4_ERRM_AWVALID_X
  // =====
  property AXI4_ERRM_AWVALID_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(AWVALID);
  endproperty
  axi4_errm_awvalid_x: assert property (AXI4_ERRM_AWVALID_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWVALID_X);


  // INDEX:        - AXI4_ERRS_AWREADY_X
  // =====
  property AXI4_ERRS_AWREADY_X;
    @(posedge `AXI4_SVA_CLK) 
      `AXI4_SVA_RSTn
      |-> ! $isunknown(AWREADY);
  endproperty
  axi4_errs_awready_x: assert property (AXI4_ERRS_AWREADY_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_AWREADY_X);

`endif // AXI4_XCHECK_OFF

//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI4 Rules: Write Data Channel (*_W*)
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------

  // This will fire in one of the following situations:
  // 1) Write data arrives and WLAST set and WDATA count is not equal to AWLEN
  // 2) Write data arrives and WLAST not set and WDATA count is equal to AWLEN
  // 3) ADDR arrives, WLAST already received and WDATA count not equal to AWLEN

  // =====
  // INDEX:        - AXI4_ERRM_WDATA_NUM_PROP1
  // =====
  property AXI4_ERRM_WDATA_NUM_PROP1;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown(AWDataNumError1))
      |-> ~AWDataNumError1;
  endproperty
  axi4_errm_wdata_num_prop1: assert property (AXI4_ERRM_WDATA_NUM_PROP1) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WDATA_NUM);

  // =====
  // INDEX:        - AXI4_ERRM_WDATA_NUM_PROP2
  // =====
  property AXI4_ERRM_WDATA_NUM_PROP2;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown(AWDataNumError2))
      |-> ~AWDataNumError2;
  endproperty
  axi4_errm_wdata_num_prop2: assert property (AXI4_ERRM_WDATA_NUM_PROP2) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WDATA_NUM);

  // =====
  // INDEX:        - AXI4_ERRM_WDATA_NUM_PROP3
  // =====
  property AXI4_ERRM_WDATA_NUM_PROP3;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown(AWDataNumError3))
      |-> ~AWDataNumError3;
  endproperty
  axi4_errm_wdata_num_prop3: assert property (AXI4_ERRM_WDATA_NUM_PROP3) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WDATA_NUM);

  // =====
  // INDEX:        - AXI4_ERRM_WDATA_NUM_PROP4
  // =====
  property AXI4_ERRM_WDATA_NUM_PROP4;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown(WDataNumError1))
      |-> ~WDataNumError1;
  endproperty
  axi4_errm_wdata_num_prop4: assert property (AXI4_ERRM_WDATA_NUM_PROP4) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WDATA_NUM);

  // =====
  // INDEX:        - AXI4_ERRM_WDATA_NUM_PROP5
  // =====
  property AXI4_ERRM_WDATA_NUM_PROP5;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown(WDataNumError2))
      |-> ~WDataNumError2;
  endproperty
  axi4_errm_wdata_num_prop5: assert property (AXI4_ERRM_WDATA_NUM_PROP5) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WDATA_NUM);


  // INDEX:        - AXI4_ERRM_WSTRB
  // =====
  wire BStrbError = BVALID ? CheckBurst(WBurstCam[BIDMatch], WCountCam[BIDMatch]) : 1'b0;
  property AXI4_ERRM_WSTRB;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown({BVALID,BREADY,WAddrCam[BIDMatch],WLastCam[BIDMatch],WBurstCam[BIDMatch],WCountCam[BIDMatch]})) 
      & BVALID & BREADY & WAddrCam[BIDMatch]& WLastCam[BIDMatch]
      |-> ~BStrbError;
  endproperty
  axi4_errm_wstrb: assert property (AXI4_ERRM_WSTRB) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WSTRB);



  // INDEX:        - AXI4_ERRM_WVALID_RESET
  // =====
  property AXI4_ERRM_WVALID_RESET;
    @(posedge `AXI4_SVA_CLK)
          !(`AXI4_SVA_RSTn) & !($isunknown(`AXI4_SVA_RSTn))
      ##1   `AXI4_SVA_RSTn
      |-> !WVALID;
  endproperty
  axi4_errm_wvalid_reset: assert property (AXI4_ERRM_WVALID_RESET) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WVALID_RESET);

//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4_ERRM_WDATA_STABLE
  // =====
  property AXI4_ERRM_WDATA_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({WVALID,WREADY,WDATA})) &
      `AXI4_SVA_RSTn & WVALID & !WREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(WDATA & WdataMask);
  endproperty
  axi4_errm_wdata_stable: assert property (AXI4_ERRM_WDATA_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WDATA_STABLE);


  // INDEX:        - AXI4_ERRM_WLAST_STABLE
  // =====
  property AXI4_ERRM_WLAST_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({WVALID,WREADY,WLAST})) &
      `AXI4_SVA_RSTn & WVALID & !WREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(WLAST);
  endproperty
  axi4_errm_wlast_stable: assert property (AXI4_ERRM_WLAST_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WLAST_STABLE);


  // INDEX:        - AXI4_ERRM_WSTRB_STABLE
  // =====
  property AXI4_ERRM_WSTRB_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({WVALID,WREADY,WSTRB})) &
      `AXI4_SVA_RSTn & WVALID & !WREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(WSTRB);
  endproperty
  axi4_errm_wstrb_stable: assert property (AXI4_ERRM_WSTRB_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WSTRB_STABLE);


  // INDEX:        - AXI4_ERRM_WVALID_STABLE
  // =====
  property AXI4_ERRM_WVALID_STABLE;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & WVALID & !WREADY & !($isunknown({WVALID,WREADY}))
      ##1 `AXI4_SVA_RSTn
      |-> WVALID;
  endproperty
  axi4_errm_wvalid_stable: assert property (AXI4_ERRM_WVALID_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WVALID_STABLE);


  // INDEX:        - AXI4_RECS_WREADY_MAX_WAIT 
  // =====
  // Note: this rule does not error if VALID goes low (breaking VALID_STABLE rule)
  property   AXI4_RECS_WREADY_MAX_WAIT;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown({WVALID,WREADY})) &
      RecommendOn  & // Parameter that can disable all AXI4_REC*_* rules
      RecMaxWaitOn & // Parameter that can disable just AXI4_REC*_MAX_WAIT rules
      ( WVALID & !WREADY) // READY=1 within MAXWAITS cycles (or VALID=0)
      |-> ##[1:MAXWAITS] (!WVALID |  WREADY);    
  endproperty
  axi4_recs_wready_max_wait: assert property (AXI4_RECS_WREADY_MAX_WAIT) else
   `ARM_AMBA4_PC_MSG_WARN(`RECS_WREADY_MAX_WAIT);  

//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------

`ifdef AXI4_XCHECK_OFF
`else  // X-Checking on by default


  // INDEX:        - AXI4_ERRM_WDATA_X
  // =====
  property AXI4_ERRM_WDATA_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & WVALID & !($isunknown(WdataMask))
      |-> ! $isunknown(WDATA & WdataMask);
  endproperty
  axi4_errm_wdata_x: assert property (AXI4_ERRM_WDATA_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WDATA_X);


  // INDEX:        - AXI4_ERRM_WLAST_X
  // =====
  property AXI4_ERRM_WLAST_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & WVALID
      |-> ! $isunknown(WLAST);
  endproperty
  axi4_errm_wlast_x: assert property (AXI4_ERRM_WLAST_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WLAST_X);


  // INDEX:        - AXI4_ERRM_WSTRB_X
  // =====
  property AXI4_ERRM_WSTRB_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & WVALID
      |-> ! $isunknown(WSTRB);
  endproperty
  axi4_errm_wstrb_x: assert property (AXI4_ERRM_WSTRB_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WSTRB_X);


  // INDEX:        - AXI4_ERRM_WVALID_X
  // =====
  property AXI4_ERRM_WVALID_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(WVALID);
  endproperty
  axi4_errm_wvalid_x: assert property (AXI4_ERRM_WVALID_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WVALID_X);


  // INDEX:        - AXI4_ERRS_WREADY_X
  // =====
  property AXI4_ERRS_WREADY_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(WREADY);
  endproperty
  axi4_errs_wready_x: assert property (AXI4_ERRS_WREADY_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_WREADY_X);


`endif // AXI4_XCHECK_OFF

//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI4 Rules: Write Response Channel (*_B*)
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------


  // INDEX:        - AXI4_ERRS_BRESP_WLAST
  // =====
  property AXI4_ERRS_BRESP_WLAST;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & !($isunknown({BVALID,WLastCam[BIDMatch]}))
      & BVALID
      |-> WLastCam[BIDMatch] && (BIDMatch <= MAXWBURSTS);
  endproperty
  axi4_errs_bresp_wlast: assert property (AXI4_ERRS_BRESP_WLAST) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BRESP_WLAST);




  // INDEX:        - AXI4_ERRS_BRESP_EXOKAY
  // =====
  //if (Burst[EXCL] == 1'b0 && BRESP == `AXI4PC_RESP_EXOKAY)
  property AXI4_ERRS_BRESP_EXOKAY;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown({BVALID,BRESP})) 
      & BVALID & (BRESP == `AXI4PC_RESP_EXOKAY)
      |-> WBurstCam[BIDMatch][EXCL] ;
  endproperty
  axi4_errs_bresp_exokay: assert property (AXI4_ERRS_BRESP_EXOKAY) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BRESP_EXOKAY);


  // INDEX:        - AXI4_ERRS_BVALID_RESET
  // =====
  property AXI4_ERRS_BVALID_RESET;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !(`AXI4_SVA_RSTn) & !($isunknown(`AXI4_SVA_RSTn))
      ##1  `AXI4_SVA_RSTn
      |-> !BVALID;
  endproperty
axi4_errs_bvalid_reset: assert property (AXI4_ERRS_BVALID_RESET) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BVALID_RESET);


  // INDEX:        - AXI4_ERRS_BRESP_AW 
  // =====
  property AXI4_ERRS_BRESP_AW;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & !($isunknown(BVALID)) 
      & BVALID
      |-> WAddrCam[BIDMatch] && (BIDMatch <= MAXWBURSTS);
  endproperty
  axi4_errs_bresp_aw: assert property (AXI4_ERRS_BRESP_AW) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BRESP_AW);

//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4_ERRS_BID_STABLE
  // =====
  property AXI4_ERRS_BID_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({BVALID,BREADY,BID})) &
      `AXI4_SVA_RSTn & BVALID & !BREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(BID);
  endproperty
  axi4_errs_bid_stable: assert property (AXI4_ERRS_BID_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BID_STABLE);


  // INDEX:        - AXI4_ERRS_BRESP_STABLE
  // =====
  property AXI4_ERRS_BRESP_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({BVALID,BREADY,BRESP})) &
      `AXI4_SVA_RSTn & BVALID & !BREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(BRESP);
  endproperty
  axi4_errs_bresp_stable: assert property (AXI4_ERRS_BRESP_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BRESP_STABLE);


  // INDEX:        - AXI4_ERRS_BVALID_STABLE
  // =====
  property AXI4_ERRS_BVALID_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & BVALID & !BREADY & !($isunknown({BVALID,BREADY}))
      ##1 `AXI4_SVA_RSTn
      |-> BVALID;
  endproperty
  axi4_errs_bvalid_stable: assert property (AXI4_ERRS_BVALID_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BVALID_STABLE);


  // INDEX:        - AXI4_RECM_BREADY_MAX_WAIT 
  // =====
  // Note: this rule does not error if VALID goes low (breaking VALID_STABLE rule)
  property   AXI4_RECM_BREADY_MAX_WAIT;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & !($isunknown({BVALID,BREADY})) &
      RecommendOn  & // Parameter that can disable all AXI4_REC*_* rules
      RecMaxWaitOn & // Parameter that can disable just AXI4_REC*_MAX_WAIT rules
      ( BVALID & !BREADY) // READY=1 within MAXWAITS cycles (or VALID=0)
      |-> ##[1:MAXWAITS] (!BVALID |  BREADY);    
  endproperty
  axi4_recm_bready_max_wait: assert property (AXI4_RECM_BREADY_MAX_WAIT) else
   `ARM_AMBA4_PC_MSG_WARN(`RECM_BREADY_MAX_WAIT);

//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------

`ifdef AXI4_XCHECK_OFF
`else  // X-Checking on by default


  // INDEX:        - AXI4_ERRM_BREADY_X
  // =====
  property AXI4_ERRM_BREADY_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(BREADY);
  endproperty
  axi4_errm_bready_x: assert property (AXI4_ERRM_BREADY_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_BREADY_X);


  // INDEX:        - AXI4_ERRS_BID_X
  // =====
  property AXI4_ERRS_BID_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & BVALID
      |-> ! $isunknown(BID);
  endproperty
  axi4_errs_bid_x: assert property (AXI4_ERRS_BID_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BID_X);


  // INDEX:        - AXI4_ERRS_BRESP_X
  // =====
  property AXI4_ERRS_BRESP_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & BVALID
      |-> ! $isunknown(BRESP);
  endproperty
  axi4_errs_bresp_x: assert property (AXI4_ERRS_BRESP_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BRESP_X);


  // INDEX:        - AXI4_ERRS_BVALID_X
  // =====
  property AXI4_ERRS_BVALID_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(BVALID);
  endproperty
  axi4_errs_bvalid_x: assert property (AXI4_ERRS_BVALID_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BVALID_X);


`endif // AXI4_XCHECK_OFF

//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI4 Rules: Read Address Channel (*_AR*)
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4_ERRM_ARADDR_BOUNDARY
  // =====
  // 4kbyte boundary: only bottom twelve bits (11 to 0) can change
  //
  // Only need to check INCR bursts since:
  //
  //   a) FIXED bursts cannot violate the 4kB boundary by definition
  //
  //   b) WRAP bursts always stay within a <4kB region because of the wrap
  //      address boundary.  The biggest WRAP burst possible has length 16,
  //      size 128 bytes (1024 bits), so it can transfer 2048 bytes. The
  //      individual transfer addresses wrap at a 2048 byte address boundary,
  //      and the max data transferred in also 2048 bytes, so a 4kB boundary
  //      can never be broken.
  property AXI4_ERRM_ARADDR_BOUNDARY;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARBURST,ARADDR})) &
      ARVALID & (ARBURST == `AXI4PC_ABURST_INCR)
      |-> (ArAddrIncr[ADDR_MAX:12] == ARADDR[ADDR_MAX:12]);
  endproperty
  axi4_errm_araddr_boundary: assert property (AXI4_ERRM_ARADDR_BOUNDARY) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARADDR_BOUNDARY);


  // INDEX:        - AXI4_ERRM_ARADDR_WRAP_ALIGN
  // =====
  property AXI4_ERRM_ARADDR_WRAP_ALIGN;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARBURST,ARADDR})) &
      ARVALID & (ARBURST == `AXI4PC_ABURST_WRAP)
      |-> ((ARADDR[6:0] & AlignMaskR) == ARADDR[6:0]);
  endproperty
  axi4_errm_araddr_wrap_align: assert property (AXI4_ERRM_ARADDR_WRAP_ALIGN) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARADDR_WRAP_ALIGN);


  // INDEX:        - AXI4_ERRM_ARBURST
  // =====
  property AXI4_ERRM_ARBURST;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARBURST})) &
      ARVALID
      |-> (ARBURST != 2'b11);
  endproperty
  axi4_errm_arburst: assert property (AXI4_ERRM_ARBURST) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARBURST);


  // INDEX:        - AXI4_ERRM_ARLEN_LOCK
  // =====
  property AXI4_ERRM_ARLEN_LOCK;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARLEN,ARLOCK})) &
      ARVALID & ARLEN > `AXI4PC_ALEN_16
      |-> (ARLOCK != `AXI4PC_ALOCK_EXCL);
  endproperty
  axi4_errm_arlen_lock: assert property (AXI4_ERRM_ARLEN_LOCK) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARLEN_LOCK);


  // INDEX:        - AXI4_ERRM_ARCACHE
  // =====
  property AXI4_ERRM_ARCACHE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARCACHE})) &
      ARVALID & ~ARCACHE[1]
      |-> (ARCACHE[3:2] == 2'b00);
  endproperty
  axi4_errm_arcache: assert property (AXI4_ERRM_ARCACHE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARCACHE);


  // INDEX:        - AXI4_ERRM_ARLEN_FIXED
  // =====
  property AXI4_ERRM_ARLEN_FIXED;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARLEN,ARBURST})) &
      ARVALID & ARLEN > `AXI4PC_ALEN_16
      |-> (ARBURST != `AXI4PC_ABURST_FIXED);
  endproperty
  axi4_errm_arlen_fixed: assert property (AXI4_ERRM_ARLEN_FIXED) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARLEN_FIXED);


  // INDEX:        - AXI4_ERRM_ARLEN_WRAP
  // =====
  // This property is disabled for ACE because a cache maintenance transfer 
  // can have a length of 1 and be a wrap. This rule is duplicated in the
  // ACEPC to cover this rule.
  property AXI4_ERRM_ARLEN_WRAP;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({ARVALID,ARBURST,ARLEN})) &
      ARVALID & (ARBURST == `AXI4PC_ABURST_WRAP) 
      |-> (ARLEN == `AXI4PC_ALEN_2 ||
           ARLEN == `AXI4PC_ALEN_4 ||
           ARLEN == `AXI4PC_ALEN_8 ||
           ARLEN == `AXI4PC_ALEN_16);
  endproperty
  axi4_errm_arlen_wrap: assert property (AXI4_ERRM_ARLEN_WRAP) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARLEN_WRAP);


  // INDEX:        - AXI4_ERRM_ARSIZE
  // =====
  property AXI4_ERRM_ARSIZE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARSIZE})) &
      ARVALID
      |-> (ArSizeInBits <= DATA_WIDTH);
  endproperty
  axi4_errm_arsize: assert property (AXI4_ERRM_ARSIZE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARSIZE);


  // INDEX:        - AXI4_ERRM_ARVALID_RESET
  // =====
  property AXI4_ERRM_ARVALID_RESET;
    @(posedge `AXI4_SVA_CLK)
      !(`AXI4_SVA_RSTn) & !($isunknown(`AXI4_SVA_RSTn))
      ##1  `AXI4_SVA_RSTn
      |-> !ARVALID;
  endproperty
  axi4_errm_arvalid_reset: assert property (AXI4_ERRM_ARVALID_RESET) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARVALID_RESET);

//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4_ERRM_ARADDR_STABLE
  // =====
  property AXI4_ERRM_ARADDR_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARREADY,ARADDR})) &
      `AXI4_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(ARADDR);
  endproperty
  axi4_errm_araddr_stable: assert property (AXI4_ERRM_ARADDR_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARADDR_STABLE);


  // INDEX:        - AXI4_ERRM_ARBURST_STABLE
  // =====
  property AXI4_ERRM_ARBURST_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARREADY,ARBURST})) &
      `AXI4_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(ARBURST);
  endproperty
  axi4_errm_arburst_stable: assert property (AXI4_ERRM_ARBURST_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARBURST_STABLE);


  // INDEX:        - AXI4_ERRM_ARCACHE_STABLE
  // =====
  property AXI4_ERRM_ARCACHE_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARREADY,ARCACHE})) &
      `AXI4_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(ARCACHE);
  endproperty
  axi4_errm_arcache_stable: assert property (AXI4_ERRM_ARCACHE_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARCACHE_STABLE);


  // INDEX:        - AXI4_ERRM_ARID_STABLE
  // =====
  property AXI4_ERRM_ARID_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARREADY,ARID})) &
      `AXI4_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(ARID);
  endproperty
  axi4_errm_arid_stable: assert property (AXI4_ERRM_ARID_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARID_STABLE);


  // INDEX:        - AXI4_ERRM_ARLEN_STABLE
  // =====
  property AXI4_ERRM_ARLEN_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({ARVALID,ARREADY,ARLEN})) &
      `AXI4_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(ARLEN);
  endproperty
  axi4_errm_arlen_stable: assert property (AXI4_ERRM_ARLEN_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARLEN_STABLE);


  // INDEX:        - AXI4_ERRM_ARLOCK_STABLE
  // =====
  property AXI4_ERRM_ARLOCK_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARREADY,ARLOCK})) &
      `AXI4_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(ARLOCK);
  endproperty
  axi4_errm_arlock_stable: assert property (AXI4_ERRM_ARLOCK_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARLOCK_STABLE);


  // INDEX:        - AXI4_ERRM_ARPROT_STABLE
  // =====
  property AXI4_ERRM_ARPROT_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARREADY,ARPROT})) &
      `AXI4_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(ARPROT);
  endproperty
  axi4_errm_arprot_stable: assert property (AXI4_ERRM_ARPROT_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARPROT_STABLE);


  // INDEX:        - AXI4_ERRM_ARSIZE_STABLE
  // =====
  property AXI4_ERRM_ARSIZE_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARREADY,ARSIZE})) &
      `AXI4_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(ARSIZE);
  endproperty
  axi4_errm_arsize_stable: assert property (AXI4_ERRM_ARSIZE_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARSIZE_STABLE);


  // INDEX:        - AXI4_ERRM_ARQOS_STABLE
  // =====
  property AXI4_ERRM_ARQOS_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARREADY,ARQOS})) &
      `AXI4_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(ARQOS);
  endproperty
  axi4_errm_arqos_stable: assert property (AXI4_ERRM_ARQOS_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARQOS_STABLE);


  // INDEX:        - AXI4_ERRM_ARREGION_STABLE
  // =====
  property AXI4_ERRM_ARREGION_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARREADY,ARREGION})) &
      `AXI4_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(ARREGION);
  endproperty
  axi4_errm_arregion_stable: assert property (AXI4_ERRM_ARREGION_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARREGION_STABLE);


  // INDEX:        - AXI4_ERRM_ARVALID_STABLE
  // =====
  property AXI4_ERRM_ARVALID_STABLE;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & ARVALID & !ARREADY & !($isunknown({ARVALID,ARREADY}))
      ##1 `AXI4_SVA_RSTn
      |-> ARVALID;
  endproperty
  axi4_errm_arvalid_stable: assert property (AXI4_ERRM_ARVALID_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARVALID_STABLE);


  // INDEX:        - AXI4_RECS_ARREADY_MAX_WAIT 
  // =====
  // Note: this rule does not error if VALID goes low (breaking VALID_STABLE rule)
  property   AXI4_RECS_ARREADY_MAX_WAIT;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown({ARVALID,ARREADY})) &
      RecommendOn  & // Parameter that can disable all AXI4_REC*_* rules
      RecMaxWaitOn & // Parameter that can disable just AXI4_REC*_MAX_WAIT rules
      ( ARVALID & !ARREADY) // READY=1 within MAXWAITS cycles (or VALID=0)
      |-> ##[1:MAXWAITS] (!ARVALID |  ARREADY);  
  endproperty
  axi4_recs_arready_max_wait: assert property (AXI4_RECS_ARREADY_MAX_WAIT) else
   `ARM_AMBA4_PC_MSG_WARN(`RECS_ARREADY_MAX_WAIT);  

//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------

`ifdef AXI4_XCHECK_OFF
`else  // X-Checking on by default


  // INDEX:        - AXI4_ERRM_ARADDR_X
  // =====
  property AXI4_ERRM_ARADDR_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & ARVALID
      |-> ! $isunknown(ARADDR);
  endproperty
  axi4_errm_araddr_x: assert property (AXI4_ERRM_ARADDR_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARADDR_X);


  // INDEX:        - AXI4_ERRM_ARBURST_X
  // =====
  property AXI4_ERRM_ARBURST_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & ARVALID
      |-> ! $isunknown(ARBURST);
  endproperty
  axi4_errm_arburst_x: assert property (AXI4_ERRM_ARBURST_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARBURST_X);


  // INDEX:        - AXI4_ERRM_ARCACHE_X
  // =====
  property AXI4_ERRM_ARCACHE_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & ARVALID
      |-> ! $isunknown(ARCACHE);
  endproperty
  axi4_errm_arcache_x: assert property (AXI4_ERRM_ARCACHE_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARCACHE_X);


  // INDEX:        - AXI4_ERRM_ARID_X
  // =====
  property AXI4_ERRM_ARID_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & ARVALID
      |-> ! $isunknown(ARID);
  endproperty
  axi4_errm_arid_x: assert property (AXI4_ERRM_ARID_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARID_X);


  // INDEX:        - AXI4_ERRM_ARLEN_X
  // =====
  property AXI4_ERRM_ARLEN_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & ARVALID
      |-> ! $isunknown(ARLEN);
  endproperty
  axi4_errm_arlen_x: assert property (AXI4_ERRM_ARLEN_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARLEN_X);


  // INDEX:        - AXI4_ERRM_ARLOCK_X
  // =====
  property AXI4_ERRM_ARLOCK_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & ARVALID
      |-> ! $isunknown(ARLOCK);
  endproperty
  axi4_errm_arlock_x: assert property (AXI4_ERRM_ARLOCK_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARLOCK_X);


  // INDEX:        - AXI4_ERRM_ARPROT_X
  // =====
  property AXI4_ERRM_ARPROT_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & ARVALID
      |-> ! $isunknown(ARPROT);
  endproperty
  axi4_errm_arprot_x: assert property (AXI4_ERRM_ARPROT_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARPROT_X);


  // INDEX:        - AXI4_ERRM_ARSIZE_X
  // =====
  property AXI4_ERRM_ARSIZE_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & ARVALID
      |-> ! $isunknown(ARSIZE);
  endproperty
  axi4_errm_arsize_x: assert property (AXI4_ERRM_ARSIZE_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARSIZE_X);


  // INDEX:        - AXI4_ERRM_ARQOS_X
  // =====
  property AXI4_ERRM_ARQOS_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & ARVALID
      |-> ! $isunknown(ARQOS);
  endproperty
  axi4_errm_arqos_x: assert property (AXI4_ERRM_ARQOS_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARQOS_X);


  // INDEX:        - AXI4_ERRM_ARREGION_X
  // =====
  property AXI4_ERRM_ARREGION_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & ARVALID
      |-> ! $isunknown(ARREGION);
  endproperty
  axi4_errm_arregion_x: assert property (AXI4_ERRM_ARREGION_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARREGION_X);


  // INDEX:        - AXI4_ERRM_ARVALID_X
  // =====
  property AXI4_ERRM_ARVALID_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(ARVALID);
  endproperty
  axi4_errm_arvalid_x: assert property (AXI4_ERRM_ARVALID_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARVALID_X);


  // INDEX:        - AXI4_ERRS_ARREADY_X
  // =====
  property AXI4_ERRS_ARREADY_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(ARREADY);
  endproperty
  axi4_errs_arready_x: assert property (AXI4_ERRS_ARREADY_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_ARREADY_X);

`endif // AXI4_XCHECK_OFF

//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI4 Rules: Read Data Channel (*_R*)
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4_ERRS_RDATA_NUM
  // =====
  property AXI4_ERRS_RDATA_NUM;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({RVALID,RREADY,RLAST,ArLenPending})) &
      `AXI4_SVA_RSTn & RVALID // Last RDATA and RLAST is asserted
      |-> ( ((ArCountPending == ArLenPending) & RLAST)  
      // Not last RDATA and RLAST is not asserted
      |((ArCountPending != ArLenPending) & ~RLAST)); 
  endproperty
  axi4_errs_rdata_num: assert property (AXI4_ERRS_RDATA_NUM) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RDATA_NUM);

  // INDEX:        - AXI4_ERRS_RID
  // =====
  // Read data must always follow the address that it relates to.
  property AXI4_ERRS_RID;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(RVALID)) &
      `AXI4_SVA_RSTn & RVALID
      |-> (RidMatch > 0);
  endproperty
  axi4_errs_rid: assert property (AXI4_ERRS_RID) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RID);


  // INDEX:        - AXI4_ERRS_RRESP_EXOKAY
  // =====
  property AXI4_ERRS_RRESP_EXOKAY;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({RVALID,RREADY,RRESP})) &
      `AXI4_SVA_RSTn & RVALID & RREADY & (RRESP == `AXI4PC_RESP_EXOKAY)
      |-> (ArExclPending);
  endproperty
  axi4_errs_rresp_exokay: assert property (AXI4_ERRS_RRESP_EXOKAY) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RRESP_EXOKAY);


  // INDEX:        - AXI4_ERRS_RVALID_RESET
  // =====
  property AXI4_ERRS_RVALID_RESET;
    @(posedge `AXI4_SVA_CLK)
      !(`AXI4_SVA_RSTn) & !($isunknown(`AXI4_SVA_RSTn))
      ##1   `AXI4_SVA_RSTn
      |-> !RVALID;
  endproperty
   axi4_errs_rvalid_reset: assert property (AXI4_ERRS_RVALID_RESET) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RVALID_RESET);

//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4_ERRS_RDATA_STABLE
  // =====
  property AXI4_ERRS_RDATA_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({RVALID,RREADY,RDATA})) &
      `AXI4_SVA_RSTn & RVALID & !RREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(RDATA | ~RdataMask);
  endproperty
  axi4_errs_rdata_stable: assert property (AXI4_ERRS_RDATA_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RDATA_STABLE);


  // INDEX:        - AXI4_ERRS_RID_STABLE
  // =====
  property AXI4_ERRS_RID_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({RVALID,RREADY,RID})) &
      `AXI4_SVA_RSTn & RVALID & !RREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(RID);
  endproperty
  axi4_errs_rid_stable: assert property (AXI4_ERRS_RID_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RID_STABLE);


  // INDEX:        - AXI4_ERRS_RLAST_STABLE
  // =====
  property AXI4_ERRS_RLAST_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({RVALID,RREADY,RLAST})) &
      `AXI4_SVA_RSTn & RVALID & !RREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(RLAST);
  endproperty
  axi4_errs_rlast_stable: assert property (AXI4_ERRS_RLAST_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RLAST_STABLE);


  // INDEX:        - AXI4_ERRS_RRESP_STABLE
  // =====
  property AXI4_ERRS_RRESP_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({RVALID,RREADY,RRESP})) &
      `AXI4_SVA_RSTn & RVALID & !RREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(RRESP);
  endproperty
  axi4_errs_rresp_stable: assert property (AXI4_ERRS_RRESP_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RRESP_STABLE);


  // INDEX:        - AXI4_ERRS_RVALID_STABLE
  // =====
  property AXI4_ERRS_RVALID_STABLE;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & RVALID & !RREADY & !($isunknown({RVALID,RREADY}))
      ##1 `AXI4_SVA_RSTn
      |-> RVALID;
  endproperty
  axi4_errs_rvalid_stable: assert property (AXI4_ERRS_RVALID_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RVALID_STABLE);


  // INDEX:        - AXI4_RECM_RREADY_MAX_WAIT 
  // =====
  // Note: this rule does not error if VALID goes low (breaking VALID_STABLE rule)
  property   AXI4_RECM_RREADY_MAX_WAIT;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown({RVALID,RREADY})) &
      RecommendOn  & // Parameter that can disable all AXI4_REC*_* rules
      RecMaxWaitOn & // Parameter that can disable just AXI4_REC*_MAX_WAIT rules
      ( RVALID & !RREADY) // READY=1 within MAXWAITS cycles (or VALID=0)
      |-> ##[1:MAXWAITS] (!RVALID |  RREADY);    
  endproperty
  axi4_recm_rready_max_wait: assert property (AXI4_RECM_RREADY_MAX_WAIT) else
   `ARM_AMBA4_PC_MSG_WARN(`RECM_RREADY_MAX_WAIT);  

//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------

`ifdef AXI4_XCHECK_OFF
`else  // X-Checking on by default


  // INDEX:        - AXI4_ERRS_RDATA_X
  // =====
  property AXI4_ERRS_RDATA_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & RVALID
      |-> ! $isunknown(RDATA | ~RdataMask);
  endproperty
  axi4_errs_rdata_x: assert property (AXI4_ERRS_RDATA_X) else
    `ARM_AMBA4_PC_MSG_ERR(`ERRS_RDATA_X);


  // INDEX:        - AXI4_ERRM_RREADY_X
  // =====
  property AXI4_ERRM_RREADY_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(RREADY);
  endproperty
  axi4_errm_rready_x: assert property (AXI4_ERRM_RREADY_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_RREADY_X);


  // INDEX:        - AXI4_ERRS_RID_X
  // =====
  property AXI4_ERRS_RID_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & RVALID
      |-> ! $isunknown(RID);
  endproperty
  axi4_errs_rid_x: assert property (AXI4_ERRS_RID_X) else
    `ARM_AMBA4_PC_MSG_ERR(`ERRS_RID_X);


  // INDEX:        - AXI4_ERRS_RLAST_X
  // =====
  property AXI4_ERRS_RLAST_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & RVALID
      |-> ! $isunknown(RLAST);
  endproperty
  axi4_errs_rlast_x: assert property (AXI4_ERRS_RLAST_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RLAST_X);


  // INDEX:        - AXI4_ERRS_RRESP_X
  // =====
  property AXI4_ERRS_RRESP_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & RVALID
      |-> ! $isunknown(RRESP);
  endproperty
  axi4_errs_rresp_x: assert property (AXI4_ERRS_RRESP_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RRESP_X);


  // INDEX:        - AXI4_ERRS_RVALID_X
  // =====
  property AXI4_ERRS_RVALID_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(RVALID);
  endproperty
  axi4_errs_rvalid_x: assert property (AXI4_ERRS_RVALID_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RVALID_X);

`endif // AXI4_XCHECK_OFF

//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI4 Rules: Low Power Interface (*_C*)
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules (none for Low Power signals)
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules (asynchronous to ACLK)
// =====
// The low-power handshake rules below use rising/falling edges on REQ and ACK,
// in order to detect changes within ACLK cycles (including low power state).
//------------------------------------------------------------------------------


  // INDEX:        - AXI4_ERRL_CSYSACK_FALL
  // =====
  property AXI4_ERRL_CSYSACK_FALL;
    @(negedge CSYSACK) disable iff (~`AXI4_SVA_RSTn) // falling edge of CSYSACK
      !($isunknown(CSYSREQ))
      |-> ~CSYSREQ;                     // CSYSREQ low
  endproperty
  axi4_errl_csysack_fall: assert property (AXI4_ERRL_CSYSACK_FALL) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRL_CSYSACK_FALL);


  // INDEX:        - AXI4_ERRL_CSYSACK_RISE
  // =====
  property AXI4_ERRL_CSYSACK_RISE;
    @(posedge CSYSACK) disable iff (~`AXI4_SVA_RSTn) // rising edge of CSYSACK
      !($isunknown(CSYSREQ))
      |-> CSYSREQ;                      // CSYSREQ high
  endproperty
  axi4_errl_csysack_rise: assert property (AXI4_ERRL_CSYSACK_RISE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRL_CSYSACK_RISE);


  // INDEX:        - AXI4_ERRL_CSYSREQ_FALL
  // =====
  property AXI4_ERRL_CSYSREQ_FALL;
    @(negedge CSYSREQ) disable iff (~`AXI4_SVA_RSTn) // falling edge of CSYSREQ
      !($isunknown(CSYSACK))
      |-> CSYSACK;                      // CSYSACK high
  endproperty
  axi4_errl_csysreq_fall: assert property (AXI4_ERRL_CSYSREQ_FALL) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRL_CSYSREQ_FALL);


  // INDEX:        - AXI4_ERRL_CSYSREQ_RISE
  // =====
  property AXI4_ERRL_CSYSREQ_RISE;
    @(posedge CSYSREQ) disable iff (~`AXI4_SVA_RSTn) // rising edge of CSYSREQ
      !($isunknown(CSYSACK))
      |-> ~CSYSACK;                     // CSYSACK low
  endproperty
  axi4_errl_csysreq_rise: assert property (AXI4_ERRL_CSYSREQ_RISE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRL_CSYSREQ_RISE);

//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------

`ifdef AXI4_XCHECK_OFF
`else  // X-Checking on by default


  // INDEX:        - AXI4_ERRL_CACTIVE_X
  // =====
  property AXI4_ERRL_CACTIVE_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(CACTIVE);
  endproperty
  axi4_errl_cactive_x: assert property (AXI4_ERRL_CACTIVE_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRL_CACTIVE_X);


  // INDEX:        - AXI4_ERRL_CSYSACK_X
  // =====
  property AXI4_ERRL_CSYSACK_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(CSYSACK);
  endproperty
  axi4_errl_csysack_x: assert property (AXI4_ERRL_CSYSACK_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRL_CSYSACK_X);


  // INDEX:        - AXI4_ERRL_CSYSREQ_X
  // =====
  property AXI4_ERRL_CSYSREQ_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn
      |-> ! $isunknown(CSYSREQ);
  endproperty
  axi4_errl_csysreq_x: assert property (AXI4_ERRL_CSYSREQ_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRL_CSYSREQ_X);

`endif // AXI4_XCHECK_OFF

//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI Rules: Exclusive Access
// =====
// These are inter-channel rules.
// Supports one outstanding exclusive access per ID
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4_ERRM_EXCL_ALIGN
  // =====
  // Burst lengths that are not a power of two are not checked here, because
  // these will violate EXCLLEN. Checked for excl reads only as 
  // AXI4_RECM_EXCL_PAIR or AXI4_RECM_EXCL_MATCH will fire if an excl write 
  // violates.
  property AXI4_ERRM_EXCL_ALIGN;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARLOCK,ARLEN,ARADDR})) &
      (ARVALID &                                   // valid address
       (ARLOCK == `AXI4PC_ALOCK_EXCL) &            // exclusive transaction
       (ARLEN == `AXI4PC_ALEN_1 ||                 // length is power of 2
        ARLEN == `AXI4PC_ALEN_2 ||
        ARLEN == `AXI4PC_ALEN_4 ||
        ARLEN == `AXI4PC_ALEN_8 ||
        ARLEN == `AXI4PC_ALEN_16))
      |-> ((ARADDR[10:0] & ExclMask) == ARADDR[10:0]); // address aligned
  endproperty
  axi4_errm_excl_align: assert property (AXI4_ERRM_EXCL_ALIGN) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_EXCL_ALIGN);


  // INDEX:        - AXI4_ERRM_EXCL_LEN
  // =====
  // Checked for excl reads only as AXI4_RECM_EXCL_PAIR or AXI4_RECM_EXCL_MATCH
  // will fire if an excl write violates.
  property AXI4_ERRM_EXCL_LEN;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARLOCK,ARLEN})) &
      ARVALID & (ARLOCK == `AXI4PC_ALOCK_EXCL)
      |-> ((ARLEN == `AXI4PC_ALEN_1)  ||
           (ARLEN == `AXI4PC_ALEN_2)  ||
           (ARLEN == `AXI4PC_ALEN_4)  ||
           (ARLEN == `AXI4PC_ALEN_8)  ||
           (ARLEN == `AXI4PC_ALEN_16));
  endproperty
  axi4_errm_excl_len: assert property (AXI4_ERRM_EXCL_LEN) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_EXCL_LEN);


  // INDEX:        - AXI4_RECM_EXCL_MATCH
  // =====
  // Recommendation as it can be affected by software, e.g. if a dummy STREX is 
  // used to clear any outstanding exclusive accesses.
  // User and QOS removed as these may change
  property   AXI4_RECM_EXCL_MATCH;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({AWVALID,AWREADY,AWLOCK,ExclAwId,ExclAwMatch,AWADDR,AWSIZE,
      AWLEN,AWBURST,AWCACHE,AWPROT,AWREGION})) &
      RecommendOn &       // Parameter that can disable all AXI4_REC*_* rules
      AWVALID  &   // excl write & excl read outstanding
      (AWLOCK == `AXI4PC_ALOCK_EXCL) & ExclReadAddr[ExclAwId] 
      & ExclAwMatch
      |-> ((ExclAddr[ExclAwId]   == AWADDR)  &
           (ExclSize[ExclAwId]   == AWSIZE)  &
           (ExclLen[ExclAwId]    == AWLEN)   &
           (ExclBurst[ExclAwId]  == AWBURST) &
           (ExclCache[ExclAwId]  == AWCACHE) &
           (ExclProt[ExclAwId]   == AWPROT)  &
           (ExclRegion[ExclAwId] == AWREGION)
          );
  endproperty
  axi4_recm_excl_match: assert property (AXI4_RECM_EXCL_MATCH) else
   `ARM_AMBA4_PC_MSG_WARN(`RECM_EXCL_MATCH);


  // INDEX:        - AXI4_ERRM_EXCL_MAX
  // =====
  // Burst lengths that are not a power of two are not checked here, because
  // these will violate EXCLLEN. Bursts of length 1 can never violate this
  // rule. Checked for excl reads only as AXI4_RECM_EXCL_PAIR or 
  // AXI4_RECM_EXCL_MATCH will fire if an excl write violates.
  property AXI4_ERRM_EXCL_MAX;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARLOCK,ARLEN})) &
      (ARVALID &                         // valid address
       (ARLOCK == `AXI4PC_ALOCK_EXCL) &  // exclusive transaction
       (ARLEN == `AXI4PC_ALEN_2 ||       // length is power of 2
        ARLEN == `AXI4PC_ALEN_4 ||
        ARLEN == `AXI4PC_ALEN_8 ||
        ARLEN == `AXI4PC_ALEN_16))
      |-> (ArLenInBytes <= 128 );            // max 128 bytes transferred
  endproperty
  axi4_errm_excl_max: assert property (AXI4_ERRM_EXCL_MAX) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_EXCL_MAX);


  // INDEX:        - AXI4_RECM_EXCL_PAIR
  // =====
  // Recommendation as it can be affected by software, e.g. if a dummy STREX is 
  // used to clear any outstanding exclusive accesses.
  property   AXI4_RECM_EXCL_PAIR;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({AWVALID,AWREADY,AWLOCK,ExclAwMatch,ExclAwId})) &
      RecommendOn & // Parameter that can disable all AXI4_REC*_* rules
      AWVALID & (AWLOCK == `AXI4PC_ALOCK_EXCL) // excl write
      |-> (ExclAwMatch &&
      ExclReadAddr[ExclAwId] &&
      ExclReadData[ExclAwId]);               // excl read with same ID complete
  endproperty
  axi4_recm_excl_pair: assert property (AXI4_RECM_EXCL_PAIR) else
   `ARM_AMBA4_PC_MSG_WARN(`RECM_EXCL_PAIR);


  // INDEX:        - AXI4_RECM_EXCL_R_W
  // =====
  //Should not have conurrent exclusive reads and writes with the same ID
  property   AXI4_RECM_EXCL_R_W;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({AWVALID,AWLOCK,AWID,ARVALID,ARLOCK,ARID})) &
      RecommendOn & // Parameter that can disable all AXI4_REC*_* rules
      AWVALID & (AWLOCK == `AXI4PC_ALOCK_EXCL) && // excl write
      ARVALID & (ARLOCK == `AXI4PC_ALOCK_EXCL) // excl read
      |-> ARID != AWID;               //IDs not the same
  endproperty
  axi4_recm_excl_r_w: assert property (AXI4_RECM_EXCL_R_W) else
   `ARM_AMBA4_PC_MSG_WARN(`RECM_EXCL_R_W);

//------------------------------------------------------------------------------
// INDEX:
// INDEX: AXI4 Rules: USER_* Rules (extension to AXI4)
// =====
// The USER signals are user-defined extensions to the AXI4 spec, so have been
// located separately from the channel-specific rules.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Functional Rules (none for USER signals)
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   2) Handshake Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4_ERRM_AWUSER_STABLE
  // =====
  property AXI4_ERRM_AWUSER_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({AWVALID,AWREADY,AWUSER})) &
      `AXI4_SVA_RSTn & AWVALID & !AWREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(AWUSER);
  endproperty
  axi4_errm_awuser_stable: assert property (AXI4_ERRM_AWUSER_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWUSER_STABLE);


  // INDEX:        - AXI4_ERRM_WUSER_STABLE
  // =====
  property AXI4_ERRM_WUSER_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({WVALID,WREADY,WUSER})) &
      `AXI4_SVA_RSTn & WVALID & !WREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(WUSER);
  endproperty
  axi4_errm_wuser_stable: assert property (AXI4_ERRM_WUSER_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WUSER_STABLE);


  // INDEX:        - AXI4_ERRS_BUSER_STABLE
  // =====
  property AXI4_ERRS_BUSER_STABLE;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      !($isunknown({BVALID,BREADY,BUSER})) &
      `AXI4_SVA_RSTn & BVALID & !BREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(BUSER);
  endproperty
  axi4_errs_buser_stable: assert property (AXI4_ERRS_BUSER_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BUSER_STABLE);


  // INDEX:        - AXI4_ERRM_ARUSER_STABLE
  // =====
  property AXI4_ERRM_ARUSER_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({ARVALID,ARREADY,ARUSER})) &
      `AXI4_SVA_RSTn & ARVALID & !ARREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(ARUSER);
  endproperty
  axi4_errm_aruser_stable: assert property (AXI4_ERRM_ARUSER_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARUSER_STABLE);


  // INDEX:        - AXI4_ERRS_RUSER_STABLE
  // =====
  property AXI4_ERRS_RUSER_STABLE;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown({RVALID,RREADY,RUSER})) &
      `AXI4_SVA_RSTn & RVALID & !RREADY
      ##1 `AXI4_SVA_RSTn
      |-> $stable(RUSER);
  endproperty
  axi4_errs_ruser_stable: assert property (AXI4_ERRS_RUSER_STABLE) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RUSER_STABLE);

//------------------------------------------------------------------------------
// INDEX:   3) X-Propagation Rules
//------------------------------------------------------------------------------

`ifdef AXI4_XCHECK_OFF
`else  // X-Checking on by default

  // INDEX:        - AXI4_ERRM_AWUSER_X
  // =====
  property AXI4_ERRM_AWUSER_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & AWVALID
      |-> ! $isunknown(AWUSER);
  endproperty
  axi4_errm_awuser_x: assert property (AXI4_ERRM_AWUSER_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWUSER_X);


  // INDEX:        - AXI4_ERRM_WUSER_X
  // =====
  property AXI4_ERRM_WUSER_X;
    @(posedge `AXI4_SVA_CLK) 
      `AXI4_SVA_RSTn & WVALID
      |-> ! $isunknown(WUSER);
  endproperty
  axi4_errm_wuser_x: assert property (AXI4_ERRM_WUSER_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WUSER_X);


  // INDEX:        - AXI4_ERRS_BUSER_X
  // =====
  property AXI4_ERRS_BUSER_X;
    @(posedge `AXI4_SVA_CLK) disable iff (PROTOCOL != `AXI4PC_AMBA_AXI4)
      `AXI4_SVA_RSTn & BVALID
      |-> ! $isunknown(BUSER);
  endproperty
  axi4_errs_buser_x: assert property (AXI4_ERRS_BUSER_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BUSER_X);


  // INDEX:        - AXI4_ERRM_ARUSER_X
  // =====
  property AXI4_ERRM_ARUSER_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & ARVALID
      |-> ! $isunknown(ARUSER);
  endproperty
  axi4_errm_aruser_x: assert property (AXI4_ERRM_ARUSER_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARUSER_X);


  // INDEX:        - AXI4_ERRS_RUSER_X
  // =====
  property AXI4_ERRS_RUSER_X;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & RVALID
      |-> ! $isunknown(RUSER);
  endproperty
  axi4_errs_ruser_x: assert property (AXI4_ERRS_RUSER_X) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RUSER_X);

`endif // AXI4_XCHECK_OFF

//------------------------------------------------------------------------------
// INDEX:   4) Zero Width Stability Rules
//------------------------------------------------------------------------------

  // INDEX:        - AXI4_ERRM_AWUSER_TIEOFF
  // =====
  property AXI4_ERRM_AWUSER_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(AWUSER)) &
      `AXI4_SVA_RSTn &
      (AWUSER_WIDTH == 0)
      |-> $stable(AWUSER);
  endproperty
  axi4_errm_awuser_tieoff: assert property (AXI4_ERRM_AWUSER_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWUSER_TIEOFF);


  // INDEX:        - AXI4_ERRM_WUSER_TIEOFF
  // =====
  property AXI4_ERRM_WUSER_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(WUSER)) &
      `AXI4_SVA_RSTn &
      (WUSER_WIDTH == 0)
      |-> $stable(WUSER);
  endproperty
  axi4_errm_wuser_tieoff: assert property (AXI4_ERRM_WUSER_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_WUSER_TIEOFF);


  // INDEX:        - AXI4_ERRS_BUSER_TIEOFF
  // =====
  property AXI4_ERRS_BUSER_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(BUSER)) &
      `AXI4_SVA_RSTn &
      (BUSER_WIDTH == 0)
      |-> $stable(BUSER);
  endproperty
  axi4_errs_buser_tieoff: assert property (AXI4_ERRS_BUSER_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BUSER_TIEOFF);


  // INDEX:        - AXI4_ERRM_ARUSER_TIEOFF
  // =====
  property AXI4_ERRM_ARUSER_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(ARUSER)) &
      `AXI4_SVA_RSTn &
      (ARUSER_WIDTH == 0)
      |-> $stable(ARUSER);
  endproperty
  axi4_errm_aruser_tieoff: assert property (AXI4_ERRM_ARUSER_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARUSER_TIEOFF);


  // INDEX:        - AXI4_ERRS_RUSER_TIEOFF
  // =====
  property AXI4_ERRS_RUSER_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(RUSER)) &
      `AXI4_SVA_RSTn &
      (RUSER_WIDTH == 0)
      |-> $stable(RUSER);
  endproperty
  axi4_errs_ruser_tieoff: assert property (AXI4_ERRS_RUSER_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RUSER_TIEOFF);


  // INDEX:        - AXI4_ERRM_AWID_TIEOFF
  // =====
  property AXI4_ERRM_AWID_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(AWID)) &
      `AXI4_SVA_RSTn &
      (WID_WIDTH == 0)
      |-> $stable(AWID);
  endproperty
  axi4_errm_awid_tieoff: assert property (AXI4_ERRM_AWID_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_AWID_TIEOFF);


  // INDEX:        - AXI4_ERRS_BID_TIEOFF
  // =====
  property AXI4_ERRS_BID_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(BID)) &
      `AXI4_SVA_RSTn &
      (WID_WIDTH == 0)
      |-> $stable(BID);
  endproperty
  axi4_errs_bid_tieoff: assert property (AXI4_ERRS_BID_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BID_TIEOFF);


  // INDEX:        - AXI4_ERRM_ARID_TIEOFF
  // =====
  property AXI4_ERRM_ARID_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(ARID)) &
      `AXI4_SVA_RSTn &
      (RID_WIDTH == 0)
      |-> $stable(ARID);
  endproperty
  axi4_errm_arid_tieoff: assert property (AXI4_ERRM_ARID_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRM_ARID_TIEOFF);

  
  // INDEX:        - AXI4_ERRS_RID_TIEOFF
  // =====
  property AXI4_ERRS_RID_TIEOFF;
    @(posedge `AXI4_SVA_CLK)
      !($isunknown(RID)) &
      `AXI4_SVA_RSTn &
      (RID_WIDTH == 0)
      |-> $stable(RID);
  endproperty
  axi4_errs_rid_tieoff: assert property (AXI4_ERRS_RID_TIEOFF) else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RID_TIEOFF);

 //------------------------------------------------------------------------------
// INDEX:   5) EOS checks
//------------------------------------------------------------------------------
final
begin
  `ifndef AXI4PC_EOS_OFF
  $display ("Executing Axi4 End Of Simulation checks");

  // INDEX:        - AXI4_ERRS_BRESP_ALL_DONE_EOS
  // =====
  //property AXI4_ERRS_BRESP_ALL_DONE_EOS;
  axi4_errs_bresp_all_done_eos: 
  assert (WIndex == 1)
  else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_BRESP_ALL_DONE_EOS);
 
  // INDEX:        - AXI4_ERRS_RLAST_ALL_DONE_EOS
  // =====
  //property AXI4_ERRS_RLAST_ALL_DONE_EOS;
  axi4_errs_rlast_all_done_eos:
   assert (nROutstanding == 1'b1)
   else
   `ARM_AMBA4_PC_MSG_ERR(`ERRS_RLAST_ALL_DONE_EOS);


  `endif
end
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
// INDEX:
// INDEX: Auxiliary Logic
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// INDEX:   1) Rules for Auxiliary Logic
//------------------------------------------------------------------------------

  //----------------------------------------------------------------------------
  // INDEX:      a) Master (AUX*)
  //----------------------------------------------------------------------------

  // INDEX:        - AXI4_AUX_DATA_WIDTH
  // =====
  property AXI4_AUX_DATA_WIDTH;
    @(posedge `AXI4_SVA_CLK)
      (DATA_WIDTH ==   32 ||
       DATA_WIDTH ==   64 ||
       DATA_WIDTH ==  128 ||
       DATA_WIDTH ==  256 ||
       DATA_WIDTH ==  512 ||
       DATA_WIDTH == 1024);
  endproperty
  axi4_aux_data_width: assert property (AXI4_AUX_DATA_WIDTH) else
   `ARM_AMBA4_PC_MSG_ERR(`AUX_DATA_WIDTH);


  // INDEX:        - AXI4_AUX_ADDR_WIDTH
  // =====
  property AXI4_AUX_ADDR_WIDTH;
    @(posedge `AXI4_SVA_CLK)
      (ADDR_WIDTH >= 32 && ADDR_WIDTH <= 64);
  endproperty
  axi4_aux_addr_width: assert property (AXI4_AUX_ADDR_WIDTH) else
   `ARM_AMBA4_PC_MSG_ERR(`AUX_ADDR_WIDTH);


  // INDEX:        - AXI4_AUX_EXMON_WIDTH
  // =====
  property AXI4_AUX_EXMON_WIDTH;
    @(posedge `AXI4_SVA_CLK)
      (EXMON_WIDTH >= 1);
  endproperty
  axi4_aux_exmon_width: assert property (AXI4_AUX_EXMON_WIDTH) else
   `ARM_AMBA4_PC_MSG_ERR(`AUX_EXMON_WIDTH);


  // INDEX:        - AXI4_AUX_MAXRBURSTS
  // =====
  property AXI4_AUX_MAXRBURSTS;
    @(posedge `AXI4_SVA_CLK)
      (MAXRBURSTS >= 1);
  endproperty
  axi4_aux_maxrbursts: assert property (AXI4_AUX_MAXRBURSTS) else
   `ARM_AMBA4_PC_MSG_ERR(`AUX_MAXRBURSTS);


  // INDEX:        - AXI4_AUX_MAXWBURSTS
  // =====
  property AXI4_AUX_MAXWBURSTS;
    @(posedge `AXI4_SVA_CLK)
      (MAXWBURSTS >= 1);
  endproperty
  axi4_aux_maxwbursts: assert property (AXI4_AUX_MAXWBURSTS) else
   `ARM_AMBA4_PC_MSG_ERR(`AUX_MAXWBURSTS);


  // INDEX:        - AXI4_AUX_RCAM_OVERFLOW
  // =====
  property AXI4_AUX_RCAM_OVERFLOW;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown(RIndex))
      |-> (RIndex <= (MAXRBURSTS+1));
  endproperty
  axi4_aux_rcam_overflow: assert property (AXI4_AUX_RCAM_OVERFLOW) else
    `ARM_AMBA4_PC_MSG_ERR(`AUX_RCAM_OVERFLOW);


  // INDEX:        - AXI4_AUX_RCAM_UNDERFLOW
  // =====
  property AXI4_AUX_RCAM_UNDERFLOW;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown(RIndex))
      |-> (RIndex > 0);
  endproperty
  axi4_aux_rcam_underflow: assert property (AXI4_AUX_RCAM_UNDERFLOW) else
   `ARM_AMBA4_PC_MSG_ERR(`AUX_RCAM_UNDERFLOW);


  // INDEX:        - AXI4_AUX_WCAM_OVERFLOW
  // =====
  property AXI4_AUX_WCAM_OVERFLOW;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown(WIndex))
      |-> (WIndex <= (MAXWBURSTS+1));
  endproperty
  axi4_aux_wcam_overflow: assert property (AXI4_AUX_WCAM_OVERFLOW) else
   `ARM_AMBA4_PC_MSG_ERR(`AUX_WCAM_OVERFLOW);


  // INDEX:        - AXI4_AUX_WCAM_UNDERFLOW
  // =====
  property AXI4_AUX_WCAM_UNDERFLOW;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown(WIndex))
      |-> (WIndex > 0);
  endproperty
  axi4_aux_wcam_underflow: assert property (AXI4_AUX_WCAM_UNDERFLOW) else
   `ARM_AMBA4_PC_MSG_ERR(`AUX_WCAM_UNDERFLOW);


  // INDEX:        - AXI4_AUX_EXCL_OVERFLOW
  // =====
  property AXI4_AUX_EXCL_OVERFLOW;
    @(posedge `AXI4_SVA_CLK)
      `AXI4_SVA_RSTn & !($isunknown(ExclIdOverflow))
      |-> (!ExclIdOverflow);
  endproperty
  axi4_aux_excl_overflow: assert property (AXI4_AUX_EXCL_OVERFLOW) else
   `ARM_AMBA4_PC_MSG_ERR(`AUX_EXCL_OVERFLOW);

//------------------------------------------------------------------------------
// INDEX:   2) Combinatorial Logic
//------------------------------------------------------------------------------

  //----------------------------------------------------------------------------
  // INDEX:      a) Masks
  //----------------------------------------------------------------------------

  // INDEX:           - AlignMaskR
  // =====
  // Calculate wrap mask for read address
  always @(ARSIZE or ARVALID)
  begin
    if (ARVALID)
      case (ARSIZE)
        `AXI4PC_ASIZE_1024:  AlignMaskR = 7'b0000000;
        `AXI4PC_ASIZE_512:   AlignMaskR = 7'b1000000;
        `AXI4PC_ASIZE_256:   AlignMaskR = 7'b1100000;
        `AXI4PC_ASIZE_128:   AlignMaskR = 7'b1110000;
        `AXI4PC_ASIZE_64:    AlignMaskR = 7'b1111000;
        `AXI4PC_ASIZE_32:    AlignMaskR = 7'b1111100;
        `AXI4PC_ASIZE_16:    AlignMaskR = 7'b1111110;
        `AXI4PC_ASIZE_8:     AlignMaskR = 7'b1111111;
        default:             AlignMaskR = 7'b1111111;
      endcase
    else
      AlignMaskR = 7'b1111111;
  end


  // INDEX:           - AlignMaskW
  // =====
  // Calculate wrap mask for write address
  always @(AWSIZE or AWVALID)
  begin
    if (AWVALID)
      case (AWSIZE)
        `AXI4PC_ASIZE_1024:  AlignMaskW = 7'b0000000;
        `AXI4PC_ASIZE_512:   AlignMaskW = 7'b1000000;
        `AXI4PC_ASIZE_256:   AlignMaskW = 7'b1100000;
        `AXI4PC_ASIZE_128:   AlignMaskW = 7'b1110000;
        `AXI4PC_ASIZE_64:    AlignMaskW = 7'b1111000;
        `AXI4PC_ASIZE_32:    AlignMaskW = 7'b1111100;
        `AXI4PC_ASIZE_16:    AlignMaskW = 7'b1111110;
        `AXI4PC_ASIZE_8:     AlignMaskW = 7'b1111111;
        default:             AlignMaskW = 7'b1111111;
      endcase // case(AWSIZE)
    else
      AlignMaskW = 7'b1111111;
  end


  // INDEX:           - ExclMask
  // =====
  always @(ARLEN or ARSIZE)
  begin : p_ExclMaskComb
    ExclMask = ~((({7'b000_0000, ARLEN} + 15'b000_0000_0000_0001) << ARSIZE) - 15'b000_0000_0000_0001);
  end // block: p_ExclMaskComb


  // INDEX:           - WdataMask
  // =====
  always @(WSTRB)
  begin : p_WdataMaskComb
    integer i;  // data byte loop counter
    integer j;  // data bit loop counter

    for (i = 0; i < STRB_WIDTH; i = i + 1)
      for (j = i * 8; j <= (i * 8) + 7; j = j + 1)
        WdataMask[j] = WSTRB[i];
  end


  // INDEX:           - RdataMask
  // =====
  assign RdataMask = ReadDataMask(RBurstCam[RidMatch], RCountCam[RidMatch]);


  //----------------------------------------------------------------------------
  // INDEX:      b) Increments
  //----------------------------------------------------------------------------

  // INDEX:           - ArAddrIncr
  // =====
  always @(ARSIZE or ARLEN or ARADDR)
  begin : p_RAddrIncrComb
    ArAddrIncr = ARADDR + (ARLEN << ARSIZE);  // The final address of the burst
  end


  // INDEX:           - AwAddrIncr
  // =====
  always @(AWSIZE or AWLEN or AWADDR)
  begin : p_WAddrIncrComb
    AwAddrIncr = AWADDR + (AWLEN << AWSIZE);  // The final address of the burst
  end


  //----------------------------------------------------------------------------
  // INDEX:      c) Conversions
  //----------------------------------------------------------------------------

  // INDEX:           - ArLenInBytes
  // =====
  always @(ARSIZE or ARLEN)
  begin : p_ArLenInBytes
    // bytes = (ARLEN+1) data transfers x ARSIZE bytes
    ArLenInBytes = (({8'h00, ARLEN} + 16'h001) << ARSIZE); 
  end


  // INDEX:           - ArSizeInBits
  // =====
  always @(ARSIZE)
  begin : p_ArSizeInBits
    ArSizeInBits = (11'b000_0000_1000 << ARSIZE); // bits = 8 x ARSIZE bytes
  end


  // INDEX:           - AwSizeInBits
  // =====
  always @(AWSIZE)
  begin : p_AwSizeInBits
    AwSizeInBits = (11'b000_0000_1000 << AWSIZE); // bits = 8 x AWSIZE bytes
  end


  //----------------------------------------------------------------------------
  // INDEX:      d) Other
  //----------------------------------------------------------------------------

  // INDEX:           - ArExclPending
  // =====
  // Avoid putting on assertion directly as index is an integer
  assign ArExclPending = RBurstCam[RidMatch][EXCL];


  // INDEX:           - ArLenPending
  // =====
  // Avoid putting on assertion directly as index is an integer
  assign ArLenPending = {1'b0, RBurstCam[RidMatch][ALENHI:ALENLO]};

  // INDEX:           - ArCountPending
  // =====
  // Avoid putting on assertion directly as index is an integer
  assign ArCountPending = RCountCam[RidMatch];

//------------------------------------------------------------------------------
// INDEX:   3) EXCL Accesses
//------------------------------------------------------------------------------

  // INDEX:        - Exclusive Access ID Lookup
  // =====
  // Map transaction IDs to the available exclusive access storage locations

  // Lookup table for IDs used by the exclusive access monitor
  // Each location in the table has a valid flag to indicate if the ID is in use
  // The location of an ID flagged as valid is used as a virtual ID in the
  // exclusive access monitor checks
  always @(negedge `AXI4_AUX_RSTn or posedge `AXI4_AUX_CLK)
  begin : p_ExclIdSeq
    integer i;  // loop counter
    if (!`AXI4_AUX_RSTn)
    begin
      ExclIdValid <= {EXMON_HI+1{1'b0}};
      ExclIdDelta <= 1'b0;
      for (i = 0; i <= EXMON_HI; i = i + 1)
      begin
        ExclId[i] <= {ID_MAX+1{1'b0}};
      end
    end
    else // clk edge
    begin
      // The write conditions need to be done first. If there is
      // a simultaneous read and write then the read condition must succeed.
      // exclusive write
      if (AWVALID && AWREADY && (AWLOCK == `AXI4PC_ALOCK_EXCL) &&
          ExclAwMatch)
      begin
        ExclIdValid[ExclAwId] <= 1'b0;
        ExclIdDelta <= ~ExclIdDelta;
      end
      // exclusive read address transfer
      if (ARVALID && ARREADY && (ARLOCK == `AXI4PC_ALOCK_EXCL) &&
          !ExclIdFull)
      begin
        ExclId[ExclIdWrPtr] <= ARID;
        ExclIdValid[ExclIdWrPtr] <= 1'b1;
        ExclIdDelta <= ~ExclIdDelta;
      end
    end // else: !if(!`AXI4_AUX_RSTn)
  end // block: p_ExclIdSeq

  // Lookup table is full when all valid bits are set
  assign ExclIdFull = &ExclIdValid;

  // Lookup table overflows when it is full and another exclusive read happens
  // with an ID that does not match any already being monitored
  assign ExclIdOverflow = ExclIdFull &&
                          ARVALID && ARREADY && (ARLOCK == `AXI4PC_ALOCK_EXCL) &&
                          !ExclArMatch;

  // New IDs are written to the highest location
  // that does not have the valid flag set 
  always @(ExclIdValid or ExclIdDelta)
  begin : p_ExclIdFreePtrComb
    integer i;  // loop counter
    ExclIdFreePtr = '0;
    for (i = 0; i <= EXMON_HI; i = i + 1)
    begin
      if (ExclIdValid[i] == 1'b0)
      begin
        ExclIdFreePtr = i;
      end
    end
  end // p_ExclIdFreePtrComb

  // If the ID is already being monitored then reuse the location
  // New IDs are written to the highest location
  // that does not have the valid flag set 
  assign ExclIdWrPtr = ExclArMatch ? ExclArId : ExclIdFreePtr;

  // Write address ID comparator
  always @(AWVALID or AWID or ExclIdValid or ExclIdDelta)
  begin : p_ExclAwMatchComb
    integer i;  // loop counter
    ExclAwMatch = 1'b0;
    ExclAwId = {EXMON_WIDTH{1'b0}};
    if (AWVALID)
    begin
      for (i = 0; i <= EXMON_HI; i = i + 1)
      begin
        if (ExclIdValid[i] && (AWID == ExclId[i]))
        begin
          ExclAwMatch = 1'b1;
          ExclAwId = i;
        end
      end
    end
  end // p_ExclAwMatchComb

  // Read address ID comparator
  always @(ARVALID or ARID or ExclIdValid or ExclIdDelta)
  begin : p_ExclArMatchComb
    integer i;  // loop counter
    ExclArMatch = 1'b0;
    ExclArId = {EXMON_WIDTH{1'b0}};
    if (ARVALID)
    begin
      for (i = 0; i <= EXMON_HI; i = i + 1)
      begin
        if (ExclIdValid[i] && (ARID == ExclId[i]))
        begin
          ExclArMatch = 1'b1;
          ExclArId = i;
        end
      end
    end
  end // p_ExclArMatchComb

  // Read data ID comparator
  always @(RVALID or RID or ExclIdValid or ExclIdDelta)
  begin : p_ExclRMatchComb
    integer i;  // loop counter
    ExclRMatch = 1'b0;
    ExclRId = {EXMON_WIDTH{1'b0}};
    if (RVALID)
    begin
      for (i = 0; i <= EXMON_HI; i = i + 1)
      begin
        if (ExclIdValid[i] && (RID == ExclId[i]))
        begin
          ExclRMatch = 1'b1;
          ExclRId = i;
        end
      end
    end
  end // p_ExclRMatchComb

  // INDEX:        - Exclusive Access Storage
  // =====
  // Store exclusive control info on each read for checking against write

  always @(negedge `AXI4_AUX_RSTn or posedge `AXI4_AUX_CLK)
  begin : p_ExclCtrlSeq
    integer i;  // loop counter

    if (!`AXI4_AUX_RSTn)
      for (i = 0; i <= EXMON_HI; i = i + 1)
      begin
        ExclReadAddr[i] <= 1'b0;
        ExclReadData[i] <= 1'b0;
        ExclAddr[i]     <= {ADDR_WIDTH{1'b0}};
        ExclSize[i]     <= 3'b000;
        ExclLen[i]      <= {8{1'b0}};
        ExclBurst[i]    <= 2'b00;
        ExclCache[i]    <= {4{1'b0}};
        ExclProt[i]     <= {3{1'b0}};
        ExclQos[i]      <= {4{1'b0}};
        ExclRegion[i]   <= {4{1'b0}};
        ExclUser[i]     <= {ARUSER_MAX+1{1'b0}};
      end
    else // clk edge
    begin
      // The write conditions need to be done first. If there is
      // a simultaneous read and write then the read condition must succeed.
      // exclusive write
      if (AWVALID && AWREADY && (AWLOCK == `AXI4PC_ALOCK_EXCL) &&
          ExclAwMatch)
      begin
        ExclReadAddr[ExclAwId] <= 1'b0; // reset exclusive address flag for AWID
        ExclReadData[ExclAwId] <= 1'b0; // reset exclusive read data flag for AWID
      end
      // completion of exclusive read data transaction
      if ((RVALID && RREADY && RLAST && ExclReadAddr[ExclRId] &&
           ExclRMatch) &&
           // check the read CAM that this is part of an exclusive transfer 
           RBurstCam[RidMatch][EXCL] 
         )
        ExclReadData[ExclRId]  <= (RRESP == `AXI4PC_RESP_EXOKAY); // set exclusive read data flag for RID
      // exclusive read address transfer
      if (ARVALID && ARREADY && (ARLOCK == `AXI4PC_ALOCK_EXCL) &&
          (!ExclIdFull || ExclArMatch) )
      begin
        ExclReadAddr[ExclIdWrPtr] <= 1'b1; // set exclusive read addr flag for ARID
        ExclReadData[ExclIdWrPtr] <= 1'b0; // reset exclusive read data flag for ARID
        ExclAddr[ExclIdWrPtr]     <= ARADDR;
        ExclSize[ExclIdWrPtr]     <= ARSIZE;
        ExclLen[ExclIdWrPtr]      <= ARLEN;
        ExclBurst[ExclIdWrPtr]    <= ARBURST;
        ExclCache[ExclIdWrPtr]    <= ARCACHE;
        ExclProt[ExclIdWrPtr]     <= ARPROT;
        ExclQos[ExclIdWrPtr]      <= ARQOS;
        ExclRegion[ExclIdWrPtr]   <= ARREGION;
        ExclUser[ExclIdWrPtr]     <= ARUSER;
      end
    end // else: !if(!`AXI4_AUX_RSTn)
  end // block: p_ExclCtrlSeq

//------------------------------------------------------------------------------
// INDEX:   4) Content addressable memories (CAMs)
//------------------------------------------------------------------------------

  // INDEX:        - Read CAMSs (CAM+Shift)
  // =====
  // New entries are added at the end of the CAM.
  // Elements may be removed from any location in the CAM, determined by the
  // first matching RID. When an element is removed, remaining elements
  // with a higher index are shifted down to fill the empty space.

  // Read CAMs store all outstanding addresses for read transactions
  assign RPush  = ARVALID & ARREADY;        // Push on address handshake
  assign RPop   = RVALID & RREADY & RLAST;  // Pop on last handshake

  // Flag when there are no outstanding read transactions
  assign nROutstanding = (RIndex == 1);

  // Find the index of the first item in the CAM that matches the current RID
  // (Note that RIdCamDelta is used to determine when RIdCam has changed)
  always @(RID or RIndex or RIdCamDelta)
  begin : p_RidMatch
    integer i;  // loop counter
    RidMatch = '0;
    for (i=MAXRBURSTS; i>0; i=i-1)
      if ((i < RIndex) && (RID == RBurstCam[i][IDHI:IDLO]))
        RidMatch = i;
  end

  // Calculate the index of the next free element in the CAM
  always @(RIndex or RPop or RPush)
  begin : p_RIndexNextComb
    case ({RPush,RPop})
      2'b00   : RIndexNext = RIndex;      // no push, no pop
      2'b01   : RIndexNext = RIndex - 1;  // pop, no push
      2'b10   : RIndexNext = RIndex + 1;  // push, no pop
      2'b11   : RIndexNext = RIndex;      // push and pop
      default : RIndexNext = 'bX;         // X-propagation
    endcase
  end
  
  // RIndex Register
  always @(negedge `AXI4_AUX_RSTn or posedge `AXI4_AUX_CLK)
  begin : p_RIndexSeq
    if (!`AXI4_AUX_RSTn)
      RIndex <= 1;
    else
      RIndex <= RIndexNext;
  end
  
  // CAM Implementation
  always @(negedge `AXI4_AUX_RSTn or posedge `AXI4_AUX_CLK)
  begin : p_ReadCam
    reg [RBURSTMAX:0] Burst; // temporary store for burst data structure
    if (!`AXI4_AUX_RSTn)
    begin : p_ReadCamReset
      integer i;  // loop counter
      // Reset all the entries in the CAM
      for (i=1; i<=MAXRBURSTS; i=i+1)
      begin
        RBurstCam[i] <= {RBURSTMAX+1{1'b0}};
        RCountCam[i] <= 9'h0;
        RIdCamDelta  <= 1'b0;
      end //for (i=1; i<=MAXBURSTS; i=i+1)
    end //p_ReadCamReset 
    else
    begin

      // Pop item from the CAM, at location determined by RidMatch
      if (RPop)
      begin : p_ReadCamPop
        integer i;  // loop counter
        for (i=1; i<MAXRBURSTS; i=i+1)
          if (i >= RidMatch)
          begin
              RBurstCam[i] <= RBurstCam[i+1];
              RCountCam[i] <= RCountCam[i+1];
              RIdCamDelta  <= ~RIdCamDelta;
          end //for (i=1; i<MAXRBURSTS; i=i+1)
      end //p_ReadCamPop
      else if (RVALID & RREADY)
      // if not last data item, increment beat count
      begin
        RCountCam[RidMatch] <= RCountCam[RidMatch] + 9'b0_0000_0001;
      end

      if (ARVALID)
      begin
          Burst[ADDRHI:ADDRLO]   = ARADDR[ADDRHI:ADDRLO];
          Burst[EXCL]            = (ARLOCK == `AXI4PC_ALOCK_EXCL);
          Burst[BURSTHI:BURSTLO] = ARBURST;
          Burst[ALENHI:ALENLO]   = ARLEN;
          Burst[ASIZEHI:ASIZELO] = ARSIZE;
          Burst[IDHI:IDLO]       = ARID;

          // Push item at end of the CAM
          // Note that the value of the final index in the CAM is depends on
          // whether another item has been popped
          if (RPush)
          begin
            if (RPop)
            begin
              RBurstCam[RIndex-1] <= Burst;
              RCountCam[RIndex-1] <= 9'h00;
            end
            else
            begin
              RBurstCam[RIndex]   <= Burst;
              RCountCam[RIndex]   <= 9'h00;
            end // else: !if(RPop)
            RIdCamDelta <= ~RIdCamDelta;
          end // if (RPush)
      end // if (ARVALID)
    end // else: if(!`AXI4_AUX_RSTn)
  end // always @(negedge `AXI4_AUX_RSTn or posedge `AXI4_AUX_CLK)


  always @(*)
  begin : p_AIDMatch
    integer i;  // loop counter
    AIDMatch = WIndex;
    for (i=MAXWBURSTS; i>0 ; i=i-1)
      if (i < WIndex)                  // only consider valid entries in WBurstCam
      begin
        if (~WAddrCam[i])              // write address not already transferred
          AIDMatch = i;
      end
  end


  always @(*)
  begin : p_WIDMatch
    integer i;  // loop counter
    WIDMatch = WIndex;
    for (i=MAXWBURSTS; i>0 ; i=i-1)
      if ((i < WIndex) && ~WLastCam[i] )
        WIDMatch = i ;
  end
  assign WIDMatch_next = (AwPop && (BIDMatch < WIDMatch)) ? WIDMatch -1 : WIDMatch;
  assign AIDMatch_next = (AwPop && (BIDMatch < AIDMatch)) ? AIDMatch -1 : AIDMatch;


  // Find the index of the first item in the CAM that matches the current BID
  // that has seen WLAST
  always @(*)
  begin : p_BIDMatch
    integer i;  // loop counter
    BIDMatch = WIndex;
    for (i=MAXWBURSTS; i>0 ; i=i-1)
      if (i < WIndex) 
      begin
        if (BID == WBurstCam[i][IDHI:IDLO] && ~BRespCam[i])  
        begin
          BIDMatch = i;
        end
      end
  end

  //
  // assert protocol error flag if address received after leading write
  // data and:
  // - WLAST was asserted when the beat count is less than AWLEN
  // - WLAST was not asserted when the beat count is equal to AWLEN
  // - the beat count is greater than AWLEN
  //always @(*)
  always @(AWVALID or CurrentAWInfo or WLastCam[AIDMatch] or WCountCam[AIDMatch] or AIDMatch or AWLEN or WLAST or WVALID or WIDMatch)
  begin : p_AWDataNumError
    if (AWVALID)
    begin
      if ((WLastCam[AIDMatch] & 
      (({1'b0, AWLEN} + 9'b000000001) > WCountCam[AIDMatch]))
      ||
      (WVALID & WLAST && (WCountCam[AIDMatch] < AWLEN) & (AIDMatch == WIDMatch)) )
      begin
        AWDataNumError1 = 1'b1;
      end
      else
      begin
          AWDataNumError1 = 1'b0;
      end
      
      if ((~WLastCam[AIDMatch] & 
        (({1'b0, AWLEN} + 9'b000000001) == WCountCam[AIDMatch]))
         ||
         (WVALID & ~WLAST & (WCountCam[AIDMatch] == AWLEN) & (AIDMatch == WIDMatch)))
      begin
        AWDataNumError2 = 1'b1;
      end
      else
      begin
          AWDataNumError2 = 1'b0;
      end
      
      if (({1'b0, AWLEN} + 9'b000000001) < WCountCam[AIDMatch])
      begin
        AWDataNumError3 = 1'b1;
      end
      else
      begin
          AWDataNumError3 = 1'b0;
      end
    end
    else
    begin
        AWDataNumError1 = 1'b0;
        AWDataNumError2 = 1'b0;
        AWDataNumError3 = 1'b0;
    end
  end


  // if last data item or correct number of data items received already,
  // check number of data items and WLAST against AWLEN.
  // WCountCam hasn't yet incremented so can be compared with AWLEN
  always @(WVALID or WLAST or WAddrCam[WIDMatch] or WCountCam[WIDMatch] or CurrentWInfo or WIDMatch)
  begin : p_WDataNumError
    if (WVALID  )
    begin
      if   (WAddrCam[WIDMatch] &       // Only perform test if address is known
            ( (WLAST & (WCountCam[WIDMatch] != {1'b0,CurrentWInfo[ALENHI:ALENLO]}))) )
      begin
        WDataNumError1 = 1'b1;
      end
      else
      begin
        WDataNumError1 = 1'b0;
      end
      if  ( WAddrCam[WIDMatch] &       // Only perform test if address is known
              (~WLAST & (WCountCam[WIDMatch] == {1'b0,CurrentWInfo[ALENHI:ALENLO]})))
      begin
        WDataNumError2 = 1'b1;
      end
      //else if (AWVALID & (AIDMatch == WIDMatch) & ~WLAST & (WCountCam[WIDMatch] == AWLEN))
      else
      begin
        WDataNumError2 = 1'b0;
      end
    end
    else
    begin
      WDataNumError1 = 1'b0;
      WDataNumError2 = 1'b0;
    end
  end
  // INDEX:        - Write CAMs (CAM+Shift)
  // =====
  // New entries are added at the end of the CAM.
  // Elements may be removed from any location in the CAM, determined by the
  // first matching WID and/or BID. When an element is removed, remaining
  // elements with a higher index are shifted down to fill the empty space.

  assign AwPop = BVALID && BREADY ;

  // Write bursts stored in single structure for checking when complete.
  // This avoids the problem of early write data.
  always @(negedge `AXI4_AUX_RSTn or posedge `AXI4_AUX_CLK)
  begin : p_WriteCam
    reg [WBURSTMAX:0] Burst; // temporary store for burst data structure
    integer i;               // loop counter
    if (!`AXI4_AUX_RSTn)
    begin : p_WriteCamReset
      for (i=1; i<=MAXWBURSTS; i=i+1)
      begin
        WBurstCam[i]   <= {WBURSTMAX+1{1'b0}}; // initialise to zero on reset
        WCountCam[i]   <= 9'b0;                // initialise beat counters to zero
        WLastCam[i]    <= 1'b0;
        WAddrCam[i]    <= 1'b0;
        BRespCam[i]    <= 1'b0;
      end

      WIndex   = 1;
      Burst    = {WBURSTMAX+1{1'b0}};
   end
    else
    begin

      // -----------------------------------------------------------------------
      // Valid write response
      if (BVALID)
      begin


        Burst = WBurstCam[BIDMatch];         // set temporary burst signal
        BRespCam[BIDMatch] <= BREADY;         // record if write response completed

          // Write response handshake completes burst when write address has
          // already been received, and triggers protocol checking
          // WlastCam added for AXI4. 
          if ((BREADY & WAddrCam[BIDMatch]) & (WLastCam[BIDMatch]) )
          begin : p_WriteCamPopB
            // pop completed burst from CAM
            for (i = 1; i < MAXWBURSTS; i = i+1)
            begin
              if (i >= BIDMatch)             // only shift items after popped burst
              begin
                WBurstCam[i]    <= WBurstCam[i+1];
                WCountCam[i]    <= WCountCam[i+1];
                WLastCam[i]     <= WLastCam[i+1];
                WAddrCam[i]     <= WAddrCam[i+1];
                BRespCam[i]     <= BRespCam[i+1];
              end
            end

            WIndex = WIndex - 1;             // decrement index

            // Reset flags on new empty element
            WBurstCam[WIndex]    <= {WBURSTMAX+1{1'b0}};
            WCountCam[WIndex]    <= 9'b0;
            WLastCam[WIndex]     <= 1'b0;
            WAddrCam[WIndex]     <= 1'b0;
            BRespCam[WIndex]     <= 1'b0;

          //end // if (BREADY & WAddrCam[BIDMatch])

        end // else !(~(BIDMatch < WIndex))
      end // if (BVALID)



      // -----------------------------------------------------------------------
      // Valid write data
      if (WVALID)
      begin : p_WriteCamWValid


        Burst = WBurstCam[WIDMatch];         // temp store for 2-D burst lookup


        // need to use full case statement to occupy WSTRB as in Verilog the
        // bit slice range must be bounded by constant expressions
        case (WCountCam[WIDMatch])
          9'h0 : Burst[STRB1HI:STRB1LO]     = WSTRB;
          9'h1 : Burst[STRB2HI:STRB2LO]     = WSTRB;
          9'h2 : Burst[STRB3HI:STRB3LO]     = WSTRB;
          9'h3 : Burst[STRB4HI:STRB4LO]     = WSTRB;
          9'h4 : Burst[STRB5HI:STRB5LO]     = WSTRB;
          9'h5 : Burst[STRB6HI:STRB6LO]     = WSTRB;
          9'h6 : Burst[STRB7HI:STRB7LO]     = WSTRB;
          9'h7 : Burst[STRB8HI:STRB8LO]     = WSTRB;
          9'h8 : Burst[STRB9HI:STRB9LO]     = WSTRB;
          9'h9 : Burst[STRB10HI:STRB10LO]   = WSTRB;
          9'hA : Burst[STRB11HI:STRB11LO]   = WSTRB;
          9'hB : Burst[STRB12HI:STRB12LO]   = WSTRB;
          9'hC : Burst[STRB13HI:STRB13LO]   = WSTRB;
          9'hD : Burst[STRB14HI:STRB14LO]   = WSTRB;
          9'hE : Burst[STRB15HI:STRB15LO]   = WSTRB;
          9'hF : Burst[STRB16HI:STRB16LO]   = WSTRB;
          9'h10 : Burst[STRB17HI:STRB17LO]  = WSTRB;
          9'h11 : Burst[STRB18HI:STRB18LO]  = WSTRB;
          9'h12 : Burst[STRB19HI:STRB19LO]  = WSTRB;
          9'h13 : Burst[STRB20HI:STRB20LO]  = WSTRB;
          9'h14 : Burst[STRB21HI:STRB21LO]  = WSTRB;
          9'h15 : Burst[STRB22HI:STRB22LO]  = WSTRB;
          9'h16 : Burst[STRB23HI:STRB23LO]  = WSTRB;
          9'h17 : Burst[STRB24HI:STRB24LO]  = WSTRB;
          9'h18 : Burst[STRB25HI:STRB25LO]  = WSTRB;
          9'h19 : Burst[STRB26HI:STRB26LO]  = WSTRB;
          9'h1A : Burst[STRB27HI:STRB27LO]  = WSTRB;
          9'h1B : Burst[STRB28HI:STRB28LO]  = WSTRB;
          9'h1C : Burst[STRB29HI:STRB29LO]  = WSTRB;
          9'h1D : Burst[STRB30HI:STRB30LO]  = WSTRB;
          9'h1E : Burst[STRB31HI:STRB31LO]  = WSTRB;
          9'h1F : Burst[STRB32HI:STRB32LO]  = WSTRB;
          9'h20 : Burst[STRB33HI:STRB33LO]  = WSTRB;
          9'h21 : Burst[STRB34HI:STRB34LO]  = WSTRB;
          9'h22 : Burst[STRB35HI:STRB35LO]  = WSTRB;
          9'h23 : Burst[STRB36HI:STRB36LO]  = WSTRB;
          9'h24 : Burst[STRB37HI:STRB37LO]  = WSTRB;
          9'h25 : Burst[STRB38HI:STRB38LO]  = WSTRB;
          9'h26 : Burst[STRB39HI:STRB39LO]  = WSTRB;
          9'h27 : Burst[STRB40HI:STRB40LO]  = WSTRB;
          9'h28 : Burst[STRB41HI:STRB41LO]  = WSTRB;
          9'h29 : Burst[STRB42HI:STRB42LO]  = WSTRB;
          9'h2A : Burst[STRB43HI:STRB43LO]  = WSTRB;
          9'h2B : Burst[STRB44HI:STRB44LO]  = WSTRB;
          9'h2C : Burst[STRB45HI:STRB45LO]  = WSTRB;
          9'h2D : Burst[STRB46HI:STRB46LO]  = WSTRB;
          9'h2E : Burst[STRB47HI:STRB47LO]  = WSTRB;
          9'h2F : Burst[STRB48HI:STRB48LO]  = WSTRB;
          9'h30 : Burst[STRB49HI:STRB49LO]  = WSTRB;
          9'h31 : Burst[STRB50HI:STRB50LO]  = WSTRB;
          9'h32 : Burst[STRB51HI:STRB51LO]  = WSTRB;
          9'h33 : Burst[STRB52HI:STRB52LO]  = WSTRB;
          9'h34 : Burst[STRB53HI:STRB53LO]  = WSTRB;
          9'h35 : Burst[STRB54HI:STRB54LO]  = WSTRB;
          9'h36 : Burst[STRB55HI:STRB55LO]  = WSTRB;
          9'h37 : Burst[STRB56HI:STRB56LO]  = WSTRB;
          9'h38 : Burst[STRB57HI:STRB57LO]  = WSTRB;
          9'h39 : Burst[STRB58HI:STRB58LO]  = WSTRB;
          9'h3A : Burst[STRB59HI:STRB59LO]  = WSTRB;
          9'h3B : Burst[STRB60HI:STRB60LO]  = WSTRB;
          9'h3C : Burst[STRB61HI:STRB61LO]  = WSTRB;
          9'h3D : Burst[STRB62HI:STRB62LO]  = WSTRB;
          9'h3E : Burst[STRB63HI:STRB63LO]  = WSTRB;
          9'h3F : Burst[STRB64HI:STRB64LO]  = WSTRB;
          9'h40 : Burst[STRB65HI:STRB65LO]  = WSTRB;
          9'h41 : Burst[STRB66HI:STRB66LO]  = WSTRB;
          9'h42 : Burst[STRB67HI:STRB67LO]  = WSTRB;
          9'h43 : Burst[STRB68HI:STRB68LO]  = WSTRB;
          9'h44 : Burst[STRB69HI:STRB69LO]  = WSTRB;
          9'h45 : Burst[STRB70HI:STRB70LO]  = WSTRB;
          9'h46 : Burst[STRB71HI:STRB71LO]  = WSTRB;
          9'h47 : Burst[STRB72HI:STRB72LO]  = WSTRB;
          9'h48 : Burst[STRB73HI:STRB73LO]  = WSTRB;
          9'h49 : Burst[STRB74HI:STRB74LO]  = WSTRB;
          9'h4A : Burst[STRB75HI:STRB75LO]  = WSTRB;
          9'h4B : Burst[STRB76HI:STRB76LO]  = WSTRB;
          9'h4C : Burst[STRB77HI:STRB77LO]  = WSTRB;
          9'h4D : Burst[STRB78HI:STRB78LO]  = WSTRB;
          9'h4E : Burst[STRB79HI:STRB79LO]  = WSTRB;
          9'h4F : Burst[STRB80HI:STRB80LO]  = WSTRB;
          9'h50 : Burst[STRB81HI:STRB81LO]  = WSTRB;
          9'h51 : Burst[STRB82HI:STRB82LO]  = WSTRB;
          9'h52 : Burst[STRB83HI:STRB83LO]  = WSTRB;
          9'h53 : Burst[STRB84HI:STRB84LO]  = WSTRB;
          9'h54 : Burst[STRB85HI:STRB85LO]  = WSTRB;
          9'h55 : Burst[STRB86HI:STRB86LO]  = WSTRB;
          9'h56 : Burst[STRB87HI:STRB87LO]  = WSTRB;
          9'h57 : Burst[STRB88HI:STRB88LO]  = WSTRB;
          9'h58 : Burst[STRB89HI:STRB89LO]  = WSTRB;
          9'h59 : Burst[STRB90HI:STRB90LO]  = WSTRB;
          9'h5A : Burst[STRB91HI:STRB91LO]  = WSTRB;
          9'h5B : Burst[STRB92HI:STRB92LO]  = WSTRB;
          9'h5C : Burst[STRB93HI:STRB93LO]  = WSTRB;
          9'h5D : Burst[STRB94HI:STRB94LO]  = WSTRB;
          9'h5E : Burst[STRB95HI:STRB95LO]  = WSTRB;
          9'h5F : Burst[STRB96HI:STRB96LO]  = WSTRB;
          9'h60 : Burst[STRB97HI:STRB97LO]  = WSTRB;
          9'h61 : Burst[STRB98HI:STRB98LO]  = WSTRB;
          9'h62 : Burst[STRB99HI:STRB99LO]  = WSTRB;
          9'h63 : Burst[STRB100HI:STRB100LO]  = WSTRB;
          9'h64 : Burst[STRB101HI:STRB101LO]  = WSTRB;
          9'h65 : Burst[STRB102HI:STRB102LO]  = WSTRB;
          9'h66 : Burst[STRB103HI:STRB103LO]  = WSTRB;
          9'h67 : Burst[STRB104HI:STRB104LO]  = WSTRB;
          9'h68 : Burst[STRB105HI:STRB105LO]  = WSTRB;
          9'h69 : Burst[STRB106HI:STRB106LO]  = WSTRB;
          9'h6A : Burst[STRB107HI:STRB107LO]  = WSTRB;
          9'h6B : Burst[STRB108HI:STRB108LO]  = WSTRB;
          9'h6C : Burst[STRB109HI:STRB109LO]  = WSTRB;
          9'h6D : Burst[STRB110HI:STRB110LO]  = WSTRB;
          9'h6E : Burst[STRB111HI:STRB111LO]  = WSTRB;
          9'h6F : Burst[STRB112HI:STRB112LO]  = WSTRB;
          9'h70 : Burst[STRB113HI:STRB113LO]  = WSTRB;
          9'h71 : Burst[STRB114HI:STRB114LO]  = WSTRB;
          9'h72 : Burst[STRB115HI:STRB115LO]  = WSTRB;
          9'h73 : Burst[STRB116HI:STRB116LO]  = WSTRB;
          9'h74 : Burst[STRB117HI:STRB117LO]  = WSTRB;
          9'h75 : Burst[STRB118HI:STRB118LO]  = WSTRB;
          9'h76 : Burst[STRB119HI:STRB119LO]  = WSTRB;
          9'h77 : Burst[STRB120HI:STRB120LO]  = WSTRB;
          9'h78 : Burst[STRB121HI:STRB121LO]  = WSTRB;
          9'h79 : Burst[STRB122HI:STRB122LO]  = WSTRB;
          9'h7A : Burst[STRB123HI:STRB123LO]  = WSTRB;
          9'h7B : Burst[STRB124HI:STRB124LO]  = WSTRB;
          9'h7C : Burst[STRB125HI:STRB125LO]  = WSTRB;
          9'h7D : Burst[STRB126HI:STRB126LO]  = WSTRB;
          9'h7E : Burst[STRB127HI:STRB127LO]  = WSTRB;
          9'h7F : Burst[STRB128HI:STRB128LO]  = WSTRB;
          9'h80 : Burst[STRB129HI:STRB129LO]  = WSTRB;
          9'h81 : Burst[STRB130HI:STRB130LO]  = WSTRB;
          9'h82 : Burst[STRB131HI:STRB131LO]  = WSTRB;
          9'h83 : Burst[STRB132HI:STRB132LO]  = WSTRB;
          9'h84 : Burst[STRB133HI:STRB133LO]  = WSTRB;
          9'h85 : Burst[STRB134HI:STRB134LO]  = WSTRB;
          9'h86 : Burst[STRB135HI:STRB135LO]  = WSTRB;
          9'h87 : Burst[STRB136HI:STRB136LO]  = WSTRB;
          9'h88 : Burst[STRB137HI:STRB137LO]  = WSTRB;
          9'h89 : Burst[STRB138HI:STRB138LO]  = WSTRB;
          9'h8A : Burst[STRB139HI:STRB139LO]  = WSTRB;
          9'h8B : Burst[STRB140HI:STRB140LO]  = WSTRB;
          9'h8C : Burst[STRB141HI:STRB141LO]  = WSTRB;
          9'h8D : Burst[STRB142HI:STRB142LO]  = WSTRB;
          9'h8E : Burst[STRB143HI:STRB143LO]  = WSTRB;
          9'h8F : Burst[STRB144HI:STRB144LO]  = WSTRB;
          9'h90 : Burst[STRB145HI:STRB145LO]  = WSTRB;
          9'h91 : Burst[STRB146HI:STRB146LO]  = WSTRB;
          9'h92 : Burst[STRB147HI:STRB147LO]  = WSTRB;
          9'h93 : Burst[STRB148HI:STRB148LO]  = WSTRB;
          9'h94 : Burst[STRB149HI:STRB149LO]  = WSTRB;
          9'h95 : Burst[STRB150HI:STRB150LO]  = WSTRB;
          9'h96 : Burst[STRB151HI:STRB151LO]  = WSTRB;
          9'h97 : Burst[STRB152HI:STRB152LO]  = WSTRB;
          9'h98 : Burst[STRB153HI:STRB153LO]  = WSTRB;
          9'h99 : Burst[STRB154HI:STRB154LO]  = WSTRB;
          9'h9A : Burst[STRB155HI:STRB155LO]  = WSTRB;
          9'h9B : Burst[STRB156HI:STRB156LO]  = WSTRB;
          9'h9C : Burst[STRB157HI:STRB157LO]  = WSTRB;
          9'h9D : Burst[STRB158HI:STRB158LO]  = WSTRB;
          9'h9E : Burst[STRB159HI:STRB159LO]  = WSTRB;
          9'h9F : Burst[STRB160HI:STRB160LO]  = WSTRB;
          9'hA0 : Burst[STRB161HI:STRB161LO]  = WSTRB;
          9'hA1 : Burst[STRB162HI:STRB162LO]  = WSTRB;
          9'hA2 : Burst[STRB163HI:STRB163LO]  = WSTRB;
          9'hA3 : Burst[STRB164HI:STRB164LO]  = WSTRB;
          9'hA4 : Burst[STRB165HI:STRB165LO]  = WSTRB;
          9'hA5 : Burst[STRB166HI:STRB166LO]  = WSTRB;
          9'hA6 : Burst[STRB167HI:STRB167LO]  = WSTRB;
          9'hA7 : Burst[STRB168HI:STRB168LO]  = WSTRB;
          9'hA8 : Burst[STRB169HI:STRB169LO]  = WSTRB;
          9'hA9 : Burst[STRB170HI:STRB170LO]  = WSTRB;
          9'hAA : Burst[STRB171HI:STRB171LO]  = WSTRB;
          9'hAB : Burst[STRB172HI:STRB172LO]  = WSTRB;
          9'hAC : Burst[STRB173HI:STRB173LO]  = WSTRB;
          9'hAD : Burst[STRB174HI:STRB174LO]  = WSTRB;
          9'hAE : Burst[STRB175HI:STRB175LO]  = WSTRB;
          9'hAF : Burst[STRB176HI:STRB176LO]  = WSTRB;
          9'hB0 : Burst[STRB177HI:STRB177LO]  = WSTRB;
          9'hB1 : Burst[STRB178HI:STRB178LO]  = WSTRB;
          9'hB2 : Burst[STRB179HI:STRB179LO]  = WSTRB;
          9'hB3 : Burst[STRB180HI:STRB180LO]  = WSTRB;
          9'hB4 : Burst[STRB181HI:STRB181LO]  = WSTRB;
          9'hB5 : Burst[STRB182HI:STRB182LO]  = WSTRB;
          9'hB6 : Burst[STRB183HI:STRB183LO]  = WSTRB;
          9'hB7 : Burst[STRB184HI:STRB184LO]  = WSTRB;
          9'hB8 : Burst[STRB185HI:STRB185LO]  = WSTRB;
          9'hB9 : Burst[STRB186HI:STRB186LO]  = WSTRB;
          9'hBA : Burst[STRB187HI:STRB187LO]  = WSTRB;
          9'hBB : Burst[STRB188HI:STRB188LO]  = WSTRB;
          9'hBC : Burst[STRB189HI:STRB189LO]  = WSTRB;
          9'hBD : Burst[STRB190HI:STRB190LO]  = WSTRB;
          9'hBE : Burst[STRB191HI:STRB191LO]  = WSTRB;
          9'hBF : Burst[STRB192HI:STRB192LO]  = WSTRB;
          9'hC0 : Burst[STRB193HI:STRB193LO]  = WSTRB;
          9'hC1 : Burst[STRB194HI:STRB194LO]  = WSTRB;
          9'hC2 : Burst[STRB195HI:STRB195LO]  = WSTRB;
          9'hC3 : Burst[STRB196HI:STRB196LO]  = WSTRB;
          9'hC4 : Burst[STRB197HI:STRB197LO]  = WSTRB;
          9'hC5 : Burst[STRB198HI:STRB198LO]  = WSTRB;
          9'hC6 : Burst[STRB199HI:STRB199LO]  = WSTRB;
          9'hC7 : Burst[STRB200HI:STRB200LO]  = WSTRB;
          9'hC8 : Burst[STRB201HI:STRB201LO]  = WSTRB;
          9'hC9 : Burst[STRB202HI:STRB202LO]  = WSTRB;
          9'hCA : Burst[STRB203HI:STRB203LO]  = WSTRB;
          9'hCB : Burst[STRB204HI:STRB204LO]  = WSTRB;
          9'hCC : Burst[STRB205HI:STRB205LO]  = WSTRB;
          9'hCD : Burst[STRB206HI:STRB206LO]  = WSTRB;
          9'hCE : Burst[STRB207HI:STRB207LO]  = WSTRB;
          9'hCF : Burst[STRB208HI:STRB208LO]  = WSTRB;
          9'hD0 : Burst[STRB209HI:STRB209LO]  = WSTRB;
          9'hD1 : Burst[STRB210HI:STRB210LO]  = WSTRB;
          9'hD2 : Burst[STRB211HI:STRB211LO]  = WSTRB;
          9'hD3 : Burst[STRB212HI:STRB212LO]  = WSTRB;
          9'hD4 : Burst[STRB213HI:STRB213LO]  = WSTRB;
          9'hD5 : Burst[STRB214HI:STRB214LO]  = WSTRB;
          9'hD6 : Burst[STRB215HI:STRB215LO]  = WSTRB;
          9'hD7 : Burst[STRB216HI:STRB216LO]  = WSTRB;
          9'hD8 : Burst[STRB217HI:STRB217LO]  = WSTRB;
          9'hD9 : Burst[STRB218HI:STRB218LO]  = WSTRB;
          9'hDA : Burst[STRB219HI:STRB219LO]  = WSTRB;
          9'hDB : Burst[STRB220HI:STRB220LO]  = WSTRB;
          9'hDC : Burst[STRB221HI:STRB221LO]  = WSTRB;
          9'hDD : Burst[STRB222HI:STRB222LO]  = WSTRB;
          9'hDE : Burst[STRB223HI:STRB223LO]  = WSTRB;
          9'hDF : Burst[STRB224HI:STRB224LO]  = WSTRB;
          9'hE0 : Burst[STRB225HI:STRB225LO]  = WSTRB;
          9'hE1 : Burst[STRB226HI:STRB226LO]  = WSTRB;
          9'hE2 : Burst[STRB227HI:STRB227LO]  = WSTRB;
          9'hE3 : Burst[STRB228HI:STRB228LO]  = WSTRB;
          9'hE4 : Burst[STRB229HI:STRB229LO]  = WSTRB;
          9'hE5 : Burst[STRB230HI:STRB230LO]  = WSTRB;
          9'hE6 : Burst[STRB231HI:STRB231LO]  = WSTRB;
          9'hE7 : Burst[STRB232HI:STRB232LO]  = WSTRB;
          9'hE8 : Burst[STRB233HI:STRB233LO]  = WSTRB;
          9'hE9 : Burst[STRB234HI:STRB234LO]  = WSTRB;
          9'hEA : Burst[STRB235HI:STRB235LO]  = WSTRB;
          9'hEB : Burst[STRB236HI:STRB236LO]  = WSTRB;
          9'hEC : Burst[STRB237HI:STRB237LO]  = WSTRB;
          9'hED : Burst[STRB238HI:STRB238LO]  = WSTRB;
          9'hEE : Burst[STRB239HI:STRB239LO]  = WSTRB;
          9'hEF : Burst[STRB240HI:STRB240LO]  = WSTRB;
          9'hF0 : Burst[STRB241HI:STRB241LO]  = WSTRB;
          9'hF1 : Burst[STRB242HI:STRB242LO]  = WSTRB;
          9'hF2 : Burst[STRB243HI:STRB243LO]  = WSTRB;
          9'hF3 : Burst[STRB244HI:STRB244LO]  = WSTRB;
          9'hF4 : Burst[STRB245HI:STRB245LO]  = WSTRB;
          9'hF5 : Burst[STRB246HI:STRB246LO]  = WSTRB;
          9'hF6 : Burst[STRB247HI:STRB247LO]  = WSTRB;
          9'hF7 : Burst[STRB248HI:STRB248LO]  = WSTRB;
          9'hF8 : Burst[STRB249HI:STRB249LO]  = WSTRB;
          9'hF9 : Burst[STRB250HI:STRB250LO]  = WSTRB;
          9'hFA : Burst[STRB251HI:STRB251LO]  = WSTRB;
          9'hFB : Burst[STRB252HI:STRB252LO]  = WSTRB;
          9'hFC : Burst[STRB253HI:STRB253LO]  = WSTRB;
          9'hFD : Burst[STRB254HI:STRB254LO]  = WSTRB;
          9'hFE : Burst[STRB255HI:STRB255LO]  = WSTRB;
          9'hFF : Burst[STRB256HI:STRB256LO]  = WSTRB;
          default : Burst[STRB256HI:STRB256LO] = {STRB_WIDTH{1'bx}};
        endcase

        WBurstCam[WIDMatch_next] <= Burst;         // copy back from temp store

        // when write data transfer completes, determine if last
        WLastCam[WIDMatch_next] <= WLAST & WREADY; // record whether last data completed

        // When transfer completes, increment the count
        WCountCam[WIDMatch_next] <=
          WREADY ? WCountCam[WIDMatch] + 9'b000000001:  // inc count
                   WCountCam[WIDMatch];


        if (WIDMatch_next == WIndex)              // if new burst, increment CAM index
          WIndex = WIndex + 1;

      end // if (WVALID)

      // -----------------------------------------------------------------------
      // Valid write address
      if (AWVALID)
      begin : p_WriteCamAWVALID


        //if WVALID and AWVALID for the same transaction then the WVALID
        //assignments in section above will not have been assigned so will
        //lose strobe information
        if(!(WVALID & (AIDMatch == WIDMatch)))
        begin
          Burst = WBurstCam[AIDMatch];
        end
        Burst[ADDRHI:ADDRLO]   = AWADDR[ADDRHI:ADDRLO];
        Burst[EXCL]            = (AWLOCK == `AXI4PC_ALOCK_EXCL);
        Burst[BURSTHI:BURSTLO] = AWBURST;
        Burst[ALENHI:ALENLO]   = AWLEN;
        Burst[ASIZEHI:ASIZELO] = AWSIZE;
        Burst[IDHI:IDLO]       = AWID;
        WBurstCam[AIDMatch_next] <= Burst;         // copy back from temp store
        WAddrCam[AIDMatch_next] <= AWREADY;        // record if write address completed
        // If new burst, increment CAM index
        if (AIDMatch_next == WIndex)
        begin
          WIndex = WIndex + 1;
        end
      end // p_WriteCamAWVALID new write address

    end // else: !if(!`AXI4_AUX_RSTn)
  end // always @(negedge `AXI4_AUX_RSTn or posedge `AXI4_AUX_CLK)
  

//------------------------------------------------------------------------------
// INDEX:   5) Verilog Functions
//------------------------------------------------------------------------------
// INDEX:        - function integer clogb2 (input integer n)
// function to determine ceil of log2(n)
//-----------------------------------------------------------------------------
  function integer clogb2 (input integer n);
    begin
      for (clogb2=0; n>0; clogb2=clogb2+1)
        n = n >> 1;
    end
  endfunction


  // INDEX:        - CheckBurst
  // =====
  // Inputs: Burst (burst data structure)
  //         Count (number of data items)
  // Returns: High is any of the write strobes are illegal
  // Calls CheckStrb to test each WSTRB value.
  //------------------------------------------------------------------------------
  function CheckBurst;
    input [WBURSTMAX:0] Burst;         // burst vector
    input         [9:0] Count;         // number of beats in the burst
    integer             loop_ctr;          // general loop counter
    integer             NumBytes;      // number of bytes in the burst
    reg           [6:0] StartAddr;     // start address of burst
    reg           [6:0] StrbAddr;      // address used to check WSTRB
    reg           [2:0] StrbSize;      // size used to check WSTRB
    reg           [7:0] StrbLen;       // length used to check WSTRB
    reg    [STRB_MAX:0] Strb;          // WSTRB to be checked
    reg           [9:0] WrapMaskWide;  // address mask for wrapping bursts
    reg           [6:0] WrapMask;      // relevant bits WrapMaskWide
  begin

    StartAddr   = Burst[ADDRHI:ADDRLO];
    StrbAddr    = StartAddr;   // incrementing address initialises to start addr
    StrbSize    = Burst[ASIZEHI:ASIZELO];
    StrbLen     = Burst[ALENHI:ALENLO];
    CheckBurst  = 1'b0;

    // Initialize to avoid latch warnings (not really latches as they are set in loop)
    Strb         = {STRB_WIDTH{1'bX}};
    WrapMask     =          {7{1'bX}};
    WrapMaskWide =         {10{1'bX}};

    // determine the number of bytes in the burst for wrapping purposes
    NumBytes = (StrbLen + 1) << StrbSize;

    // Check the strobe for each write data transfer
    for (loop_ctr=1; loop_ctr<=256; loop_ctr=loop_ctr+1)
    begin
      if (loop_ctr <= Count)               // Only consider entries up to burst length
      begin

        // Need to use full case statement to index WSTRB as in Verilog the
        // bit slice range must be bounded by constant expressions
        case (loop_ctr)
          1   : Strb = Burst[STRB1HI:STRB1LO];
          2   : Strb = Burst[STRB2HI:STRB2LO];
          3   : Strb = Burst[STRB3HI:STRB3LO];
          4   : Strb = Burst[STRB4HI:STRB4LO];
          5   : Strb = Burst[STRB5HI:STRB5LO];
          6   : Strb = Burst[STRB6HI:STRB6LO];
          7   : Strb = Burst[STRB7HI:STRB7LO];
          8   : Strb = Burst[STRB8HI:STRB8LO];
          9   : Strb = Burst[STRB9HI:STRB9LO];
          10  : Strb = Burst[STRB10HI:STRB10LO];
          11  : Strb = Burst[STRB11HI:STRB11LO];
          12  : Strb = Burst[STRB12HI:STRB12LO];
          13  : Strb = Burst[STRB13HI:STRB13LO];
          14  : Strb = Burst[STRB14HI:STRB14LO];
          15  : Strb = Burst[STRB15HI:STRB15LO];
          16  : Strb = Burst[STRB16HI:STRB16LO];
          17  : Strb = Burst[STRB17HI:STRB17LO];
          18  : Strb = Burst[STRB18HI:STRB18LO];
          19  : Strb = Burst[STRB19HI:STRB19LO];
          20  : Strb = Burst[STRB20HI:STRB20LO];
          21  : Strb = Burst[STRB21HI:STRB21LO];
          22  : Strb = Burst[STRB22HI:STRB22LO];
          23  : Strb = Burst[STRB23HI:STRB23LO];
          24  : Strb = Burst[STRB24HI:STRB24LO];
          25  : Strb = Burst[STRB25HI:STRB25LO];
          26  : Strb = Burst[STRB26HI:STRB26LO];
          27  : Strb = Burst[STRB27HI:STRB27LO];
          28  : Strb = Burst[STRB28HI:STRB28LO];
          29  : Strb = Burst[STRB29HI:STRB29LO];
          30  : Strb = Burst[STRB30HI:STRB30LO];
          31  : Strb = Burst[STRB31HI:STRB31LO];
          32  : Strb = Burst[STRB32HI:STRB32LO];
          33  : Strb = Burst[STRB33HI:STRB33LO];
          34  : Strb = Burst[STRB34HI:STRB34LO];
          35  : Strb = Burst[STRB35HI:STRB35LO];
          36  : Strb = Burst[STRB36HI:STRB36LO];
          37  : Strb = Burst[STRB37HI:STRB37LO];
          38  : Strb = Burst[STRB38HI:STRB38LO];
          39  : Strb = Burst[STRB39HI:STRB39LO];
          40  : Strb = Burst[STRB40HI:STRB40LO];
          41  : Strb = Burst[STRB41HI:STRB41LO];
          42  : Strb = Burst[STRB42HI:STRB42LO];
          43  : Strb = Burst[STRB43HI:STRB43LO];
          44  : Strb = Burst[STRB44HI:STRB44LO];
          45  : Strb = Burst[STRB45HI:STRB45LO];
          46  : Strb = Burst[STRB46HI:STRB46LO];
          47  : Strb = Burst[STRB47HI:STRB47LO];
          48  : Strb = Burst[STRB48HI:STRB48LO];
          49  : Strb = Burst[STRB49HI:STRB49LO];
          50  : Strb = Burst[STRB50HI:STRB50LO];
          51  : Strb = Burst[STRB51HI:STRB51LO];
          52  : Strb = Burst[STRB52HI:STRB52LO];
          53  : Strb = Burst[STRB53HI:STRB53LO];
          54  : Strb = Burst[STRB54HI:STRB54LO];
          55  : Strb = Burst[STRB55HI:STRB55LO];
          56  : Strb = Burst[STRB56HI:STRB56LO];
          57  : Strb = Burst[STRB57HI:STRB57LO];
          58  : Strb = Burst[STRB58HI:STRB58LO];
          59  : Strb = Burst[STRB59HI:STRB59LO];
          60  : Strb = Burst[STRB60HI:STRB60LO];
          61  : Strb = Burst[STRB61HI:STRB61LO];
          62  : Strb = Burst[STRB62HI:STRB62LO];
          63  : Strb = Burst[STRB63HI:STRB63LO];
          64  : Strb = Burst[STRB64HI:STRB64LO];
          65  : Strb = Burst[STRB65HI:STRB65LO];
          66  : Strb = Burst[STRB66HI:STRB66LO];
          67  : Strb = Burst[STRB67HI:STRB67LO];
          68  : Strb = Burst[STRB68HI:STRB68LO];
          69  : Strb = Burst[STRB69HI:STRB69LO];
          70  : Strb = Burst[STRB70HI:STRB70LO];
          71  : Strb = Burst[STRB71HI:STRB71LO];
          72  : Strb = Burst[STRB72HI:STRB72LO];
          73  : Strb = Burst[STRB73HI:STRB73LO];
          74  : Strb = Burst[STRB74HI:STRB74LO];
          75  : Strb = Burst[STRB75HI:STRB75LO];
          76  : Strb = Burst[STRB76HI:STRB76LO];
          77  : Strb = Burst[STRB77HI:STRB77LO];
          78  : Strb = Burst[STRB78HI:STRB78LO];
          79  : Strb = Burst[STRB79HI:STRB79LO];
          80  : Strb = Burst[STRB80HI:STRB80LO];
          81  : Strb = Burst[STRB81HI:STRB81LO];
          82  : Strb = Burst[STRB82HI:STRB82LO];
          83  : Strb = Burst[STRB83HI:STRB83LO];
          84  : Strb = Burst[STRB84HI:STRB84LO];
          85  : Strb = Burst[STRB85HI:STRB85LO];
          86  : Strb = Burst[STRB86HI:STRB86LO];
          87  : Strb = Burst[STRB87HI:STRB87LO];
          88  : Strb = Burst[STRB88HI:STRB88LO];
          89  : Strb = Burst[STRB89HI:STRB89LO];
          90  : Strb = Burst[STRB90HI:STRB90LO];
          91  : Strb = Burst[STRB91HI:STRB91LO];
          92  : Strb = Burst[STRB92HI:STRB92LO];
          93  : Strb = Burst[STRB93HI:STRB93LO];
          94  : Strb = Burst[STRB94HI:STRB94LO];
          95  : Strb = Burst[STRB95HI:STRB95LO];
          96  : Strb = Burst[STRB96HI:STRB96LO];
          97  : Strb = Burst[STRB97HI:STRB97LO];
          98  : Strb = Burst[STRB98HI:STRB98LO];
          99  : Strb = Burst[STRB99HI:STRB99LO];
          100  : Strb = Burst[STRB100HI:STRB100LO];
          101  : Strb = Burst[STRB101HI:STRB101LO];
          102  : Strb = Burst[STRB102HI:STRB102LO];
          103  : Strb = Burst[STRB103HI:STRB103LO];
          104  : Strb = Burst[STRB104HI:STRB104LO];
          105  : Strb = Burst[STRB105HI:STRB105LO];
          106  : Strb = Burst[STRB106HI:STRB106LO];
          107  : Strb = Burst[STRB107HI:STRB107LO];
          108  : Strb = Burst[STRB108HI:STRB108LO];
          109  : Strb = Burst[STRB109HI:STRB109LO];
          110  : Strb = Burst[STRB110HI:STRB110LO];
          111  : Strb = Burst[STRB111HI:STRB111LO];
          112  : Strb = Burst[STRB112HI:STRB112LO];
          113  : Strb = Burst[STRB113HI:STRB113LO];
          114  : Strb = Burst[STRB114HI:STRB114LO];
          115  : Strb = Burst[STRB115HI:STRB115LO];
          116  : Strb = Burst[STRB116HI:STRB116LO];
          117  : Strb = Burst[STRB117HI:STRB117LO];
          118  : Strb = Burst[STRB118HI:STRB118LO];
          119  : Strb = Burst[STRB119HI:STRB119LO];
          120  : Strb = Burst[STRB120HI:STRB120LO];
          121  : Strb = Burst[STRB121HI:STRB121LO];
          122  : Strb = Burst[STRB122HI:STRB122LO];
          123  : Strb = Burst[STRB123HI:STRB123LO];
          124  : Strb = Burst[STRB124HI:STRB124LO];
          125  : Strb = Burst[STRB125HI:STRB125LO];
          126  : Strb = Burst[STRB126HI:STRB126LO];
          127  : Strb = Burst[STRB127HI:STRB127LO];
          128  : Strb = Burst[STRB128HI:STRB128LO];
          129  : Strb = Burst[STRB129HI:STRB129LO];
          130  : Strb = Burst[STRB130HI:STRB130LO];
          131  : Strb = Burst[STRB131HI:STRB131LO];
          132  : Strb = Burst[STRB132HI:STRB132LO];
          133  : Strb = Burst[STRB133HI:STRB133LO];
          134  : Strb = Burst[STRB134HI:STRB134LO];
          135  : Strb = Burst[STRB135HI:STRB135LO];
          136  : Strb = Burst[STRB136HI:STRB136LO];
          137  : Strb = Burst[STRB137HI:STRB137LO];
          138  : Strb = Burst[STRB138HI:STRB138LO];
          139  : Strb = Burst[STRB139HI:STRB139LO];
          140  : Strb = Burst[STRB140HI:STRB140LO];
          141  : Strb = Burst[STRB141HI:STRB141LO];
          142  : Strb = Burst[STRB142HI:STRB142LO];
          143  : Strb = Burst[STRB143HI:STRB143LO];
          144  : Strb = Burst[STRB144HI:STRB144LO];
          145  : Strb = Burst[STRB145HI:STRB145LO];
          146  : Strb = Burst[STRB146HI:STRB146LO];
          147  : Strb = Burst[STRB147HI:STRB147LO];
          148  : Strb = Burst[STRB148HI:STRB148LO];
          149  : Strb = Burst[STRB149HI:STRB149LO];
          150  : Strb = Burst[STRB150HI:STRB150LO];
          151  : Strb = Burst[STRB151HI:STRB151LO];
          152  : Strb = Burst[STRB152HI:STRB152LO];
          153  : Strb = Burst[STRB153HI:STRB153LO];
          154  : Strb = Burst[STRB154HI:STRB154LO];
          155  : Strb = Burst[STRB155HI:STRB155LO];
          156  : Strb = Burst[STRB156HI:STRB156LO];
          157  : Strb = Burst[STRB157HI:STRB157LO];
          158  : Strb = Burst[STRB158HI:STRB158LO];
          159  : Strb = Burst[STRB159HI:STRB159LO];
          160  : Strb = Burst[STRB160HI:STRB160LO];
          161  : Strb = Burst[STRB161HI:STRB161LO];
          162  : Strb = Burst[STRB162HI:STRB162LO];
          163  : Strb = Burst[STRB163HI:STRB163LO];
          164  : Strb = Burst[STRB164HI:STRB164LO];
          165  : Strb = Burst[STRB165HI:STRB165LO];
          166  : Strb = Burst[STRB166HI:STRB166LO];
          167  : Strb = Burst[STRB167HI:STRB167LO];
          168  : Strb = Burst[STRB168HI:STRB168LO];
          169  : Strb = Burst[STRB169HI:STRB169LO];
          170  : Strb = Burst[STRB170HI:STRB170LO];
          171  : Strb = Burst[STRB171HI:STRB171LO];
          172  : Strb = Burst[STRB172HI:STRB172LO];
          173  : Strb = Burst[STRB173HI:STRB173LO];
          174  : Strb = Burst[STRB174HI:STRB174LO];
          175  : Strb = Burst[STRB175HI:STRB175LO];
          176  : Strb = Burst[STRB176HI:STRB176LO];
          177  : Strb = Burst[STRB177HI:STRB177LO];
          178  : Strb = Burst[STRB178HI:STRB178LO];
          179  : Strb = Burst[STRB179HI:STRB179LO];
          180  : Strb = Burst[STRB180HI:STRB180LO];
          181  : Strb = Burst[STRB181HI:STRB181LO];
          182  : Strb = Burst[STRB182HI:STRB182LO];
          183  : Strb = Burst[STRB183HI:STRB183LO];
          184  : Strb = Burst[STRB184HI:STRB184LO];
          185  : Strb = Burst[STRB185HI:STRB185LO];
          186  : Strb = Burst[STRB186HI:STRB186LO];
          187  : Strb = Burst[STRB187HI:STRB187LO];
          188  : Strb = Burst[STRB188HI:STRB188LO];
          189  : Strb = Burst[STRB189HI:STRB189LO];
          190  : Strb = Burst[STRB190HI:STRB190LO];
          191  : Strb = Burst[STRB191HI:STRB191LO];
          192  : Strb = Burst[STRB192HI:STRB192LO];
          193  : Strb = Burst[STRB193HI:STRB193LO];
          194  : Strb = Burst[STRB194HI:STRB194LO];
          195  : Strb = Burst[STRB195HI:STRB195LO];
          196  : Strb = Burst[STRB196HI:STRB196LO];
          197  : Strb = Burst[STRB197HI:STRB197LO];
          198  : Strb = Burst[STRB198HI:STRB198LO];
          199  : Strb = Burst[STRB199HI:STRB199LO];
          200  : Strb = Burst[STRB200HI:STRB200LO];
          201  : Strb = Burst[STRB201HI:STRB201LO];
          202  : Strb = Burst[STRB202HI:STRB202LO];
          203  : Strb = Burst[STRB203HI:STRB203LO];
          204  : Strb = Burst[STRB204HI:STRB204LO];
          205  : Strb = Burst[STRB205HI:STRB205LO];
          206  : Strb = Burst[STRB206HI:STRB206LO];
          207  : Strb = Burst[STRB207HI:STRB207LO];
          208  : Strb = Burst[STRB208HI:STRB208LO];
          209  : Strb = Burst[STRB209HI:STRB209LO];
          210  : Strb = Burst[STRB210HI:STRB210LO];
          211  : Strb = Burst[STRB211HI:STRB211LO];
          212  : Strb = Burst[STRB212HI:STRB212LO];
          213  : Strb = Burst[STRB213HI:STRB213LO];
          214  : Strb = Burst[STRB214HI:STRB214LO];
          215  : Strb = Burst[STRB215HI:STRB215LO];
          216  : Strb = Burst[STRB216HI:STRB216LO];
          217  : Strb = Burst[STRB217HI:STRB217LO];
          218  : Strb = Burst[STRB218HI:STRB218LO];
          219  : Strb = Burst[STRB219HI:STRB219LO];
          220  : Strb = Burst[STRB220HI:STRB220LO];
          221  : Strb = Burst[STRB221HI:STRB221LO];
          222  : Strb = Burst[STRB222HI:STRB222LO];
          223  : Strb = Burst[STRB223HI:STRB223LO];
          224  : Strb = Burst[STRB224HI:STRB224LO];
          225  : Strb = Burst[STRB225HI:STRB225LO];
          226  : Strb = Burst[STRB226HI:STRB226LO];
          227  : Strb = Burst[STRB227HI:STRB227LO];
          228  : Strb = Burst[STRB228HI:STRB228LO];
          229  : Strb = Burst[STRB229HI:STRB229LO];
          230  : Strb = Burst[STRB230HI:STRB230LO];
          231  : Strb = Burst[STRB231HI:STRB231LO];
          232  : Strb = Burst[STRB232HI:STRB232LO];
          233  : Strb = Burst[STRB233HI:STRB233LO];
          234  : Strb = Burst[STRB234HI:STRB234LO];
          235  : Strb = Burst[STRB235HI:STRB235LO];
          236  : Strb = Burst[STRB236HI:STRB236LO];
          237  : Strb = Burst[STRB237HI:STRB237LO];
          238  : Strb = Burst[STRB238HI:STRB238LO];
          239  : Strb = Burst[STRB239HI:STRB239LO];
          240  : Strb = Burst[STRB240HI:STRB240LO];
          241  : Strb = Burst[STRB241HI:STRB241LO];
          242  : Strb = Burst[STRB242HI:STRB242LO];
          243  : Strb = Burst[STRB243HI:STRB243LO];
          244  : Strb = Burst[STRB244HI:STRB244LO];
          245  : Strb = Burst[STRB245HI:STRB245LO];
          246  : Strb = Burst[STRB246HI:STRB246LO];
          247  : Strb = Burst[STRB247HI:STRB247LO];
          248  : Strb = Burst[STRB248HI:STRB248LO];
          249  : Strb = Burst[STRB249HI:STRB249LO];
          250  : Strb = Burst[STRB250HI:STRB250LO];
          251  : Strb = Burst[STRB251HI:STRB251LO];
          252  : Strb = Burst[STRB252HI:STRB252LO];
          253  : Strb = Burst[STRB253HI:STRB253LO];
          254  : Strb = Burst[STRB254HI:STRB254LO];
          255  : Strb = Burst[STRB255HI:STRB255LO];
          256  : Strb = Burst[STRB256HI:STRB256LO];
          default : Strb = {STRB_WIDTH{1'bx}};
        endcase

        // returns high if any strobes are illegal
        if (CheckStrb(StrbAddr, StrbSize, Strb))
        begin
          CheckBurst = 1'b1;
        end

        // -----------------------------------------------------------------------
        // Increment aligned StrbAddr
        if (Burst[BURSTHI:BURSTLO] != `AXI4PC_ABURST_FIXED)
          // fixed bursts don't increment or align the address
        begin
          // align and increment address,
          // Address is incremented from an aligned version
          StrbAddr = StrbAddr &
            (7'b111_1111 - (7'b000_0001 << StrbSize) + 7'b000_0001);
                                                                // align to size
          StrbAddr = StrbAddr + (7'b000_0001 << StrbSize);      // increment
        end // if (Burst[BURSTHI:BURSTLO] != `AXI4PC_ABURST_FIXED)

        // for wrapping bursts the top bits of the strobe address remain
        // unchanged
        if (Burst[BURSTHI:BURSTLO] == `AXI4PC_ABURST_WRAP)
        begin
          WrapMaskWide = (10'b11_1111_1111 - NumBytes + 10'b00_0000_0001);
          // To wrap the address, need 10 bits
          WrapMask = WrapMaskWide[6:0];
          // Only 7 bits of address are necessary to calculate strobe
          StrbAddr = (StartAddr & WrapMask) | (StrbAddr & ~WrapMask);
          // upper bits remain stable for wrapping bursts depending on the
          // number of bytes in the burst
        end
      end // if (loop_ctr < Count)
    end // for (loop_ctr=1; loop_ctr<=256; loop_ctr=loop_ctr+1)
  end
  endfunction // CheckBurst


  // INDEX:        - CheckStrb
  // =====
  function CheckStrb;
    input        [6:0] StrbAddr;
    input        [2:0] StrbSize;
    input [STRB_MAX:0] Strb;
    reg   [STRB_MAX:0] StrbMask;
  begin

    // The basic strobe for an aligned address
    StrbMask = (STRB_1 << (STRB_1 << StrbSize)) - STRB_1;

    // Zero the unaligned byte lanes
    // Note: the number of unaligned byte lanes is given by:
    // (StrbAddr & ((1 << StrbSize) - 1)), i.e. the unaligned part of the
    // address with respect to the transfer size
    //
    // Note! {{STRB_MAX{1'b0}}, 1'b1} gives 1 in the correct vector length

    StrbMask = StrbMask &                   // Mask off unaligned byte lanes
      (StrbMask <<                          // shift the strb mask left by
        (StrbAddr & ((STRB_1 << StrbSize) -  STRB_1))
                                            // the number of unaligned byte lanes
      );

    // Shift mask into correct byte lanes
    // Note: (STRB_MAX << StrbSize) & STRB_MAX is used as a mask on the address
    // to pick out the bits significant bits, with respect to the bus width and
    // transfer size, for shifting the mask to the correct byte lanes.
    StrbMask = StrbMask << (StrbAddr & ((STRB_MAX << StrbSize) & STRB_MAX));

    // check for strobe error
    CheckStrb = (|(Strb & ~StrbMask));

  end
  endfunction // CheckStrb


  // INDEX:        - ReadDataMask
  // =====
  // Inputs: Burst (Burst data structure)
  //         Beat  (Data beat number)
  // Returns: Read data mask for valid byte lanes.
  //----------------------------------------------------------------------------
  function [DATA_MAX:0]  ReadDataMask;
    input [STRB256HI:0]  Burst;         // burst vector
    input [9:0]          Beat;          // beat number in the burst (1-256)
    reg   [11:0]         bit_count;
    reg   [DATA_MAX+1:0] byte_mask;
  begin
    bit_count = ByteCount(Burst, Beat) << 3;
    byte_mask = (1'b1 << bit_count) - 1;
    // Result is the valid byte mask shifted by the calculated bit shift
    ReadDataMask = byte_mask[DATA_MAX:0] << (ByteShift(Burst, Beat)*8);
  end
  endfunction // ReadDataMask


  // INDEX:        - ByteShift
  // =====
  // Inputs: Burst (Burst data structure)
  //         Beat  (Data beat number)
  // Returns: Byte Shift for valid byte lanes.
  //------------------------------------------------------------------------------
  function [DATA_MAX:0] ByteShift;
    input [STRB256HI:0] Burst;         // burst vector
    input [9:0]        Beat;           // beat number in the burst (1-256)
    reg   [6:0]        axaddr;
    reg   [2:0]        axsize;
    reg   [7:0]        axlen;
    reg   [1:0]        axburst;
    integer bus_data_bytes;
    integer length;
    integer unaligned_byte_shift;
    integer beat_addr_inc;
    integer addr_trans_bus;
    integer addr_trans_bus_inc;
    integer wrap_point;
    integer transfer_byte_shift;
  begin
    axaddr  = Burst[ADDRHI:ADDRLO];
    axsize  = Burst[ASIZEHI:ASIZELO];
    axlen   = Burst[ALENHI:ALENLO];
    axburst = Burst[BURSTHI:BURSTLO];

    bus_data_bytes = STRB_WIDTH;

    length = axlen + 1;

    // Number of bytes that the data needs to be shifted when
    // the address is unaligned
    unaligned_byte_shift =
      axaddr &                        // Byte address
      ((1<<axsize)-1);                //   masked by the number of bytes
                                      //   in a transfer

    // Burst beat address increment
    beat_addr_inc = 0;
    // For a FIXED burst ther is no increment
    // For INCR and WRAP it is the beat number minus 1
    if (axburst != 0)
    begin
      beat_addr_inc = Beat;
    end

    // Transfer address within data bus
    // The root of the transfer address within the data bus is byte address
    // divided by the number of bytes in each transfer. This is also masked
    // so that the upper bits that do not control the byte shift are not
    // included.
    addr_trans_bus = (axaddr & (bus_data_bytes - 1))>>axsize;

    // The address may increment with each beat. The increment will be zero
    // for a FIXED burst.
    addr_trans_bus_inc = addr_trans_bus + beat_addr_inc;

    // Modify the byte shift for wrapping bursts
    if (axburst == 2)
    begin
      // The upper address of the transfer before wrapping
      wrap_point = length + (addr_trans_bus & ~(length - 1));
      // If adding the beat number to the transfer address causes it to
      // pass the upper wrap address then wrap to the lower address.
      if (addr_trans_bus_inc >= wrap_point)
      begin
        addr_trans_bus_inc = addr_trans_bus_inc - length;
      end
    end

    // Address calculation may exceed the number of transfers that can fit
    // in the data bus for INCR bursts. So the calculation is truncated to
    // make the byte shift wrap round to zero. 
    addr_trans_bus_inc = addr_trans_bus_inc & ((bus_data_bytes-1)>>axsize);

    // Number of bytes that the data needs to be shifted when
    // the transfer size is less than the data bus width
    transfer_byte_shift = (1<<axsize) *      // Number of bytes in a transfer
                          addr_trans_bus_inc;// Transfer address within data bus

    // For a FIXED burst or on the frist beat of an INCR burst
    // shift the data if the address is unaligned
    if ((axburst == 0) || ((axburst == 1) && (Beat == 0)))
    begin
      ByteShift = transfer_byte_shift + unaligned_byte_shift;
    end
    else
    begin
      ByteShift = transfer_byte_shift;
    end
  end
  endfunction // ByteShift


  // INDEX:        - ByteCount
  // =====
  // Inputs: Burst (Burst data structure)
  //         Beat  (Data beat number)
  // Returns: Byte Count of valid byte lanes.
  //----------------------------------------------------------------------------
  function [7:0] ByteCount;
    input [STRB256HI:0] Burst;         // burst vector
    input [9:0]        Beat;           // beat number in the burst (1-256)
    reg   [6:0]        axaddr;
    reg   [2:0]        axsize;
    reg   [7:0]        axlen;
    reg   [1:0]        axburst;
    integer bus_data_bytes;
    integer unaligned_byte_shift;
  begin
    axaddr  = Burst[ADDRHI:ADDRLO];
    axsize  = Burst[ASIZEHI:ASIZELO];
    axlen   = Burst[ALENHI:ALENLO];
    axburst = Burst[BURSTHI:BURSTLO];

    bus_data_bytes = STRB_WIDTH;

    // Number of bytes that the data needs to be shifted when
    // the address is unaligned
    unaligned_byte_shift =
      axaddr &              // Byte address
      ((1<<axsize)-1);      //   masked by the number of bytes
                            //   in a transfer

    // The number of valid bits depends on the transfer size.
    ByteCount = (1<<axsize);

    // For FIXED bursts or on the first beat of an INCR burst
    // if the address is unaligned modify the number of
    // valid strobe bits
    if ((axburst == 0) || (Beat == 0))
    begin
      // The number of valid bits depends on the transfer size
      // and the offset of the unaligned address.
      ByteCount = ByteCount - unaligned_byte_shift;
    end
  end
  endfunction // ByteCount



//------------------------------------------------------------------------------
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

//------------------------------------------------------------------------------
// INDEX:   2) End of module
//------------------------------------------------------------------------------
endmodule // Axi4PC
`include "Axi4PC_undefs.v"
`include "Axi4PC_message_undefs.v"
`endif    //AXI4PC
`endif    //AXI4PC_OFF































