// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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

`include "cfg.sv"

module rust_top ( 
    input bit                          core_clk,

    input logic                        cptra_pwrgood,
    input logic                        cptra_rst_b,

    //JTAG Interface
    input logic                        jtag_tck,    // JTAG clk
    input logic                        jtag_tms,    // JTAG TMS
    input logic                        jtag_tdi,    // JTAG tdi
    input logic                        jtag_trst_n, // JTAG Reset //TODO optional needs review
    output logic                       jtag_tdo,    // JTAG TDO

    //APB Interface
    input  logic [`APB_ADDR_WIDTH-1:0] PADDR,
    input  logic [2:0]                 PPROT,
    input  logic                       PSEL,
    input  logic                       PENABLE,
    input  logic                       PWRITE,
    input  logic [`APB_DATA_WIDTH-1:0] PWDATA,
    input  logic [`APB_USER_WIDTH-1:0] PAUSER,

    output logic                       PREADY,
    output logic                       PSLVERR,
    output logic [`APB_DATA_WIDTH-1:0] PRDATA,

    //QSPI Interface
    output logic                       qspi_clk_o,
    output logic [`QSPI_CS_WIDTH-1:0]  qspi_cs_no,
    inout  wire  [`QSPI_IO_WIDTH-1:0]  qspi_d_io,

    //UART Interface
    //TODO update with UART interface signals

    //I3C Interface
    //TODO update with I3C interface signals
    
    output logic                       ready_for_fuses,
    output logic                       ready_for_fw_push,
    output logic                       ready_for_runtime,

    output logic                       mailbox_data_avail,
    output logic                       mailbox_flow_done,
    
    input logic                        BootFSM_BrkPoint,

    input logic  [63:0]                generic_input_wires,
    output logic [63:0]                generic_output_wires,

    input logic  [`SOC_SEC_STATE_WIDTH-1:0] security_state

    );

    //caliptra reset driven by boot fsm in mailbox
    logic                       cptra_uc_rst_b;

    logic        [31:0]         ic_haddr        ;
    logic        [2:0]          ic_hburst       ;
    logic                       ic_hmastlock    ;
    logic        [3:0]          ic_hprot        ;
    logic        [2:0]          ic_hsize        ;
    logic        [1:0]          ic_htrans       ;
    logic                       ic_hwrite       ;
    logic        [63:0]         ic_hrdata       ;
    logic                       ic_hready       ;
    logic                       ic_hresp        ;

    logic        [31:0]         lsu_haddr       ;
    logic        [2:0]          lsu_hburst      ;
    logic                       lsu_hmastlock   ;
    logic        [3:0]          lsu_hprot       ;
    logic        [2:0]          lsu_hsize       ;
    logic        [1:0]          lsu_htrans      ;
    logic                       lsu_hwrite      ;
    logic        [63:0]         lsu_hrdata      ;
    logic        [63:0]         lsu_hwdata      ;
    logic                       lsu_hready      ;
    logic                       lsu_hresp       ;

    logic        [31:0]         sb_haddr        ;
    logic        [2:0]          sb_hburst       ;
    logic                       sb_hmastlock    ;
    logic        [3:0]          sb_hprot        ;
    logic        [2:0]          sb_hsize        ;
    logic        [1:0]          sb_htrans       ;
    logic                       sb_hwrite       ;

    logic        [63:0]         sb_hrdata       ;
    logic        [63:0]         sb_hwdata       ;
    logic                       sb_hready       ;
    logic                       sb_hresp        ;

    logic        [31:0]         trace_rv_i_insn_ip;
    logic        [31:0]         trace_rv_i_address_ip;
    logic                       trace_rv_i_valid_ip;
    logic                       trace_rv_i_exception_ip;
    logic        [4:0]          trace_rv_i_ecause_ip;
    logic                       trace_rv_i_interrupt_ip;
    logic        [31:0]         trace_rv_i_tval_ip;

    logic                       o_debug_mode_status;


    logic                       o_cpu_halt_ack;
    logic                       o_cpu_halt_status;
    logic                       o_cpu_run_ack;

    logic                       mailbox_write;
    logic        [63:0]         dma_hrdata       ;
    logic        [63:0]         dma_hwdata       ;
    logic                       dma_hready       ;
    logic                       dma_hresp        ;

    logic                       mpc_debug_halt_req;
    logic                       mpc_debug_run_req;
    logic                       mpc_reset_run_req;
    logic                       mpc_debug_halt_ack;
    logic                       mpc_debug_run_ack;
    logic                       debug_brkpt_status;

    int                         cycleCnt;
    logic                       mailbox_data_val;

    wire                        dma_hready_out;
    int                         commit_count;

    logic                       wb_valid;
    logic [4:0]                 wb_dest;
    logic [31:0]                wb_data;

`ifdef RV_BUILD_AXI4
   //-------------------------- LSU AXI signals--------------------------
   // AXI Write Channels
    wire                        lsu_axi_awvalid;
    wire                        lsu_axi_awready;
    wire [`RV_LSU_BUS_TAG-1:0]  lsu_axi_awid;
    wire [31:0]                 lsu_axi_awaddr;
    wire [3:0]                  lsu_axi_awregion;
    wire [7:0]                  lsu_axi_awlen;
    wire [2:0]                  lsu_axi_awsize;
    wire [1:0]                  lsu_axi_awburst;
    wire                        lsu_axi_awlock;
    wire [3:0]                  lsu_axi_awcache;
    wire [2:0]                  lsu_axi_awprot;
    wire [3:0]                  lsu_axi_awqos;

    wire                        lsu_axi_wvalid;
    wire                        lsu_axi_wready;
    wire [63:0]                 lsu_axi_wdata;
    wire [7:0]                  lsu_axi_wstrb;
    wire                        lsu_axi_wlast;

    wire                        lsu_axi_bvalid;
    wire                        lsu_axi_bready;
    wire [1:0]                  lsu_axi_bresp;
    wire [`RV_LSU_BUS_TAG-1:0]  lsu_axi_bid;

    // AXI Read Channels
    wire                        lsu_axi_arvalid;
    wire                        lsu_axi_arready;
    wire [`RV_LSU_BUS_TAG-1:0]  lsu_axi_arid;
    wire [31:0]                 lsu_axi_araddr;
    wire [3:0]                  lsu_axi_arregion;
    wire [7:0]                  lsu_axi_arlen;
    wire [2:0]                  lsu_axi_arsize;
    wire [1:0]                  lsu_axi_arburst;
    wire                        lsu_axi_arlock;
    wire [3:0]                  lsu_axi_arcache;
    wire [2:0]                  lsu_axi_arprot;
    wire [3:0]                  lsu_axi_arqos;

    wire                        lsu_axi_rvalid;
    wire                        lsu_axi_rready;
    wire [`RV_LSU_BUS_TAG-1:0]  lsu_axi_rid;
    wire [63:0]                 lsu_axi_rdata;
    wire [1:0]                  lsu_axi_rresp;
    wire                        lsu_axi_rlast;

    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    wire                        ifu_axi_awvalid;
    wire                        ifu_axi_awready;
    wire [`RV_IFU_BUS_TAG-1:0]  ifu_axi_awid;
    wire [31:0]                 ifu_axi_awaddr;
    wire [3:0]                  ifu_axi_awregion;
    wire [7:0]                  ifu_axi_awlen;
    wire [2:0]                  ifu_axi_awsize;
    wire [1:0]                  ifu_axi_awburst;
    wire                        ifu_axi_awlock;
    wire [3:0]                  ifu_axi_awcache;
    wire [2:0]                  ifu_axi_awprot;
    wire [3:0]                  ifu_axi_awqos;

    wire                        ifu_axi_wvalid;
    wire                        ifu_axi_wready;
    wire [63:0]                 ifu_axi_wdata;
    wire [7:0]                  ifu_axi_wstrb;
    wire                        ifu_axi_wlast;

    wire                        ifu_axi_bvalid;
    wire                        ifu_axi_bready;
    wire [1:0]                  ifu_axi_bresp;
    wire [`RV_IFU_BUS_TAG-1:0]  ifu_axi_bid;

    // AXI Read Channels
    wire                        ifu_axi_arvalid;
    wire                        ifu_axi_arready;
    wire [`RV_IFU_BUS_TAG-1:0]  ifu_axi_arid;
    wire [31:0]                 ifu_axi_araddr;
    wire [3:0]                  ifu_axi_arregion;
    wire [7:0]                  ifu_axi_arlen;
    wire [2:0]                  ifu_axi_arsize;
    wire [1:0]                  ifu_axi_arburst;
    wire                        ifu_axi_arlock;
    wire [3:0]                  ifu_axi_arcache;
    wire [2:0]                  ifu_axi_arprot;
    wire [3:0]                  ifu_axi_arqos;

    wire                        ifu_axi_rvalid;
    wire                        ifu_axi_rready;
    wire [`RV_IFU_BUS_TAG-1:0]  ifu_axi_rid;
    wire [63:0]                 ifu_axi_rdata;
    wire [1:0]                  ifu_axi_rresp;
    wire                        ifu_axi_rlast;

    //-------------------------- SB AXI signals--------------------------
    // AXI Write Channels
    wire                        sb_axi_awvalid;
    wire                        sb_axi_awready;
    wire [`RV_SB_BUS_TAG-1:0]   sb_axi_awid;
    wire [31:0]                 sb_axi_awaddr;
    wire [3:0]                  sb_axi_awregion;
    wire [7:0]                  sb_axi_awlen;
    wire [2:0]                  sb_axi_awsize;
    wire [1:0]                  sb_axi_awburst;
    wire                        sb_axi_awlock;
    wire [3:0]                  sb_axi_awcache;
    wire [2:0]                  sb_axi_awprot;
    wire [3:0]                  sb_axi_awqos;

    wire                        sb_axi_wvalid;
    wire                        sb_axi_wready;
    wire [63:0]                 sb_axi_wdata;
    wire [7:0]                  sb_axi_wstrb;
    wire                        sb_axi_wlast;

    wire                        sb_axi_bvalid;
    wire                        sb_axi_bready;
    wire [1:0]                  sb_axi_bresp;
    wire [`RV_SB_BUS_TAG-1:0]   sb_axi_bid;

    // AXI Read Channels
    wire                        sb_axi_arvalid;
    wire                        sb_axi_arready;
    wire [`RV_SB_BUS_TAG-1:0]   sb_axi_arid;
    wire [31:0]                 sb_axi_araddr;
    wire [3:0]                  sb_axi_arregion;
    wire [7:0]                  sb_axi_arlen;
    wire [2:0]                  sb_axi_arsize;
    wire [1:0]                  sb_axi_arburst;
    wire                        sb_axi_arlock;
    wire [3:0]                  sb_axi_arcache;
    wire [2:0]                  sb_axi_arprot;
    wire [3:0]                  sb_axi_arqos;

    wire                        sb_axi_rvalid;
    wire                        sb_axi_rready;
    wire [`RV_SB_BUS_TAG-1:0]   sb_axi_rid;
    wire [63:0]                 sb_axi_rdata;
    wire [1:0]                  sb_axi_rresp;
    wire                        sb_axi_rlast;

   //-------------------------- DMA AXI signals--------------------------
   // AXI Write Channels
    wire                        dma_axi_awvalid;
    wire                        dma_axi_awready;
    wire [`RV_DMA_BUS_TAG-1:0]  dma_axi_awid;
    wire [31:0]                 dma_axi_awaddr;
    wire [2:0]                  dma_axi_awsize;
    wire [2:0]                  dma_axi_awprot;
    wire [7:0]                  dma_axi_awlen;
    wire [1:0]                  dma_axi_awburst;


    wire                        dma_axi_wvalid;
    wire                        dma_axi_wready;
    wire [63:0]                 dma_axi_wdata;
    wire [7:0]                  dma_axi_wstrb;
    wire                        dma_axi_wlast;

    wire                        dma_axi_bvalid;
    wire                        dma_axi_bready;
    wire [1:0]                  dma_axi_bresp;
    wire [`RV_DMA_BUS_TAG-1:0]  dma_axi_bid;

    // AXI Read Channels
    wire                        dma_axi_arvalid;
    wire                        dma_axi_arready;
    wire [`RV_DMA_BUS_TAG-1:0]  dma_axi_arid;
    wire [31:0]                 dma_axi_araddr;
    wire [2:0]                  dma_axi_arsize;
    wire [2:0]                  dma_axi_arprot;
    wire [7:0]                  dma_axi_arlen;
    wire [1:0]                  dma_axi_arburst;

    wire                        dma_axi_rvalid;
    wire                        dma_axi_rready;
    wire [`RV_DMA_BUS_TAG-1:0]  dma_axi_rid;
    wire [63:0]                 dma_axi_rdata;
    wire [1:0]                  dma_axi_rresp;
    wire                        dma_axi_rlast;

    wire                        lmem_axi_arvalid;
    wire                        lmem_axi_arready;

    wire                        lmem_axi_rvalid;
    wire [`RV_LSU_BUS_TAG-1:0]  lmem_axi_rid;
    wire [1:0]                  lmem_axi_rresp;
    wire [63:0]                 lmem_axi_rdata;
    wire                        lmem_axi_rlast;
    wire                        lmem_axi_rready;

    wire                        lmem_axi_awvalid;
    wire                        lmem_axi_awready;

    wire                        lmem_axi_wvalid;
    wire                        lmem_axi_wready;

    wire [1:0]                  lmem_axi_bresp;
    wire                        lmem_axi_bvalid;
    wire [`RV_LSU_BUS_TAG-1:0]  lmem_axi_bid;
    wire                        lmem_axi_bready;

`endif

    //========================================================================
    // AHB Slave ports. 
    // Slave 0: LMEM
    // Slave 1: DMA Slave port
    //========================================================================
    AHB_BUS #(
        .AHB_ADDR_WIDTH(`AHB_HADDR_SIZE),
        .AHB_DATA_WIDTH(`AHB_HDATA_SIZE)
    )
    s_slave[`AHB_SLAVES_NUM-1:0]();

    //========================================================================
    // AHB Master ports
    //========================================================================
    AHB_BUS #(
        .AHB_ADDR_WIDTH(`AHB_HADDR_SIZE),
        .AHB_DATA_WIDTH(`AHB_HDATA_SIZE)
    )
    s_smaster();

    //========================================================================
    // AHB Interface and decoder logic instance
    //========================================================================
    ahb_node_wrap #(
        .NB_SLAVES        (`AHB_SLAVES_NUM),
        .AHB_ADDR_WIDTH   (`AHB_HADDR_SIZE),
        .AHB_DATA_WIDTH   (`AHB_HDATA_SIZE),
        .BYPASS           (             0 )
    )
    ahb_node_wrap_i (
        .hclk             ( core_clk          ),
        .hreset_n         ( cptra_uc_rst_b    ),
        .ahb_slaves       ( s_slave           ),
        .ahb_master       ( s_smaster         ),
        .start_addr_i     ( `SLAVE_BASE_ADDR  ),
        .end_addr_i       ( `SLAVE_MASK_ADDR  )
    );


   //=========================================================================-
   // RTL instance
   //=========================================================================-
//FIXME TIE OFFS
logic [31:0] jtag_id;
logic [31:0] reset_vector;
logic [31:0] nmi_vector;
logic nmi_int;

assign jtag_id[31:28] = 4'b1;
assign jtag_id[27:12] = '0;
assign jtag_id[11:1]  = 11'h45;
assign reset_vector = `RV_RESET_VEC;
assign nmi_vector   = 32'hee000000;
assign nmi_int   = 0;

el2_swerv_wrapper rvtop (
    .rst_l                  ( cptra_uc_rst_b),
    .dbg_rst_l              ( cptra_pwrgood), 
    .clk                    ( core_clk      ),
    .rst_vec                ( reset_vector[31:1]),
    .nmi_int                ( nmi_int       ),
    .nmi_vec                ( nmi_vector[31:1]),
    .jtag_id                ( jtag_id[31:1]),

`ifdef RV_BUILD_AHB_LITE
    .haddr                  ( ic_haddr      ),
    .hburst                 ( ic_hburst     ),
    .hmastlock              ( ic_hmastlock  ),
    .hprot                  ( ic_hprot      ),
    .hsize                  ( ic_hsize      ),
    .htrans                 ( ic_htrans     ),
    .hwrite                 ( ic_hwrite     ),

    .hrdata                 ( ic_hrdata[63:0]),
    .hready                 ( ic_hready     ),
    .hresp                  ( ic_hresp      ),

    //---------------------------------------------------------------
    // Debug AHB Master
    //---------------------------------------------------------------
    .sb_haddr               ( sb_haddr      ),
    .sb_hburst              ( sb_hburst     ),
    .sb_hmastlock           ( sb_hmastlock  ),
    .sb_hprot               ( sb_hprot      ),
    .sb_hsize               ( sb_hsize      ),
    .sb_htrans              ( sb_htrans     ),
    .sb_hwrite              ( sb_hwrite     ),
    .sb_hwdata              ( sb_hwdata     ),

    .sb_hrdata              ( sb_hrdata     ),
    .sb_hready              ( sb_hready     ),
    .sb_hresp               ( sb_hresp      ),

    //---------------------------------------------------------------
    // LSU AHB Master
    //---------------------------------------------------------------
    .lsu_haddr              ( s_smaster.haddr       ),
    .lsu_hburst             ( s_smaster.hburst      ),
    .lsu_hmastlock          ( s_smaster.hmastlock   ),
    .lsu_hprot              ( s_smaster.hprot       ),
    .lsu_hsize              ( s_smaster.hsize       ),
    .lsu_htrans             ( s_smaster.htrans      ),
    .lsu_hwrite             ( s_smaster.hwrite      ),
    .lsu_hwdata             ( s_smaster.hwdata      ),

    .lsu_hrdata             ( s_smaster.hrdata[63:0]),
    .lsu_hready             ( s_smaster.hready      ),
    .lsu_hresp              ( s_smaster.hresp       ),

    //---------------------------------------------------------------
    // DMA Slave
    //---------------------------------------------------------------
    .dma_haddr              ( s_slave[1].haddr ),
    .dma_hburst             ( s_slave[1].hburst ),
    .dma_hmastlock          ( s_slave[1].hmastlock ),
    .dma_hprot              ( s_slave[1].hprot ),
    .dma_hsize              ( s_slave[1].hsize ),
    .dma_htrans             ( s_slave[1].htrans ),
    .dma_hwrite             ( s_slave[1].hwrite ),
    .dma_hwdata             ( s_slave[1].hwdata ),

    .dma_hrdata             ( s_slave[1].hrdata    ),
    .dma_hresp              ( s_slave[1].hresp     ),
    .dma_hsel               ( s_slave[1].hsel            ),
    .dma_hreadyin           ( s_slave[1].hreadyout  ),
    .dma_hreadyout          ( s_slave[1].hreadyout  ),
`endif
`ifdef RV_BUILD_AXI4
    //-------------------------- LSU AXI signals--------------------------
    // AXI Write Channels
    .lsu_axi_awvalid        (lsu_axi_awvalid),
    .lsu_axi_awready        (lsu_axi_awready),
    .lsu_axi_awid           (lsu_axi_awid),
    .lsu_axi_awaddr         (lsu_axi_awaddr),
    .lsu_axi_awregion       (lsu_axi_awregion),
    .lsu_axi_awlen          (lsu_axi_awlen),
    .lsu_axi_awsize         (lsu_axi_awsize),
    .lsu_axi_awburst        (lsu_axi_awburst),
    .lsu_axi_awlock         (lsu_axi_awlock),
    .lsu_axi_awcache        (lsu_axi_awcache),
    .lsu_axi_awprot         (lsu_axi_awprot),
    .lsu_axi_awqos          (lsu_axi_awqos),

    .lsu_axi_wvalid         (lsu_axi_wvalid),
    .lsu_axi_wready         (lsu_axi_wready),
    .lsu_axi_wdata          (lsu_axi_wdata),
    .lsu_axi_wstrb          (lsu_axi_wstrb),
    .lsu_axi_wlast          (lsu_axi_wlast),

    .lsu_axi_bvalid         (lsu_axi_bvalid),
    .lsu_axi_bready         (lsu_axi_bready),
    .lsu_axi_bresp          (lsu_axi_bresp),
    .lsu_axi_bid            (lsu_axi_bid),


    .lsu_axi_arvalid        (lsu_axi_arvalid),
    .lsu_axi_arready        (lsu_axi_arready),
    .lsu_axi_arid           (lsu_axi_arid),
    .lsu_axi_araddr         (lsu_axi_araddr),
    .lsu_axi_arregion       (lsu_axi_arregion),
    .lsu_axi_arlen          (lsu_axi_arlen),
    .lsu_axi_arsize         (lsu_axi_arsize),
    .lsu_axi_arburst        (lsu_axi_arburst),
    .lsu_axi_arlock         (lsu_axi_arlock),
    .lsu_axi_arcache        (lsu_axi_arcache),
    .lsu_axi_arprot         (lsu_axi_arprot),
    .lsu_axi_arqos          (lsu_axi_arqos),

    .lsu_axi_rvalid         (lsu_axi_rvalid),
    .lsu_axi_rready         (lsu_axi_rready),
    .lsu_axi_rid            (lsu_axi_rid),
    .lsu_axi_rdata          (lsu_axi_rdata),
    .lsu_axi_rresp          (lsu_axi_rresp),
    .lsu_axi_rlast          (lsu_axi_rlast),

    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    .ifu_axi_awvalid        (ifu_axi_awvalid),
    .ifu_axi_awready        (ifu_axi_awready),
    .ifu_axi_awid           (ifu_axi_awid),
    .ifu_axi_awaddr         (ifu_axi_awaddr),
    .ifu_axi_awregion       (ifu_axi_awregion),
    .ifu_axi_awlen          (ifu_axi_awlen),
    .ifu_axi_awsize         (ifu_axi_awsize),
    .ifu_axi_awburst        (ifu_axi_awburst),
    .ifu_axi_awlock         (ifu_axi_awlock),
    .ifu_axi_awcache        (ifu_axi_awcache),
    .ifu_axi_awprot         (ifu_axi_awprot),
    .ifu_axi_awqos          (ifu_axi_awqos),

    .ifu_axi_wvalid         (ifu_axi_wvalid),
    .ifu_axi_wready         (ifu_axi_wready),
    .ifu_axi_wdata          (ifu_axi_wdata),
    .ifu_axi_wstrb          (ifu_axi_wstrb),
    .ifu_axi_wlast          (ifu_axi_wlast),

    .ifu_axi_bvalid         (ifu_axi_bvalid),
    .ifu_axi_bready         (ifu_axi_bready),
    .ifu_axi_bresp          (ifu_axi_bresp),
    .ifu_axi_bid            (ifu_axi_bid),

    .ifu_axi_arvalid        (ifu_axi_arvalid),
    .ifu_axi_arready        (ifu_axi_arready),
    .ifu_axi_arid           (ifu_axi_arid),
    .ifu_axi_araddr         (ifu_axi_araddr),
    .ifu_axi_arregion       (ifu_axi_arregion),
    .ifu_axi_arlen          (ifu_axi_arlen),
    .ifu_axi_arsize         (ifu_axi_arsize),
    .ifu_axi_arburst        (ifu_axi_arburst),
    .ifu_axi_arlock         (ifu_axi_arlock),
    .ifu_axi_arcache        (ifu_axi_arcache),
    .ifu_axi_arprot         (ifu_axi_arprot),
    .ifu_axi_arqos          (ifu_axi_arqos),

    .ifu_axi_rvalid         (ifu_axi_rvalid),
    .ifu_axi_rready         (ifu_axi_rready),
    .ifu_axi_rid            (ifu_axi_rid),
    .ifu_axi_rdata          (ifu_axi_rdata),
    .ifu_axi_rresp          (ifu_axi_rresp),
    .ifu_axi_rlast          (ifu_axi_rlast),

    //-------------------------- SB AXI signals--------------------------
    // AXI Write Channels
    .sb_axi_awvalid         (sb_axi_awvalid),
    .sb_axi_awready         (sb_axi_awready),
    .sb_axi_awid            (sb_axi_awid),
    .sb_axi_awaddr          (sb_axi_awaddr),
    .sb_axi_awregion        (sb_axi_awregion),
    .sb_axi_awlen           (sb_axi_awlen),
    .sb_axi_awsize          (sb_axi_awsize),
    .sb_axi_awburst         (sb_axi_awburst),
    .sb_axi_awlock          (sb_axi_awlock),
    .sb_axi_awcache         (sb_axi_awcache),
    .sb_axi_awprot          (sb_axi_awprot),
    .sb_axi_awqos           (sb_axi_awqos),

    .sb_axi_wvalid          (sb_axi_wvalid),
    .sb_axi_wready          (sb_axi_wready),
    .sb_axi_wdata           (sb_axi_wdata),
    .sb_axi_wstrb           (sb_axi_wstrb),
    .sb_axi_wlast           (sb_axi_wlast),

    .sb_axi_bvalid          (sb_axi_bvalid),
    .sb_axi_bready          (sb_axi_bready),
    .sb_axi_bresp           (sb_axi_bresp),
    .sb_axi_bid             (sb_axi_bid),


    .sb_axi_arvalid         (sb_axi_arvalid),
    .sb_axi_arready         (sb_axi_arready),
    .sb_axi_arid            (sb_axi_arid),
    .sb_axi_araddr          (sb_axi_araddr),
    .sb_axi_arregion        (sb_axi_arregion),
    .sb_axi_arlen           (sb_axi_arlen),
    .sb_axi_arsize          (sb_axi_arsize),
    .sb_axi_arburst         (sb_axi_arburst),
    .sb_axi_arlock          (sb_axi_arlock),
    .sb_axi_arcache         (sb_axi_arcache),
    .sb_axi_arprot          (sb_axi_arprot),
    .sb_axi_arqos           (sb_axi_arqos),

    .sb_axi_rvalid          (sb_axi_rvalid),
    .sb_axi_rready          (sb_axi_rready),
    .sb_axi_rid             (sb_axi_rid),
    .sb_axi_rdata           (sb_axi_rdata),
    .sb_axi_rresp           (sb_axi_rresp),
    .sb_axi_rlast           (sb_axi_rlast),

    //-------------------------- DMA AXI signals--------------------------
    // AXI Write Channels
    .dma_axi_awvalid        (dma_axi_awvalid),
    .dma_axi_awready        (dma_axi_awready),
    .dma_axi_awid           ('0),
    .dma_axi_awaddr         (lsu_axi_awaddr),
    .dma_axi_awsize         (lsu_axi_awsize),
    .dma_axi_awprot         (lsu_axi_awprot),
    .dma_axi_awlen          (lsu_axi_awlen),
    .dma_axi_awburst        (lsu_axi_awburst),


    .dma_axi_wvalid         (dma_axi_wvalid),
    .dma_axi_wready         (dma_axi_wready),
    .dma_axi_wdata          (lsu_axi_wdata),
    .dma_axi_wstrb          (lsu_axi_wstrb),
    .dma_axi_wlast          (lsu_axi_wlast),

    .dma_axi_bvalid         (dma_axi_bvalid),
    .dma_axi_bready         (dma_axi_bready),
    .dma_axi_bresp          (dma_axi_bresp),
    .dma_axi_bid            (),


    .dma_axi_arvalid        (dma_axi_arvalid),
    .dma_axi_arready        (dma_axi_arready),
    .dma_axi_arid           ('0),
    .dma_axi_araddr         (lsu_axi_araddr),
    .dma_axi_arsize         (lsu_axi_arsize),
    .dma_axi_arprot         (lsu_axi_arprot),
    .dma_axi_arlen          (lsu_axi_arlen),
    .dma_axi_arburst        (lsu_axi_arburst),

    .dma_axi_rvalid         (dma_axi_rvalid),
    .dma_axi_rready         (dma_axi_rready),
    .dma_axi_rid            (),
    .dma_axi_rdata          (dma_axi_rdata),
    .dma_axi_rresp          (dma_axi_rresp),
    .dma_axi_rlast          (dma_axi_rlast),
`endif
    .timer_int              ( 1'b0     ),
    .extintsrc_req          ( '0  ),

    .lsu_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB master interface
    .ifu_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB master interface
    .dbg_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB Debug master interface
    .dma_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB slave interface

    .trace_rv_i_insn_ip     (trace_rv_i_insn_ip),
    .trace_rv_i_address_ip  (trace_rv_i_address_ip),
    .trace_rv_i_valid_ip    (trace_rv_i_valid_ip),
    .trace_rv_i_exception_ip(trace_rv_i_exception_ip),
    .trace_rv_i_ecause_ip   (trace_rv_i_ecause_ip),
    .trace_rv_i_interrupt_ip(trace_rv_i_interrupt_ip),
    .trace_rv_i_tval_ip     (trace_rv_i_tval_ip),

    .jtag_tck               ( jtag_tck  ),
    .jtag_tms               ( jtag_tms  ),
    .jtag_tdi               ( jtag_tdi  ),
    .jtag_trst_n            ( jtag_trst_n  ),
    .jtag_tdo               ( jtag_tdo ),

    .mpc_debug_halt_ack     ( mpc_debug_halt_ack),
    .mpc_debug_halt_req     ( 1'b0),
    .mpc_debug_run_ack      ( mpc_debug_run_ack),
    .mpc_debug_run_req      ( 1'b1),
    .mpc_reset_run_req      ( 1'b1),             // Start running after reset
     .debug_brkpt_status    (debug_brkpt_status),

    .i_cpu_halt_req         ( 1'b0  ),    // Async halt req to CPU
    .o_cpu_halt_ack         ( o_cpu_halt_ack ),    // core response to halt
    .o_cpu_halt_status      ( o_cpu_halt_status ), // 1'b1 indicates core is halted
    .i_cpu_run_req          ( 1'b0  ),     // Async restart req to CPU
    .o_debug_mode_status    (o_debug_mode_status),
    .o_cpu_run_ack          ( o_cpu_run_ack ),     // Core response to run req

    .dec_tlu_perfcnt0       (),
    .dec_tlu_perfcnt1       (),
    .dec_tlu_perfcnt2       (),
    .dec_tlu_perfcnt3       (),

// remove mems DFT pins for opensource
    .dccm_ext_in_pkt        ('0),
    .iccm_ext_in_pkt        ('0),
    .ic_data_ext_in_pkt     ('0),
    .ic_tag_ext_in_pkt      ('0),

    .soft_int               ('0),
    .core_id                ('0),
    .scan_mode              ( 1'b0 ),         // To enable scan mode
    .mbist_mode             ( 1'b0 )        // to enable mbist

);

assign s_smaster.hsel = 1'b1;



   //=========================================================================-
   // AHB I$ instance
   //=========================================================================-
`ifdef RV_BUILD_AHB_LITE

ahb_sif imem (
     // Inputs
     .HWDATA(64'h0),
     .HCLK(core_clk),
     .HSEL(1'b1),
     .HPROT(ic_hprot),
     .HWRITE(ic_hwrite),
     .HTRANS(ic_htrans),
     .HSIZE(ic_hsize),
     .HREADY(ic_hready),
     .HRESETn(cptra_uc_rst_b),
     .HADDR(ic_haddr),
     .HBURST(ic_hburst),

     // Outputs
     .HREADYOUT(ic_hready),
     .HRESP(ic_hresp),
     .HRDATA(ic_hrdata[63:0])
);


ahb_sif lmem (
     // Inputs
     .HWDATA(s_slave[0].hwdata),
     .HCLK(core_clk),
     .HSEL(s_slave[0].hsel), //disabling Lmem for testing DMA access from LSU
     .HPROT(s_slave[0].hprot),
     .HWRITE(s_slave[0].hwrite),
     .HTRANS(s_slave[0].htrans),
     .HSIZE(s_slave[0].hsize),
     .HREADY(s_slave[0].hready),
     .HRESETn(cptra_uc_rst_b),
     .HADDR(s_slave[0].haddr),
     .HBURST(s_slave[0].hburst),
    //.HMASTLOCK(s_slave[0].hmastlock),

     // Outputs
     .HREADYOUT(s_slave[0].hreadyout),
     .HRESP(s_slave[0].hresp),
     .HRDATA(s_slave[0].hrdata[63:0])
);

sha512_ctrl #(
    .AHB_DATA_WIDTH (64),
    .AHB_ADDR_WIDTH (32),
    .BYPASS_SEL     (0)
) sha512 (
    .clk            (core_clk),
    .reset_n        (cptra_uc_rst_b),
    .haddr_i        (s_slave[2].haddr),
    .hwdata_i       (s_slave[2].hwdata),
    .hsel_i         (s_slave[2].hsel),
    .hwrite_i       (s_slave[2].hwrite),
    .hmastlock_i    (s_slave[2].hmastlock),
    .hready_i       (s_slave[2].hready),
    .htrans_i       (s_slave[2].htrans),
    .hprot_i        (s_slave[2].hprot),
    .hburst_i       (s_slave[2].hburst),
    .hsize_i        (s_slave[2].hsize),
    .hresp_o        (s_slave[2].hresp),
    .hreadyout_o    (s_slave[2].hreadyout),
    .hrdata_o       (s_slave[2].hrdata)
);

aes_ctrl #(
    .AHB_DATA_WIDTH (64),
    .AHB_ADDR_WIDTH (32),
    .BYPASS_SEL     (0)
) aes (
    .clk            (core_clk),
    .reset_n        (cptra_uc_rst_b),
    .haddr_i        (s_slave[3].haddr),
    .hwdata_i       (s_slave[3].hwdata),
    .hsel_i         (s_slave[3].hsel),
    .hwrite_i       (s_slave[3].hwrite),
    .hmastlock_i    (s_slave[3].hmastlock),
    .hready_i       (s_slave[3].hready),
    .htrans_i       (s_slave[3].htrans),
    .hprot_i        (s_slave[3].hprot),
    .hburst_i       (s_slave[3].hburst),
    .hsize_i        (s_slave[3].hsize),
    .hresp_o        (s_slave[3].hresp),
    .hreadyout_o    (s_slave[3].hreadyout),
    .hrdata_o       (s_slave[3].hrdata)
);


`endif
`ifdef RV_BUILD_AXI4
axi_slv #(.TAGW(`RV_IFU_BUS_TAG)) imem(
    .aclk(core_clk),
    .rst_l(cptra_uc_rst_b),
    .arvalid(ifu_axi_arvalid),
    .arready(ifu_axi_arready),
    .araddr(ifu_axi_araddr),
    .arid(ifu_axi_arid),
    .arlen(ifu_axi_arlen),
    .arburst(ifu_axi_arburst),
    .arsize(ifu_axi_arsize),

    .rvalid(ifu_axi_rvalid),
    .rready(ifu_axi_rready),
    .rdata(ifu_axi_rdata),
    .rresp(ifu_axi_rresp),
    .rid(ifu_axi_rid),
    .rlast(ifu_axi_rlast),

    .awvalid(1'b0),
    .awready(),
    .awaddr('0),
    .awid('0),
    .awlen('0),
    .awburst('0),
    .awsize('0),

    .wdata('0),
    .wstrb('0),
    .wvalid(1'b0),
    .wready(),

    .bvalid(),
    .bready(1'b0),
    .bresp(),
    .bid()
);

defparam lmem.TAGW =`RV_LSU_BUS_TAG;

//axi_slv #(.TAGW(`RV_LSU_BUS_TAG)) lmem(
axi_slv  lmem(
    .aclk(core_clk),
    .rst_l(cptra_uc_rst_b),
    .arvalid(lmem_axi_arvalid),
    .arready(lmem_axi_arready),
    .araddr(lsu_axi_araddr),
    .arid(lsu_axi_arid),
    .arlen(lsu_axi_arlen),
    .arburst(lsu_axi_arburst),
    .arsize(lsu_axi_arsize),

    .rvalid(lmem_axi_rvalid),
    .rready(lmem_axi_rready),
    .rdata(lmem_axi_rdata),
    .rresp(lmem_axi_rresp),
    .rid(lmem_axi_rid),
    .rlast(lmem_axi_rlast),

    .awvalid(lmem_axi_awvalid),
    .awready(lmem_axi_awready),
    .awaddr(lsu_axi_awaddr),
    .awid(lsu_axi_awid),
    .awlen(lsu_axi_awlen),
    .awburst(lsu_axi_awburst),
    .awsize(lsu_axi_awsize),

    .wdata(lsu_axi_wdata),
    .wstrb(lsu_axi_wstrb),
    .wvalid(lmem_axi_wvalid),
    .wready(lmem_axi_wready),

    .bvalid(lmem_axi_bvalid),
    .bready(lmem_axi_bready),
    .bresp(lmem_axi_bresp),
    .bid(lmem_axi_bid)
);

axi_lsu_dma_bridge # (`RV_LSU_BUS_TAG,`RV_LSU_BUS_TAG ) bridge(
    .clk(core_clk),
    .reset_l(cptra_uc_rst_b),

    .m_arvalid(lsu_axi_arvalid),
    .m_arid(lsu_axi_arid),
    .m_araddr(lsu_axi_araddr),
    .m_arready(lsu_axi_arready),

    .m_rvalid(lsu_axi_rvalid),
    .m_rready(lsu_axi_rready),
    .m_rdata(lsu_axi_rdata),
    .m_rid(lsu_axi_rid),
    .m_rresp(lsu_axi_rresp),
    .m_rlast(lsu_axi_rlast),

    .m_awvalid(lsu_axi_awvalid),
    .m_awid(lsu_axi_awid),
    .m_awaddr(lsu_axi_awaddr),
    .m_awready(lsu_axi_awready),

    .m_wvalid(lsu_axi_wvalid),
    .m_wready(lsu_axi_wready),

    .m_bresp(lsu_axi_bresp),
    .m_bvalid(lsu_axi_bvalid),
    .m_bid(lsu_axi_bid),
    .m_bready(lsu_axi_bready),

    .s0_arvalid(lmem_axi_arvalid),
    .s0_arready(lmem_axi_arready),

    .s0_rvalid(lmem_axi_rvalid),
    .s0_rid(lmem_axi_rid),
    .s0_rresp(lmem_axi_rresp),
    .s0_rdata(lmem_axi_rdata),
    .s0_rlast(lmem_axi_rlast),
    .s0_rready(lmem_axi_rready),

    .s0_awvalid(lmem_axi_awvalid),
    .s0_awready(lmem_axi_awready),

    .s0_wvalid(lmem_axi_wvalid),
    .s0_wready(lmem_axi_wready),

    .s0_bresp(lmem_axi_bresp),
    .s0_bvalid(lmem_axi_bvalid),
    .s0_bid(lmem_axi_bid),
    .s0_bready(lmem_axi_bready),


    .s1_arvalid(dma_axi_arvalid),
    .s1_arready(dma_axi_arready),

    .s1_rvalid(dma_axi_rvalid),
    .s1_rresp(dma_axi_rresp),
    .s1_rdata(dma_axi_rdata),
    .s1_rlast(dma_axi_rlast),
    .s1_rready(dma_axi_rready),

    .s1_awvalid(dma_axi_awvalid),
    .s1_awready(dma_axi_awready),

    .s1_wvalid(dma_axi_wvalid),
    .s1_wready(dma_axi_wready),

    .s1_bresp(dma_axi_bresp),
    .s1_bvalid(dma_axi_bvalid),
    .s1_bready(dma_axi_bready)
);


`endif

//Instantiation of mailbox
mbox_top #(
    .AHB_ADDR_WIDTH(`AHB_HADDR_SIZE),
    .AHB_DATA_WIDTH(`AHB_HDATA_SIZE),
    .APB_ADDR_WIDTH(`APB_ADDR_WIDTH),
    .APB_DATA_WIDTH(`APB_DATA_WIDTH),
    .APB_USER_WIDTH(`APB_USER_WIDTH)
    )
    mbox_top1 
    (
    .clk(core_clk),
    .cptra_pwrgood(cptra_pwrgood), 
    .cptra_rst_b(cptra_rst_b),
    //APB Interface with SoC
    .paddr_i(PADDR),
    .psel_i(PSEL),
    .penable_i(PENABLE),
    .pwrite_i(PWRITE),
    .pwdata_i(PWDATA),
    .pauser_i(PAUSER),
    .pready_o(PREADY),
    .prdata_o(PRDATA),
    .pslverr_o(PSLVERR),
    //AHB Interface with uC
    .haddr_i(s_slave[4].haddr), 
    .hwdata_i(s_slave[4].hwdata), 
    .hsel_i(s_slave[4].hsel), 
    .hwrite_i(s_slave[4].hwrite),
    .hmastlock_i(s_slave[4].hmastlock),
    .hready_i(s_slave[4].hready),
    .htrans_i(s_slave[4].htrans),
    .hprot_i(s_slave[4].hprot),
    .hburst_i(s_slave[4].hburst),
    .hsize_i(s_slave[4].hsize),
    .hresp_o(s_slave[4].hresp),
    .hreadyout_o(s_slave[4].hreadyout),
    .hrdata_o(s_slave[4].hrdata),

    .cptra_uc_rst_b (cptra_uc_rst_b) 
);



hmac_ctrl #(
     .AHB_DATA_WIDTH(32),
     .AHB_ADDR_WIDTH(`AHB_HADDR_SIZE),
     .BYPASS_HSEL(0)
)hmac (
     .clk(core_clk),
     .reset_n       (cptra_uc_rst_b),
     .hadrr_i       (s_slave[5].haddr),
     .hwdata_i      (s_slave[5].hwdata),
     .hsel_i        (s_slave[5].hsel),
     .hwrite_i      (s_slave[5].hwrite),
     .hmastlock_i   (s_slave[5].hmastlock),
     .hready_i      (s_slave[5].hready),
     .htrans_i      (s_slave[5].htrans),
     .hprot_i       (s_slave[5].hprot),
     .hburst_i      (s_slave[5].hburst),
     .hsize_i       (s_slave[5].hsize),
     .hresp_o       (s_slave[5].hresp),
     .hreadyout_o   (s_slave[5].hreadyout),
     .hrdata_o      (s_slave[5].hrdata)
);

genvar sva_i;
generate
  for(sva_i= 0; sva_i<`AHB_SLAVES_NUM; sva_i=sva_i+1)
  begin
    `ASSERT_KNOWN(AHB_SLAVE_HADDR_X,        s_slave[sva_i].haddr,       core_clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HWDATA_X,       s_slave[sva_i].hwdata,      core_clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HSEL_X,         s_slave[sva_i].hsel,        core_clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HWRITE_X,       s_slave[sva_i].hwrite,      core_clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HLOCK_X,        s_slave[sva_i].hmastlock,   core_clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HREADY_X,       s_slave[sva_i].hready,      core_clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HTRANS_X,       s_slave[sva_i].htrans,      core_clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HPROT_X,        s_slave[sva_i].hprot,       core_clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HBURS_X,        s_slave[sva_i].hburst,      core_clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HSIZE_X,        s_slave[sva_i].hsize,       core_clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HRESP_X,        s_slave[sva_i].hresp,       core_clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HREADYOUT_X,    s_slave[sva_i].hreadyout,   core_clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HRDATA_X,       s_slave[sva_i].hrdata,      core_clk, cptra_uc_rst_b)
  end
endgenerate

`ASSERT_KNOWN(AHB_MASTER_HADDR_X,        s_smaster.haddr,       core_clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HWDATA_X,       s_smaster.hwdata,      core_clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HSEL_X,         s_smaster.hsel,        core_clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HWRITE_X,       s_smaster.hwrite,      core_clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HLOCK_X,        s_smaster.hmastlock,   core_clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HREADY_X,       s_smaster.hready,      core_clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HTRANS_X,       s_smaster.htrans,      core_clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HPROT_X,        s_smaster.hprot,       core_clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HBURS_X,        s_smaster.hburst,      core_clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HSIZE_X,        s_smaster.hsize,       core_clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HRESP_X,        s_smaster.hresp,       core_clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HRDATA_X,       s_smaster.hrdata,      core_clk, cptra_uc_rst_b)

endmodule