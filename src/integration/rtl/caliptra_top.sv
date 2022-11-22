// SPDX-License-Identifier: Apache-2.0
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

module caliptra_top 
    import el2_swerv_pkg::*;
    import config_pkg::*;
    import kv_defines_pkg::*;
    import soc_ifc_pkg::*;
    (
    input bit                          clk,

    input logic                        cptra_pwrgood,
    input logic                        cptra_rst_b,

    input logic [255:0]                cptra_obf_key,

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

    // Caliptra Memory Export Interface
    el2_mem_if                         el2_mem_export,

    //SRAM interface for mbox
    output logic mbox_sram_cs,
    output logic mbox_sram_we,
    output logic [MBOX_ADDR_W-1:0] mbox_sram_addr,
    output logic [MBOX_DATA_W-1:0] mbox_sram_wdata,
    input  logic [MBOX_DATA_W-1:0] mbox_sram_rdata,

    //SRAM interface for imem
    output logic imem_cs,
    output logic [`IMEM_ADDR_WIDTH-1:0] imem_addr,
    input  logic [`IMEM_DATA_WIDTH-1:0] imem_rdata,

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


    localparam NUM_INTR = `RV_PIC_TOTAL_INT; // 31


    //caliptra reset driven by boot fsm in mailbox
    logic                       cptra_uc_rst_b;
    logic                       cptra_uc_fw_rst_b;

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

    logic [7:0][31:0] cptra_obf_key_reg;
    logic [31:0][31:0] obf_field_entropy;
    logic [11:0][31:0] obf_uds_seed;

    logic iccm_lock;

    // Interrupt Signals
    wire doe_error_intr;
    wire doe_notif_intr;
    wire ecc_error_intr;
    wire ecc_notif_intr;
    wire hmac_error_intr;
    wire hmac_notif_intr;
    wire kv_error_intr;
    wire kv_notif_intr;
    wire sha512_error_intr;
    wire sha512_notif_intr;
    wire sha256_error_intr;
    wire sha256_notif_intr;
    wire qspi_error_intr;
    wire qspi_notif_intr;
    wire uart_error_intr;
    wire uart_notif_intr;
    wire i3c_error_intr;
    wire i3c_notif_intr;
    wire soc_ifc_error_intr;
    wire soc_ifc_notif_intr;
    wire sha_error_intr;
    wire sha_notif_intr;

    logic [NUM_INTR-1:0] intr;

    kv_read_t [`KV_NUM_READ-1:0]  kv_read;
    kv_write_t [`KV_NUM_WRITE-1:0]  kv_write;
    kv_resp_t [`KV_NUM_READ-1:0] kv_resp;

    //mailbox sram gasket
    mbox_sram_req_t mbox_sram_req;
    mbox_sram_resp_t mbox_sram_resp;

    logic clear_secrets;

always_comb begin
    mbox_sram_cs = mbox_sram_req.cs;
    mbox_sram_we = mbox_sram_req.we;
    mbox_sram_addr = mbox_sram_req.addr;
    mbox_sram_wdata = mbox_sram_req.wdata;
    mbox_sram_resp.rdata = mbox_sram_rdata;
end
    //========================================================================
    // AHB Slave ports. 
    // Slave 0: LMEM
    // Slave 1: DMA Slave port
    //========================================================================
    AHB_LITE_BUS_INF #(
        .AHB_LITE_ADDR_WIDTH(`AHB_HADDR_SIZE),
        .AHB_LITE_DATA_WIDTH(`AHB_HDATA_SIZE)
    )
    responder_inst[`AHB_SLAVES_NUM-1:0]();

    //========================================================================
    // AHB Master ports
    //========================================================================
    AHB_LITE_BUS_INF #(
        .AHB_LITE_ADDR_WIDTH(`AHB_HADDR_SIZE),
        .AHB_LITE_DATA_WIDTH(`AHB_HDATA_SIZE)
    )
    initiator_inst();

    //========================================================================
    // AHB Responder Disable
    //========================================================================
    logic [`AHB_SLAVES_NUM-1:0] ahb_lite_resp_disable;
    logic [`AHB_SLAVES_NUM-1:0] ahb_lite_resp_access_blocked;

    //========================================================================
    // AHB Lite Interface and decoder logic instance
    //========================================================================
    ahb_lite_bus #(
        .NUM_RESPONDERS        (`AHB_SLAVES_NUM),
        .AHB_LITE_ADDR_WIDTH   (`AHB_HADDR_SIZE),
        .AHB_LITE_DATA_WIDTH   (`AHB_HDATA_SIZE)
    )
    ahb_lite_bus_i (
        .hclk                          ( clk                         ),
        .hreset_n                      ( cptra_uc_rst_b              ),
        .ahb_lite_responders           ( responder_inst              ),
        .ahb_lite_initiator            ( initiator_inst              ),
        .ahb_lite_resp_disable_i       ( ahb_lite_resp_disable       ),
        .ahb_lite_resp_access_blocked_o( ahb_lite_resp_access_blocked),
        .ahb_lite_start_addr_i         ( `SLAVE_BASE_ADDR            ),
        .ahb_lite_end_addr_i           ( `SLAVE_MASK_ADDR            )
    );
    always_comb ahb_lite_resp_disable[`SLAVE_SEL_DOE]     = 1'b0;
    always_comb ahb_lite_resp_disable[`SLAVE_SEL_ECC]     = 1'b0;
    always_comb ahb_lite_resp_disable[`SLAVE_SEL_HMAC]    = 1'b0;
    always_comb ahb_lite_resp_disable[`SLAVE_SEL_KV]      = 1'b0;
    always_comb ahb_lite_resp_disable[`SLAVE_SEL_SHA512]  = 1'b0;
    always_comb ahb_lite_resp_disable[`SLAVE_SEL_QSPI]    = 1'b0;
    always_comb ahb_lite_resp_disable[`SLAVE_SEL_UART]    = 1'b0;
    always_comb ahb_lite_resp_disable[`SLAVE_SEL_I3C]     = 1'b0;
    always_comb ahb_lite_resp_disable[`SLAVE_SEL_SOC_IFC] = 1'b0;
    always_comb ahb_lite_resp_disable[`SLAVE_SEL_DDMA]    = 1'b0;
    always_comb ahb_lite_resp_disable[`SLAVE_SEL_IDMA]    = iccm_lock;
    always_comb ahb_lite_resp_disable[`SLAVE_SEL_SHA256]  = 1'b0;


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
assign nmi_vector   = 32'h40000000; // TODO this should come from a ctrl reg...
assign nmi_int   = 0;

assign kv_error_intr = 1'b0; // TODO
assign kv_notif_intr = 1'b0; // TODO
assign qspi_error_intr = 1'b0; // TODO
assign qspi_notif_intr = 1'b0; // TODO
assign uart_error_intr = 1'b0; // TODO
assign uart_notif_intr = 1'b0; // TODO
assign i3c_error_intr = 1'b0; // TODO
assign i3c_notif_intr = 1'b0; // TODO

// Vector 0 usage is reserved by SweRV, so bit 0 of the intr wire
// drive Vector 1
always_comb begin
    intr[`SWERV_INTR_VEC_DOE_ERROR    -1]          = doe_error_intr;
    intr[`SWERV_INTR_VEC_DOE_NOTIF    -1]          = doe_notif_intr;
    intr[`SWERV_INTR_VEC_ECC_ERROR    -1]          = ecc_error_intr;
    intr[`SWERV_INTR_VEC_ECC_NOTIF    -1]          = ecc_notif_intr;
    intr[`SWERV_INTR_VEC_HMAC_ERROR   -1]          = hmac_error_intr;
    intr[`SWERV_INTR_VEC_HMAC_NOTIF   -1]          = hmac_notif_intr;
    intr[`SWERV_INTR_VEC_KV_ERROR     -1]          = kv_error_intr;
    intr[`SWERV_INTR_VEC_KV_NOTIF     -1]          = kv_notif_intr;
    intr[`SWERV_INTR_VEC_SHA512_ERROR -1]          = sha512_error_intr;
    intr[`SWERV_INTR_VEC_SHA512_NOTIF -1]          = sha512_notif_intr;
    intr[`SWERV_INTR_VEC_SHA256_ERROR- 1]          = sha256_error_intr;
    intr[`SWERV_INTR_VEC_SHA256_NOTIF -1]          = sha256_notif_intr;
    intr[`SWERV_INTR_VEC_QSPI_ERROR   -1]          = qspi_error_intr;
    intr[`SWERV_INTR_VEC_QSPI_NOTIF   -1]          = qspi_notif_intr;
    intr[`SWERV_INTR_VEC_UART_ERROR   -1]          = uart_error_intr;
    intr[`SWERV_INTR_VEC_UART_NOTIF   -1]          = uart_notif_intr;
    intr[`SWERV_INTR_VEC_I3C_ERROR    -1]          = i3c_error_intr;
    intr[`SWERV_INTR_VEC_I3C_NOTIF    -1]          = i3c_notif_intr;
    intr[`SWERV_INTR_VEC_SOC_IFC_ERROR-1]          = soc_ifc_error_intr;
    intr[`SWERV_INTR_VEC_SOC_IFC_NOTIF-1]          = soc_ifc_notif_intr;
    intr[`SWERV_INTR_VEC_SHA_ERROR    -1]          = sha_error_intr;
    intr[`SWERV_INTR_VEC_SHA_NOTIF    -1]          = sha_notif_intr;
    intr[NUM_INTR-1:`SWERV_INTR_VEC_MAX_ASSIGNED]  = '0;
end

el2_swerv_wrapper rvtop (
    .rst_l                  ( cptra_uc_fw_rst_b),
    .dbg_rst_l              ( cptra_pwrgood), 
    .clk                    ( clk      ),
    .rst_vec                ( reset_vector[31:1]),
    .nmi_int                ( nmi_int       ),
    .nmi_vec                ( nmi_vector[31:1]),
    .jtag_id                ( jtag_id[31:1]),

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
    .lsu_haddr              ( initiator_inst.haddr       ),
    .lsu_hburst             (                       ),
    .lsu_hmastlock          (                       ),
    .lsu_hprot              (                       ),
    .lsu_hsize              ( initiator_inst.hsize       ),
    .lsu_htrans             ( initiator_inst.htrans      ),
    .lsu_hwrite             ( initiator_inst.hwrite      ),
    .lsu_hwdata             ( initiator_inst.hwdata      ),

    .lsu_hrdata             ( initiator_inst.hrdata[63:0]),
    .lsu_hready             ( initiator_inst.hready      ),
    .lsu_hresp              ( initiator_inst.hresp       ),

    //---------------------------------------------------------------
    // DMA Slave
    //---------------------------------------------------------------
    .dma_haddr              ( responder_inst[`SLAVE_SEL_IDMA].hsel ? responder_inst[`SLAVE_SEL_IDMA].haddr  : responder_inst[`SLAVE_SEL_DDMA].haddr ),
    .dma_hburst             ( '0                             ),
    .dma_hmastlock          ( '0                             ),
    .dma_hprot              ( 4'd3                           ),
    .dma_hsize              ( responder_inst[`SLAVE_SEL_IDMA].hsel ? responder_inst[`SLAVE_SEL_IDMA].hsize  : responder_inst[`SLAVE_SEL_DDMA].hsize ),
    .dma_htrans             ( responder_inst[`SLAVE_SEL_IDMA].hsel ? responder_inst[`SLAVE_SEL_IDMA].htrans : responder_inst[`SLAVE_SEL_DDMA].htrans ),
    .dma_hwrite             ( responder_inst[`SLAVE_SEL_IDMA].hsel ? responder_inst[`SLAVE_SEL_IDMA].hwrite : responder_inst[`SLAVE_SEL_DDMA].hwrite ),
    .dma_hwdata             ( responder_inst[`SLAVE_SEL_IDMA].hsel ? responder_inst[`SLAVE_SEL_IDMA].hwdata : responder_inst[`SLAVE_SEL_DDMA].hwdata ),

    .dma_hrdata             ( responder_inst[`SLAVE_SEL_DDMA].hrdata    ),
    .dma_hresp              ( responder_inst[`SLAVE_SEL_DDMA].hresp     ),
    .dma_hsel               ( responder_inst[`SLAVE_SEL_IDMA].hsel | responder_inst[`SLAVE_SEL_DDMA].hsel),
    .dma_hreadyin           ( responder_inst[`SLAVE_SEL_IDMA].hsel ? responder_inst[`SLAVE_SEL_IDMA].hready : responder_inst[`SLAVE_SEL_DDMA].hready     ),
    .dma_hreadyout          ( responder_inst[`SLAVE_SEL_DDMA].hreadyout  ),

    .timer_int              ( 1'b0     ),
    .extintsrc_req          ( intr     ),

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
    .debug_brkpt_status     (debug_brkpt_status),

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

    // Caliptra Memory Export Interface
    .el2_mem_export         (el2_mem_export),

    .soft_int               ('0),
    .core_id                ('0),
    .scan_mode              ( 1'b0 ),         // To enable scan mode
    .mbist_mode             ( 1'b0 )        // to enable mbist

);
    // Duplicate ICCM/DCCM accesses, using only hsel to differentiate
    always_comb responder_inst[`SLAVE_SEL_IDMA].hrdata    = responder_inst[`SLAVE_SEL_DDMA].hrdata;
    always_comb responder_inst[`SLAVE_SEL_IDMA].hresp     = responder_inst[`SLAVE_SEL_DDMA].hresp;
    always_comb responder_inst[`SLAVE_SEL_IDMA].hreadyout = responder_inst[`SLAVE_SEL_DDMA].hreadyout;


//=========================================================================-
// AHB I$ instance
//=========================================================================-

caliptra_ahb_srom #(
    .AHB_DATA_WIDTH(`IMEM_DATA_WIDTH),
    .AHB_ADDR_WIDTH(`IMEM_BYTE_ADDR_W),
    .CLIENT_ADDR_WIDTH(`IMEM_ADDR_WIDTH)

) imem (

    //AMBA AHB Lite INF
    .hclk       (clk                            ),
    .hreset_n   (cptra_uc_rst_b                 ),
    .haddr_i    (ic_haddr[`IMEM_BYTE_ADDR_W-1:0]),
    .hwdata_i   (`IMEM_DATA_WIDTH'(0)           ),
    .hsel_i     (1'b1                           ),
    .hwrite_i   (ic_hwrite                      ),

    .hready_i   (ic_hready                      ),
    .htrans_i   (ic_htrans                      ),
    .hsize_i    (ic_hsize                       ),


    .hresp_o    (ic_hresp                       ),
    .hreadyout_o(ic_hready                      ),
    .hrdata_o   (ic_hrdata[63:0]                ),

    .cs         (imem_cs                        ),
    .addr       (imem_addr                      ),
    .rdata      (imem_rdata                     )

);

sha512_ctrl #(
    .AHB_DATA_WIDTH (64),
    .AHB_ADDR_WIDTH (`SLAVE_ADDR_WIDTH(`SLAVE_SEL_SHA512))
) sha512 (
    .clk            (clk),
    .reset_n        (cptra_uc_rst_b),
    .cptra_pwrgood  (cptra_pwrgood),
    .haddr_i        (responder_inst[`SLAVE_SEL_SHA512].haddr[`SLAVE_ADDR_WIDTH(`SLAVE_SEL_SHA512)-1:0]),
    .hwdata_i       (responder_inst[`SLAVE_SEL_SHA512].hwdata),
    .hsel_i         (responder_inst[`SLAVE_SEL_SHA512].hsel),
    .hwrite_i       (responder_inst[`SLAVE_SEL_SHA512].hwrite),
    .hready_i       (responder_inst[`SLAVE_SEL_SHA512].hready),
    .htrans_i       (responder_inst[`SLAVE_SEL_SHA512].htrans),
    .hsize_i        (responder_inst[`SLAVE_SEL_SHA512].hsize),
    .hresp_o        (responder_inst[`SLAVE_SEL_SHA512].hresp),
    .hreadyout_o    (responder_inst[`SLAVE_SEL_SHA512].hreadyout),
    .hrdata_o       (responder_inst[`SLAVE_SEL_SHA512].hrdata),
    .kv_read        (kv_read[2]),
    .kv_write       (kv_write[1]),
    .kv_resp        (kv_resp[2]),

    .error_intr(sha512_error_intr),
    .notif_intr(sha512_notif_intr)
);

sha256_ctrl #(
    .AHB_DATA_WIDTH (64),
    .AHB_ADDR_WIDTH (`SLAVE_ADDR_WIDTH(`SLAVE_SEL_SHA256))
) sha256 (
    .clk            (clk),
    .reset_n        (cptra_uc_rst_b),
    .cptra_pwrgood  (cptra_pwrgood),
    .haddr_i        (responder_inst[`SLAVE_SEL_SHA256].haddr[`SLAVE_ADDR_WIDTH(`SLAVE_SEL_SHA256)-1:0]),
    .hwdata_i       (responder_inst[`SLAVE_SEL_SHA256].hwdata),
    .hsel_i         (responder_inst[`SLAVE_SEL_SHA256].hsel),
    .hwrite_i       (responder_inst[`SLAVE_SEL_SHA256].hwrite),
    .hready_i       (responder_inst[`SLAVE_SEL_SHA256].hready),
    .htrans_i       (responder_inst[`SLAVE_SEL_SHA256].htrans),
    .hsize_i        (responder_inst[`SLAVE_SEL_SHA256].hsize),
    .hresp_o        (responder_inst[`SLAVE_SEL_SHA256].hresp),
    .hreadyout_o    (responder_inst[`SLAVE_SEL_SHA256].hreadyout),
    .hrdata_o       (responder_inst[`SLAVE_SEL_SHA256].hrdata),

    .error_intr(sha256_error_intr),
    .notif_intr(sha256_notif_intr)
);


doe_ctrl #(
    .AHB_DATA_WIDTH (64),
    .AHB_ADDR_WIDTH (`SLAVE_ADDR_WIDTH(`SLAVE_SEL_DOE))
) doe (
    .clk            (clk),
    .reset_n        (cptra_uc_rst_b),
    .cptra_pwrgood  (cptra_pwrgood),
    .cptra_obf_key  (cptra_obf_key_reg),
    .obf_uds_seed   (obf_uds_seed),
    .obf_field_entropy(obf_field_entropy),
    .haddr_i        (responder_inst[`SLAVE_SEL_DOE].haddr[`SLAVE_ADDR_WIDTH(`SLAVE_SEL_DOE)-1:0]),
    .hwdata_i       (responder_inst[`SLAVE_SEL_DOE].hwdata),
    .hsel_i         (responder_inst[`SLAVE_SEL_DOE].hsel),
    .hwrite_i       (responder_inst[`SLAVE_SEL_DOE].hwrite),
    .hready_i       (responder_inst[`SLAVE_SEL_DOE].hready),
    .htrans_i       (responder_inst[`SLAVE_SEL_DOE].htrans),
    .hsize_i        (responder_inst[`SLAVE_SEL_DOE].hsize),
    .hresp_o        (responder_inst[`SLAVE_SEL_DOE].hresp),
    .hreadyout_o    (responder_inst[`SLAVE_SEL_DOE].hreadyout),
    .hrdata_o       (responder_inst[`SLAVE_SEL_DOE].hrdata),

    .error_intr(doe_error_intr),
    .notif_intr(doe_notif_intr),
    .clear_secrets(clear_secrets),
    .kv_write (kv_write[`KV_NUM_WRITE-1])

    
);

ecc_top #(
    .AHB_ADDR_WIDTH(`SLAVE_ADDR_WIDTH(`SLAVE_SEL_ECC)),
    .AHB_DATA_WIDTH(`AHB_HDATA_SIZE)
)
ecc_top1
(
    .clk           (clk),
    .reset_n       (cptra_uc_rst_b),
    .cptra_pwrgood (cptra_pwrgood),
    .haddr_i       (responder_inst[`SLAVE_SEL_ECC].haddr[`SLAVE_ADDR_WIDTH(`SLAVE_SEL_ECC)-1:0]),
    .hwdata_i      (responder_inst[`SLAVE_SEL_ECC].hwdata),
    .hsel_i        (responder_inst[`SLAVE_SEL_ECC].hsel),
    .hwrite_i      (responder_inst[`SLAVE_SEL_ECC].hwrite),
    .hready_i      (responder_inst[`SLAVE_SEL_ECC].hready),
    .htrans_i      (responder_inst[`SLAVE_SEL_ECC].htrans),
    .hsize_i       (responder_inst[`SLAVE_SEL_ECC].hsize),
    .hresp_o       (responder_inst[`SLAVE_SEL_ECC].hresp),
    .hreadyout_o   (responder_inst[`SLAVE_SEL_ECC].hreadyout),
    .hrdata_o      (responder_inst[`SLAVE_SEL_ECC].hrdata),

    .kv_read        (kv_read[5:3]),
    .kv_resp        (kv_resp[5:3]),
    .kv_write       (kv_write[2]),

    .error_intr    (ecc_error_intr),
    .notif_intr    (ecc_notif_intr)
);

hmac_ctrl #(
     .AHB_DATA_WIDTH(`AHB_HDATA_SIZE),
     .AHB_ADDR_WIDTH(`SLAVE_ADDR_WIDTH(`SLAVE_SEL_HMAC))
)hmac (
     .clk(clk),
     .reset_n       (cptra_uc_rst_b),
     .cptra_pwrgood (cptra_pwrgood),
     .hadrr_i       (responder_inst[`SLAVE_SEL_HMAC].haddr[`SLAVE_ADDR_WIDTH(`SLAVE_SEL_HMAC)-1:0]),
     .hwdata_i      (responder_inst[`SLAVE_SEL_HMAC].hwdata),
     .hsel_i        (responder_inst[`SLAVE_SEL_HMAC].hsel),
     .hwrite_i      (responder_inst[`SLAVE_SEL_HMAC].hwrite),
     .hready_i      (responder_inst[`SLAVE_SEL_HMAC].hready),
     .htrans_i      (responder_inst[`SLAVE_SEL_HMAC].htrans),
     .hsize_i       (responder_inst[`SLAVE_SEL_HMAC].hsize),
     .hresp_o       (responder_inst[`SLAVE_SEL_HMAC].hresp),
     .hreadyout_o   (responder_inst[`SLAVE_SEL_HMAC].hreadyout),
     .hrdata_o      (responder_inst[`SLAVE_SEL_HMAC].hrdata),
     .kv_read       (kv_read[1:0]),
     .kv_write      (kv_write[0]),
     .kv_resp       (kv_resp[1:0]),

     .error_intr(hmac_error_intr),
     .notif_intr(hmac_notif_intr)

);

kv #(
    .AHB_ADDR_WIDTH(`SLAVE_ADDR_WIDTH(`SLAVE_SEL_KV)),
    .AHB_DATA_WIDTH(`AHB_HDATA_SIZE),
    .KV_NUM_READ(`KV_NUM_READ),
    .KV_NUM_WRITE(`KV_NUM_WRITE)
)
key_vault1
(
    .clk           (clk),
    .rst_b         (cptra_uc_rst_b),
    .cptra_pwrgood (cptra_pwrgood),
    .haddr_i       (responder_inst[`SLAVE_SEL_KV].haddr[`SLAVE_ADDR_WIDTH(`SLAVE_SEL_KV)-1:0]),
    .hwdata_i      (responder_inst[`SLAVE_SEL_KV].hwdata),
    .hsel_i        (responder_inst[`SLAVE_SEL_KV].hsel),
    .hwrite_i      (responder_inst[`SLAVE_SEL_KV].hwrite),
    .hready_i      (responder_inst[`SLAVE_SEL_KV].hready),
    .htrans_i      (responder_inst[`SLAVE_SEL_KV].htrans),
    .hsize_i       (responder_inst[`SLAVE_SEL_KV].hsize),
    .hresp_o       (responder_inst[`SLAVE_SEL_KV].hresp),
    .hreadyout_o   (responder_inst[`SLAVE_SEL_KV].hreadyout),
    .hrdata_o      (responder_inst[`SLAVE_SEL_KV].hrdata),

    .kv_read       (kv_read),
    .kv_write      (kv_write),
    .kv_resp       (kv_resp)
);

soc_ifc_top #(
    .AHB_ADDR_WIDTH(`SLAVE_ADDR_WIDTH(`SLAVE_SEL_SOC_IFC)),
    .AHB_DATA_WIDTH(`AHB_HDATA_SIZE),
    .APB_ADDR_WIDTH(`SLAVE_ADDR_WIDTH(`SLAVE_SEL_SOC_IFC)),
    .APB_DATA_WIDTH(`APB_DATA_WIDTH),
    .APB_USER_WIDTH(`APB_USER_WIDTH)
    )
soc_ifc_top1 
    (
    .clk(clk),
    .cptra_pwrgood(cptra_pwrgood), 
    .cptra_rst_b(cptra_rst_b),
    .ready_for_fuses(ready_for_fuses),
    .ready_for_fw_push(ready_for_fw_push),
    .ready_for_runtime(ready_for_runtime),
    .mailbox_data_avail(mailbox_data_avail),
    .mailbox_flow_done(mailbox_flow_done),
    
    .generic_input_wires(generic_input_wires),
    .generic_output_wires(generic_output_wires),

    //SRAM interface
    .mbox_sram_req(mbox_sram_req),
    .mbox_sram_resp(mbox_sram_resp),

    //APB Interface with SoC
    .paddr_i(PADDR[`SLAVE_ADDR_WIDTH(`SLAVE_SEL_SOC_IFC)-1:0]),
    .psel_i(PSEL),
    .penable_i(PENABLE),
    .pwrite_i(PWRITE),
    .pwdata_i(PWDATA),
    .pauser_i(PAUSER),
    .pready_o(PREADY),
    .prdata_o(PRDATA),
    .pslverr_o(PSLVERR),
    //AHB Interface with uC
    .haddr_i    (responder_inst[`SLAVE_SEL_SOC_IFC].haddr[`SLAVE_ADDR_WIDTH(`SLAVE_SEL_SOC_IFC)-1:0]), 
    .hwdata_i   (responder_inst[`SLAVE_SEL_SOC_IFC].hwdata), 
    .hsel_i     (responder_inst[`SLAVE_SEL_SOC_IFC].hsel), 
    .hwrite_i   (responder_inst[`SLAVE_SEL_SOC_IFC].hwrite),
    .hready_i   (responder_inst[`SLAVE_SEL_SOC_IFC].hready),
    .htrans_i   (responder_inst[`SLAVE_SEL_SOC_IFC].htrans),
    .hsize_i    (responder_inst[`SLAVE_SEL_SOC_IFC].hsize),
    .hresp_o    (responder_inst[`SLAVE_SEL_SOC_IFC].hresp),
    .hreadyout_o(responder_inst[`SLAVE_SEL_SOC_IFC].hreadyout),
    .hrdata_o   (responder_inst[`SLAVE_SEL_SOC_IFC].hrdata),
    // uC Interrupts
    .soc_ifc_error_intr(soc_ifc_error_intr),
    .soc_ifc_notif_intr(soc_ifc_notif_intr),
    .sha_error_intr(sha_error_intr),
    .sha_notif_intr(sha_notif_intr),
    //Obfuscated UDS and FE
    .clear_secrets(clear_secrets),
    .cptra_obf_key(cptra_obf_key),
    .cptra_obf_key_reg(cptra_obf_key_reg),
    .obf_field_entropy(obf_field_entropy),
    .obf_uds_seed(obf_uds_seed),
    // ICCM Lock
    .iccm_lock       (iccm_lock                                    ),
    .iccm_axs_blocked(ahb_lite_resp_access_blocked[`SLAVE_SEL_IDMA]),
    //uC reset
    .cptra_uc_rst_b (cptra_uc_rst_b),
    .cptra_uc_fw_rst_b (cptra_uc_fw_rst_b)
);

//TIE OFF slaves
always_comb begin: tie_off_slaves
    responder_inst[`SLAVE_SEL_QSPI].hresp = '0;
    responder_inst[`SLAVE_SEL_QSPI].hreadyout = '0;
    responder_inst[`SLAVE_SEL_QSPI].hrdata = '0;
    responder_inst[`SLAVE_SEL_UART].hresp = '0;
    responder_inst[`SLAVE_SEL_UART].hreadyout = '0;
    responder_inst[`SLAVE_SEL_UART].hrdata = '0;
    responder_inst[`SLAVE_SEL_I3C].hresp = '0;
    responder_inst[`SLAVE_SEL_I3C].hreadyout = '0;
    responder_inst[`SLAVE_SEL_I3C].hrdata = '0;
end 

genvar sva_i;
generate
  for(sva_i= 0; sva_i<`AHB_SLAVES_NUM; sva_i=sva_i+1)
  begin: gen_caliptra_asserts
    `ASSERT_KNOWN(AHB_SLAVE_HADDR_X,        responder_inst[sva_i].haddr,       clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HWDATA_X,       responder_inst[sva_i].hwdata,      clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HSEL_X,         responder_inst[sva_i].hsel,        clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HWRITE_X,       responder_inst[sva_i].hwrite,      clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HREADY_X,       responder_inst[sva_i].hready,      clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HTRANS_X,       responder_inst[sva_i].htrans,      clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HSIZE_X,        responder_inst[sva_i].hsize,       clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HRESP_X,        responder_inst[sva_i].hresp,       clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HREADYOUT_X,    responder_inst[sva_i].hreadyout,   clk, cptra_uc_rst_b)
    `ASSERT_KNOWN(AHB_SLAVE_HRDATA_X,       responder_inst[sva_i].hreadyout ? responder_inst[sva_i].hrdata : '0,      clk, cptra_uc_rst_b)
  end
endgenerate

`ASSERT_KNOWN(AHB_MASTER_HADDR_X,        initiator_inst.haddr,       clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HWDATA_X,       initiator_inst.hwdata,      clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HWRITE_X,       initiator_inst.hwrite,      clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HREADY_X,       initiator_inst.hready,      clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HTRANS_X,       initiator_inst.htrans,      clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HSIZE_X,        initiator_inst.hsize,       clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HRESP_X,        initiator_inst.hresp,       clk, cptra_uc_rst_b)
`ASSERT_KNOWN(AHB_MASTER_HRDATA_X,       initiator_inst.hready ? initiator_inst.hrdata : '0,      clk, cptra_uc_rst_b)

endmodule
