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

`include "config_defines.svh"
`include "caliptra_macros.svh"
`include "caliptra_sva.svh"

module caliptra_top
    import kv_defines_pkg::*;
    import pv_defines_pkg::*;
    import soc_ifc_pkg::*;
    import lc_ctrl_state_pkg::*;
    import lc_ctrl_reg_pkg::*;
    import lc_ctrl_pkg::*;
`ifdef CALIPTRA_INTERNAL_TRNG
    import entropy_src_pkg::*;
    import csrng_pkg::*;
`endif
    (
    input logic                        clk,

    input logic                        cptra_pwrgood,
    input logic                        cptra_rst_b,

    input logic [255:0]                cptra_obf_key,

    //JTAG Interface
    input logic                        jtag_tck,    // JTAG clk
    input logic                        jtag_tms,    // JTAG TMS
    input logic                        jtag_tdi,    // JTAG tdi
    input logic                        jtag_trst_n, // JTAG Reset
    output logic                       jtag_tdo,    // JTAG TDO

    //APB Interface
    input  logic [`CALIPTRA_APB_ADDR_WIDTH-1:0] PADDR,
    input  logic [2:0]                          PPROT,
    input  logic                                PSEL,
    input  logic                                PENABLE,
    input  logic                                PWRITE,
    input  logic [`CALIPTRA_APB_DATA_WIDTH-1:0] PWDATA,
    input  logic [`CALIPTRA_APB_USER_WIDTH-1:0] PAUSER,

    output logic                                PREADY,
    output logic                                PSLVERR,
    output logic [`CALIPTRA_APB_DATA_WIDTH-1:0] PRDATA,

    //QSPI Interface
    output logic                                qspi_clk_o,
    output logic [`CALIPTRA_QSPI_CS_WIDTH-1:0]  qspi_cs_no,
    input  wire  [`CALIPTRA_QSPI_IO_WIDTH-1:0]  qspi_d_i,
    output logic [`CALIPTRA_QSPI_IO_WIDTH-1:0]  qspi_d_o,
    output logic [`CALIPTRA_QSPI_IO_WIDTH-1:0]  qspi_d_en_o,

    //UART Interface
`ifdef CALIPTRA_INTERNAL_UART
    output logic                                uart_tx,
    input  logic                                uart_rx,
`endif

    // Caliptra Memory Export Interface
    el2_mem_if.veer_sram_src           el2_mem_export,

    //SRAM interface for mbox
    output logic mbox_sram_cs,
    output logic mbox_sram_we,
    output logic [MBOX_ADDR_W-1:0] mbox_sram_addr,
    output logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_wdata,
    input  logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_rdata,

    //SRAM interface for imem
    output logic imem_cs,
    output logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] imem_addr,
    input  logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] imem_rdata,

    output logic                       ready_for_fuses,
    output logic                       ready_for_fw_push,
    output logic                       ready_for_runtime,

    output logic                       mailbox_data_avail,
    output logic                       mailbox_flow_done,

    input logic                        BootFSM_BrkPoint,

    //SoC Interrupts
    output logic             cptra_error_fatal,
    output logic             cptra_error_non_fatal,

    // TRNG Interface
    // External Request
    output logic             etrng_req,
    // Physical Source for Internal TRNG
    input  logic [3:0]       itrng_data,
    input  logic             itrng_valid,

    input logic  [63:0]                generic_input_wires,
    output logic [63:0]                generic_output_wires,

    input security_state_t             security_state,
    input logic                        scan_mode
);

    `include "common_defines.sv"

    localparam NUM_INTR = `RV_PIC_TOTAL_INT; // 31
    localparam TOTAL_OBF_KEY_BITS = `CLP_OBF_KEY_DWORDS * 32;

    //caliptra reset driven by boot fsm in mailbox
    logic                       cptra_noncore_rst_b;
    logic                       cptra_uc_rst_b;

    //clock gating signals
    logic                       clk_gating_en   ;
    logic                       rdc_clk_dis     ;
    logic                       clk_cg          ;
    logic                       soc_ifc_clk_cg  ;
    logic                       rdc_clk_cg      ;
    logic                       uc_clk_cg       ;

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

    integer                     cycleCnt;
    logic                       mailbox_data_val;

    wire                        dma_hready_out;
    integer                     commit_count;

    logic                       wb_valid;
    logic [4:0]                 wb_dest;
    logic [31:0]                wb_data;

    logic [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key_reg;
    logic [`CLP_OBF_FE_DWORDS-1 :0][31:0] obf_field_entropy;
    logic [`CLP_OBF_UDS_DWORDS-1:0][31:0] obf_uds_seed;

    //caliptra uncore jtag ports & pertinent logic
    logic                       cptra_uncore_dmi_reg_en;
    logic                       cptra_uncore_dmi_reg_wr_en;
    logic [31:0]                cptra_uncore_dmi_reg_rdata;
    logic [6:0]                 cptra_uncore_dmi_reg_addr;
    logic [31:0]                cptra_uncore_dmi_reg_wdata;
    security_state_t            cptra_security_state_Latched;
    security_state_t            cptra_security_state_Latched_d;
    security_state_t            cptra_security_state_Latched_f;
    logic                       cptra_dmi_reg_en_preQ;
    
    logic                       fw_update_rst_window;

    // Caliptra ECC status signals
    rv_ecc_sts_t rv_ecc_sts;


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

    kv_read_t [KV_NUM_READ-1:0]  kv_read;
    kv_write_t [KV_NUM_WRITE-1:0]  kv_write;
    kv_rd_resp_t [KV_NUM_READ-1:0] kv_rd_resp;
    kv_wr_resp_t [KV_NUM_WRITE-1:0] kv_wr_resp;

    pv_read_t [PV_NUM_READ-1:0]  pv_read;
    pv_write_t [PV_NUM_WRITE-1:0]  pv_write;
    pv_rd_resp_t [PV_NUM_READ-1:0] pv_rd_resp;
    pv_wr_resp_t [PV_NUM_WRITE-1:0] pv_wr_resp;

    pcr_signing_t pcr_signing_data;

    //mailbox sram gasket
    mbox_sram_req_t mbox_sram_req;
    mbox_sram_resp_t mbox_sram_resp;

    logic clear_obf_secrets;
    logic clear_secrets;
    
    logic cptra_security_state_captured;
    logic scan_mode_switch;
    logic debug_lock_or_scan_mode_switch, clear_obf_secrets_debugScanQ, debug_lock_switch;
    logic cptra_scan_mode_Latched, cptra_scan_mode_Latched_d, cptra_scan_mode_Latched_f;

    logic [TOTAL_OBF_KEY_BITS-1:0]        cptra_obf_key_dbg;
    logic [`CLP_OBF_FE_DWORDS-1 :0][31:0] obf_field_entropy_dbg;
    logic [`CLP_OBF_UDS_DWORDS-1:0][31:0] obf_uds_seed_dbg;
    logic                                 cptra_in_debug_scan_mode;

    logic [31:0] imem_haddr;
    logic imem_hsel;
    logic imem_hwrite;
    logic imem_hready;
    logic imem_hreadyout;
    logic [1:0] imem_htrans;
    logic [2:0] imem_hsize;
    logic [63:0] imem_hrdata;
    logic imem_hresp;
    
    logic lsu_addr_ph, lsu_data_ph, lsu_sel;
    logic ic_addr_ph, ic_data_ph, ic_sel;

always_comb begin
    mbox_sram_cs = mbox_sram_req.cs;
    mbox_sram_we = mbox_sram_req.we;
    mbox_sram_addr = mbox_sram_req.addr;
    mbox_sram_wdata = mbox_sram_req.wdata; // Contains data + ecc fields
    mbox_sram_resp.rdata = mbox_sram_rdata; // Contains data + ecc fields
end
    //========================================================================
    // AHB Slave ports. 
    // Slave 0: LMEM
    // Slave 1: DMA Slave port
    //========================================================================
    CALIPTRA_AHB_LITE_BUS_INF #(
        .AHB_LITE_ADDR_WIDTH(`CALIPTRA_AHB_HADDR_SIZE),
        .AHB_LITE_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE)
    )
    responder_inst[0:`CALIPTRA_AHB_SLAVES_NUM-1]();

    //========================================================================
    // AHB Master ports
    //========================================================================
    CALIPTRA_AHB_LITE_BUS_INF #(
        .AHB_LITE_ADDR_WIDTH(`CALIPTRA_AHB_HADDR_SIZE),
        .AHB_LITE_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE)
    )
    sb_ahb();
    CALIPTRA_AHB_LITE_BUS_INF #(
        .AHB_LITE_ADDR_WIDTH(`CALIPTRA_AHB_HADDR_SIZE),
        .AHB_LITE_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE)
    )
    lsu_ahb();

    CALIPTRA_AHB_LITE_BUS_INF #(
        .AHB_LITE_ADDR_WIDTH(`CALIPTRA_AHB_HADDR_SIZE),
        .AHB_LITE_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE)
    )
    initiator_inst();

    //========================================================================
    // AHB Responder Disable
    //========================================================================
    logic [`CALIPTRA_AHB_SLAVES_NUM-1:0] ahb_lite_resp_disable;
    logic [`CALIPTRA_AHB_SLAVES_NUM-1:0] ahb_lite_resp_access_blocked;

    //========================================================================
    // AHB Lite Interface and decoder logic instance
    //========================================================================
    ahb_lite_bus #(
        .NUM_RESPONDERS        (`CALIPTRA_AHB_SLAVES_NUM),
        .AHB_LITE_ADDR_WIDTH   (`CALIPTRA_AHB_HADDR_SIZE),
        .AHB_LITE_DATA_WIDTH   (`CALIPTRA_AHB_HDATA_SIZE)
    )
    ahb_lite_bus_i (
        .hclk                          ( clk_cg                      ),
        .hreset_n                      ( cptra_noncore_rst_b         ),
        .force_bus_idle                ( fw_update_rst_window        ),
        .ahb_lite_responders           ( responder_inst              ),
        .ahb_lite_initiator            ( initiator_inst              ),
        .ahb_lite_resp_disable_i       ( ahb_lite_resp_disable       ),
        .ahb_lite_resp_access_blocked_o( ahb_lite_resp_access_blocked),
        .ahb_lite_start_addr_i         ( `CALIPTRA_SLAVE_BASE_ADDR   ),
        .ahb_lite_end_addr_i           ( `CALIPTRA_SLAVE_MASK_ADDR   )
    );
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_DOE]     = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_ECC]     = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_HMAC]    = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_KV]      = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_PV]      = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_DV]      = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_SHA512]  = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_QSPI]    = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_UART]    = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_I3C]     = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_SOC_IFC] = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_DDMA]    = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_IDMA]    = iccm_lock & responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hwrite;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_SHA256]  = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_IMEM]    = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_CSRNG]       = 1'b0;
    always_comb ahb_lite_resp_disable[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC] = 1'b0;

   //=========================================================================-
   // RTL instance
   //=========================================================================-
//FIXME TIE OFFS
logic [31:0] reset_vector;
logic [31:0] nmi_vector;
logic nmi_int;
logic soft_int;
logic timer_int;

assign reset_vector = `RV_RESET_VEC;
assign soft_int     = 1'b0;

assign kv_error_intr = 1'b0; // TODO
assign kv_notif_intr = 1'b0; // TODO
assign qspi_error_intr = 1'b0; // TODO
assign qspi_notif_intr = 1'b0; // TODO
assign uart_error_intr = 1'b0; // TODO
assign uart_notif_intr = 1'b0; // TODO
assign i3c_error_intr = 1'b0; // TODO
assign i3c_notif_intr = 1'b0; // TODO

// Vector 0 usage is reserved by VeeR, so bit 0 of the intr wire
// drive Vector 1
always_comb begin
    intr[`VEER_INTR_VEC_DOE_ERROR    -1]          = doe_error_intr;
    intr[`VEER_INTR_VEC_DOE_NOTIF    -1]          = doe_notif_intr;
    intr[`VEER_INTR_VEC_ECC_ERROR    -1]          = ecc_error_intr;
    intr[`VEER_INTR_VEC_ECC_NOTIF    -1]          = ecc_notif_intr;
    intr[`VEER_INTR_VEC_HMAC_ERROR   -1]          = hmac_error_intr;
    intr[`VEER_INTR_VEC_HMAC_NOTIF   -1]          = hmac_notif_intr;
    intr[`VEER_INTR_VEC_KV_ERROR     -1]          = kv_error_intr;
    intr[`VEER_INTR_VEC_KV_NOTIF     -1]          = kv_notif_intr;
    intr[`VEER_INTR_VEC_SHA512_ERROR -1]          = sha512_error_intr;
    intr[`VEER_INTR_VEC_SHA512_NOTIF -1]          = sha512_notif_intr;
    intr[`VEER_INTR_VEC_SHA256_ERROR- 1]          = sha256_error_intr;
    intr[`VEER_INTR_VEC_SHA256_NOTIF -1]          = sha256_notif_intr;
    intr[`VEER_INTR_VEC_QSPI_ERROR   -1]          = qspi_error_intr;
    intr[`VEER_INTR_VEC_QSPI_NOTIF   -1]          = qspi_notif_intr;
    intr[`VEER_INTR_VEC_UART_ERROR   -1]          = uart_error_intr;
    intr[`VEER_INTR_VEC_UART_NOTIF   -1]          = uart_notif_intr;
    intr[`VEER_INTR_VEC_I3C_ERROR    -1]          = i3c_error_intr;
    intr[`VEER_INTR_VEC_I3C_NOTIF    -1]          = i3c_notif_intr;
    intr[`VEER_INTR_VEC_SOC_IFC_ERROR-1]          = soc_ifc_error_intr;
    intr[`VEER_INTR_VEC_SOC_IFC_NOTIF-1]          = soc_ifc_notif_intr;
    intr[`VEER_INTR_VEC_SHA_ERROR    -1]          = sha_error_intr;
    intr[`VEER_INTR_VEC_SHA_NOTIF    -1]          = sha_notif_intr;
    intr[NUM_INTR-1:`VEER_INTR_VEC_MAX_ASSIGNED]  = '0;
end

el2_veer_wrapper rvtop (
`ifdef CALIPTRA_FORCE_CPU_RESET
    .rst_l                  ( 1'b0 ),
`else
    .rst_l                  ( cptra_uc_rst_b),
`endif
    .dbg_rst_l              ( cptra_pwrgood), 
    .clk                    ( uc_clk_cg    ),
    .rst_vec                ( reset_vector[31:1]),
    .nmi_int                ( nmi_int       ),
    .nmi_vec                ( nmi_vector[31:1]),

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
    .sb_haddr               ( sb_ahb.haddr   ),
    .sb_hburst              (                ),
    .sb_hmastlock           (                ),
    .sb_hprot               (                ),
    .sb_hsize               ( sb_ahb.hsize   ),
    .sb_htrans              ( sb_ahb.htrans  ),
    .sb_hwrite              ( sb_ahb.hwrite  ),
    .sb_hwdata              ( sb_ahb.hwdata  ),

    .sb_hrdata              ( sb_ahb.hrdata  ),
    .sb_hready              ( sb_ahb.hready  ),
    .sb_hresp               ( sb_ahb.hresp   ),

    //---------------------------------------------------------------
    // LSU AHB Master
    //---------------------------------------------------------------
    .lsu_haddr              ( lsu_ahb.haddr  ),
    .lsu_hburst             (                ),
    .lsu_hmastlock          (                ),
    .lsu_hprot              (                ),
    .lsu_hsize              ( lsu_ahb.hsize  ),
    .lsu_htrans             ( lsu_ahb.htrans ),
    .lsu_hwrite             ( lsu_ahb.hwrite ),
    .lsu_hwdata             ( lsu_ahb.hwdata ),

    .lsu_hrdata             ( lsu_ahb.hrdata ),
    .lsu_hready             ( lsu_ahb.hready ),
    .lsu_hresp              ( lsu_ahb.hresp  ),

    //---------------------------------------------------------------
    // DMA Slave
    //---------------------------------------------------------------
    .dma_haddr              ( responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hsel ? responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].haddr  : responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].haddr ),
    .dma_hburst             ( '0                             ),
    .dma_hmastlock          ( '0                             ),
    .dma_hprot              ( 4'd3                           ),
    .dma_hsize              ( responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hsel ? responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hsize  : responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hsize ),
    .dma_htrans             ( responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hsel ? responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].htrans : responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].htrans ),
    .dma_hwrite             ( responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hsel ? responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hwrite : responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hwrite ),
    .dma_hwdata             ( responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hsel ? responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hwdata : responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hwdata ),

    .dma_hrdata             ( responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hrdata    ),
    .dma_hresp              ( responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hresp     ),
    .dma_hsel               ( responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hsel | responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hsel),
    .dma_hreadyin           ( responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hsel ? responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hready : responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hready     ),
    .dma_hreadyout          ( responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hreadyout  ),

    .timer_int              ( timer_int),
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

    //caliptra uncore jtag ports
   .cptra_uncore_dmi_reg_en      ( cptra_uncore_dmi_reg_en ),
   .cptra_uncore_dmi_reg_wr_en   ( cptra_uncore_dmi_reg_wr_en ),
   .cptra_uncore_dmi_reg_rdata   ( cptra_uncore_dmi_reg_rdata ),
   .cptra_uncore_dmi_reg_addr    ( cptra_uncore_dmi_reg_addr ),
   .cptra_uncore_dmi_reg_wdata   ( cptra_uncore_dmi_reg_wdata ),
   .cptra_security_state_Latched ( cptra_security_state_Latched),
   .cptra_dmi_reg_en_preQ        ( cptra_dmi_reg_en_preQ ),

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

    // Caliptra ECC status signals
    .cptra_iccm_ecc_single_error(rv_ecc_sts.cptra_iccm_ecc_single_error),
    .cptra_iccm_ecc_double_error(rv_ecc_sts.cptra_iccm_ecc_double_error),
    .cptra_dccm_ecc_single_error(rv_ecc_sts.cptra_dccm_ecc_single_error),
    .cptra_dccm_ecc_double_error(rv_ecc_sts.cptra_dccm_ecc_double_error),

    .soft_int               (soft_int),
    .core_id                ('0),
    .scan_mode              ( scan_mode ), // To enable scan mode
    .mbist_mode             ( 1'b0 )        // to enable mbist

);
    // Duplicate ICCM/DCCM accesses, using only hsel to differentiate
    always_comb responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hrdata    = responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hrdata;
    always_comb responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hresp     = responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hresp;
    always_comb responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hreadyout = responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hreadyout;

    // SB and LSU AHB master mux
    ahb_lite_2to1_mux #(
        .AHB_LITE_ADDR_WIDTH (`CALIPTRA_AHB_HADDR_SIZE),
        .AHB_LITE_DATA_WIDTH (`CALIPTRA_AHB_HDATA_SIZE),
        .AHB_NO_OPT(1) //Prevent address and data phase overlap between initiators
    ) u_sb_lsu_ahb_mux (
        .hclk                (clk_cg),
        .hreset_n            (cptra_noncore_rst_b),
        .force_bus_idle      (fw_update_rst_window),
        // Initiator 0
        .hsel_i_0            (1'b1          ),
        .haddr_i_0           (lsu_ahb.haddr ),
        .hwdata_i_0          (lsu_ahb.hwdata),
        .hwrite_i_0          (lsu_ahb.hwrite),
        .htrans_i_0          (lsu_ahb.htrans),
        .hsize_i_0           (lsu_ahb.hsize ),
        .hready_i_0          (1'b1          ),
        .hresp_o_0           (lsu_ahb.hresp ),
        .hready_o_0          (lsu_ahb.hready),
        .hrdata_o_0          (lsu_ahb.hrdata),

        // Initiator 1
        .hsel_i_1            (1'b1          ),
        .haddr_i_1           (sb_ahb.haddr  ),
        .hwdata_i_1          (sb_ahb.hwdata ),
        .hwrite_i_1          (sb_ahb.hwrite ),
        .htrans_i_1          (sb_ahb.htrans ),
        .hsize_i_1           (sb_ahb.hsize  ),
        .hready_i_1          (1'b1          ),
        .hresp_o_1           (sb_ahb.hresp  ),
        .hready_o_1          (sb_ahb.hready ),
        .hrdata_o_1          (sb_ahb.hrdata ),

        // Responder
        .hsel_o              (initiator_inst.hsel  ),
        .haddr_o             (initiator_inst.haddr ),
        .hwdata_o            (initiator_inst.hwdata),
        .hwrite_o            (initiator_inst.hwrite),
        .htrans_o            (initiator_inst.htrans),
        .hsize_o             (initiator_inst.hsize ),
        .hready_o            (initiator_inst.hready),
        .hresp_i             (initiator_inst.hresp ),
        .hreadyout_i         (initiator_inst.hreadyout),
        .hrdata_i            (initiator_inst.hrdata)
    );

    // Security State value captured on a Caliptra reset deassertion (0->1 signal transition)
    always_ff @(posedge clk or negedge cptra_noncore_rst_b) begin
        if (~cptra_noncore_rst_b) begin
            cptra_security_state_Latched_d <= '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1}; //Setting the default value to be debug locked and in production mode
            cptra_security_state_Latched_f <= '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1};

            cptra_security_state_captured <= 0;
        end
        else if(!cptra_security_state_captured) begin
            cptra_security_state_Latched_d <= security_state;
            cptra_security_state_captured <= 1;
        end
        else begin
            cptra_security_state_Latched_f <= cptra_security_state_Latched_d;
        end
    end

    always_ff @(posedge clk or negedge cptra_pwrgood) begin
        if (~cptra_pwrgood) begin
            cptra_scan_mode_Latched_d <= '0;
            cptra_scan_mode_Latched_f <= '0;
        end
        else begin
            cptra_scan_mode_Latched_d <= scan_mode;
            cptra_scan_mode_Latched_f <= cptra_scan_mode_Latched_d;
        end
    end

    //Lock debug unless both flops are unlocked
    assign cptra_security_state_Latched.debug_locked = cptra_security_state_Latched_d.debug_locked | cptra_security_state_Latched_f.debug_locked;
    //Pass on the latched value of device lifecycle
    assign cptra_security_state_Latched.device_lifecycle = cptra_security_state_Latched_d.device_lifecycle;
    //Only assert scan mode once both flops have set
    assign cptra_scan_mode_Latched = cptra_scan_mode_Latched_d & cptra_scan_mode_Latched_f;
    
    // When scan mode goes from 0->1, generate a pulse to clear the assets
    // Note that when scan goes to '1, Caliptra state as well as SOC state
    // gets messed up. So switch to scan is destructive (obvious! Duh!)
    assign scan_mode_switch = cptra_scan_mode_Latched_d & ~cptra_scan_mode_Latched_f;
    // Detect transition of debug mode
    assign debug_lock_switch = cptra_security_state_Latched_d.debug_locked ^ cptra_security_state_Latched_f.debug_locked;
    assign debug_lock_or_scan_mode_switch = debug_lock_switch | scan_mode_switch | cptra_error_fatal;

    assign clear_obf_secrets_debugScanQ = clear_obf_secrets | cptra_in_debug_scan_mode | cptra_error_fatal;

//=========================================================================-
// Clock gating instance
//=========================================================================-
clk_gate cg (
    .clk(clk),
    .cptra_rst_b(cptra_noncore_rst_b),
    .psel(PSEL),
    .clk_gate_en(clk_gating_en),
    .cpu_halt_status(o_cpu_halt_status),
    .rdc_clk_dis(rdc_clk_dis),
    .rdc_clk_dis_uc (fw_update_rst_window),
    .clk_cg (clk_cg),
    .soc_ifc_clk_cg (soc_ifc_clk_cg),
    .rdc_clk_cg (rdc_clk_cg),
    .uc_clk_cg (uc_clk_cg),
    .generic_input_wires(generic_input_wires),
    .cptra_error_fatal(cptra_error_fatal),
    .cptra_in_debug_scan_mode(cptra_in_debug_scan_mode),
    .cptra_dmi_reg_en_preQ(cptra_dmi_reg_en_preQ)
);
//=========================================================================-
// AHB I$ instance
//=========================================================================-

    // Instanitate AHB Lite Address Decoder
ahb_lite_2to1_mux #(
    .AHB_LITE_ADDR_WIDTH(`CALIPTRA_IMEM_BYTE_ADDR_W),
    .AHB_LITE_DATA_WIDTH(`CALIPTRA_IMEM_DATA_WIDTH)
) u_ahb_lite_2to1_mux (
    .hclk           (clk_cg),
    .hreset_n       (cptra_uc_rst_b),
    .force_bus_idle (fw_update_rst_window),
    // From Initiator 0
    // Inputs
    .hsel_i_0             (responder_inst[`CALIPTRA_SLAVE_SEL_IMEM].hsel),
    .haddr_i_0            (responder_inst[`CALIPTRA_SLAVE_SEL_IMEM].haddr[`CALIPTRA_IMEM_BYTE_ADDR_W-1:0]),
    .hwdata_i_0           ('0),
    .hwrite_i_0           (responder_inst[`CALIPTRA_SLAVE_SEL_IMEM].hwrite),
    .htrans_i_0           (responder_inst[`CALIPTRA_SLAVE_SEL_IMEM].htrans),
    .hsize_i_0            (responder_inst[`CALIPTRA_SLAVE_SEL_IMEM].hsize),
    .hready_i_0           (responder_inst[`CALIPTRA_SLAVE_SEL_IMEM].hready),
    // Outputs
    .hresp_o_0            (responder_inst[`CALIPTRA_SLAVE_SEL_IMEM].hresp),
    .hready_o_0           (responder_inst[`CALIPTRA_SLAVE_SEL_IMEM].hreadyout),
    .hrdata_o_0           (responder_inst[`CALIPTRA_SLAVE_SEL_IMEM].hrdata),
    // From Initiator 1
    // Inputs
    .hsel_i_1             (1'b1),
    .haddr_i_1            (ic_haddr[`CALIPTRA_IMEM_BYTE_ADDR_W-1:0]),
    .hwdata_i_1           ('0),
    .hwrite_i_1           (ic_hwrite),
    .htrans_i_1           (ic_htrans),
    .hsize_i_1            (ic_hsize),
    .hready_i_1           (1'b1),
    // Outputs
    .hresp_o_1            (ic_hresp),
    .hready_o_1           (ic_hready),
    .hrdata_o_1           (ic_hrdata),
    // To Responder
    // Inputs
    .hresp_i            (imem_hresp),
    .hrdata_i           (imem_hrdata),
    .hreadyout_i        (imem_hreadyout),
    // Outputs
    .haddr_o            (imem_haddr[`CALIPTRA_IMEM_BYTE_ADDR_W-1:0]),
    .hwdata_o           ( ),
    .hsel_o             (imem_hsel),
    .hwrite_o           (imem_hwrite),
    .hready_o           (imem_hready),
    .htrans_o           (imem_htrans),
    .hsize_o            (imem_hsize)
);

caliptra_ahb_srom #(
    .AHB_DATA_WIDTH(`CALIPTRA_IMEM_DATA_WIDTH),
    .AHB_ADDR_WIDTH(`CALIPTRA_IMEM_BYTE_ADDR_W),
    .CLIENT_ADDR_WIDTH(`CALIPTRA_IMEM_ADDR_WIDTH)
) imem (

    //AMBA AHB Lite INF
    .hclk       (clk_cg),
    .hreset_n   (cptra_uc_rst_b),
    .haddr_i    (imem_haddr[`CALIPTRA_IMEM_BYTE_ADDR_W-1:0]),
    .hwdata_i   (`CALIPTRA_IMEM_DATA_WIDTH'(0)             ),
    .hsel_i     (imem_hsel),
    .hwrite_i   (imem_hwrite),

    .hready_i   (imem_hready),
    .htrans_i   (imem_htrans),
    .hsize_i    (imem_hsize),


    .hresp_o    (imem_hresp),
    .hreadyout_o(imem_hreadyout),
    .hrdata_o   (imem_hrdata),

    .cs         (imem_cs),
    .addr       (imem_addr),
    .rdata      (imem_rdata)

);

sha512_ctrl #(
    .AHB_DATA_WIDTH (`CALIPTRA_AHB_HDATA_SIZE),
    .AHB_ADDR_WIDTH (`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SHA512))
) sha512 (
    .clk            (clk_cg),
    .reset_n        (cptra_noncore_rst_b),
    .cptra_pwrgood  (cptra_pwrgood),
    .haddr_i        (responder_inst[`CALIPTRA_SLAVE_SEL_SHA512].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SHA512)-1:0]),
    .hwdata_i       (responder_inst[`CALIPTRA_SLAVE_SEL_SHA512].hwdata),
    .hsel_i         (responder_inst[`CALIPTRA_SLAVE_SEL_SHA512].hsel),
    .hwrite_i       (responder_inst[`CALIPTRA_SLAVE_SEL_SHA512].hwrite),
    .hready_i       (responder_inst[`CALIPTRA_SLAVE_SEL_SHA512].hready),
    .htrans_i       (responder_inst[`CALIPTRA_SLAVE_SEL_SHA512].htrans),
    .hsize_i        (responder_inst[`CALIPTRA_SLAVE_SEL_SHA512].hsize),
    .hresp_o        (responder_inst[`CALIPTRA_SLAVE_SEL_SHA512].hresp),
    .hreadyout_o    (responder_inst[`CALIPTRA_SLAVE_SEL_SHA512].hreadyout),
    .hrdata_o       (responder_inst[`CALIPTRA_SLAVE_SEL_SHA512].hrdata),
    .kv_read        (kv_read[2]),
    .kv_write       (kv_write[1]),
    .kv_rd_resp     (kv_rd_resp[2]),
    .kv_wr_resp     (kv_wr_resp[1]),
    .pv_read        (pv_read),
    .pv_write       (pv_write),
    .pv_rd_resp     (pv_rd_resp),
    .pv_wr_resp     (pv_wr_resp),
    .pcr_signing_hash(pcr_signing_data.pcr_hash),

    .error_intr(sha512_error_intr),
    .notif_intr(sha512_notif_intr),
    .debugUnlock_or_scan_mode_switch(debug_lock_or_scan_mode_switch)
);

sha256_ctrl #(
    .AHB_DATA_WIDTH (`CALIPTRA_AHB_HDATA_SIZE),
    .AHB_ADDR_WIDTH (`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SHA256))
) sha256 (
    .clk            (clk_cg),
    .reset_n        (cptra_noncore_rst_b),
    .cptra_pwrgood  (cptra_pwrgood),
    .haddr_i        (responder_inst[`CALIPTRA_SLAVE_SEL_SHA256].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SHA256)-1:0]),
    .hwdata_i       (responder_inst[`CALIPTRA_SLAVE_SEL_SHA256].hwdata),
    .hsel_i         (responder_inst[`CALIPTRA_SLAVE_SEL_SHA256].hsel),
    .hwrite_i       (responder_inst[`CALIPTRA_SLAVE_SEL_SHA256].hwrite),
    .hready_i       (responder_inst[`CALIPTRA_SLAVE_SEL_SHA256].hready),
    .htrans_i       (responder_inst[`CALIPTRA_SLAVE_SEL_SHA256].htrans),
    .hsize_i        (responder_inst[`CALIPTRA_SLAVE_SEL_SHA256].hsize),
    .hresp_o        (responder_inst[`CALIPTRA_SLAVE_SEL_SHA256].hresp),
    .hreadyout_o    (responder_inst[`CALIPTRA_SLAVE_SEL_SHA256].hreadyout),
    .hrdata_o       (responder_inst[`CALIPTRA_SLAVE_SEL_SHA256].hrdata),

    .error_intr(sha256_error_intr),
    .notif_intr(sha256_notif_intr),
    .debugUnlock_or_scan_mode_switch(debug_lock_or_scan_mode_switch)
);

//override device secrets with debug values in Debug or Scan Mode
always_comb cptra_in_debug_scan_mode = ~cptra_security_state_Latched.debug_locked | cptra_scan_mode_Latched;
always_comb cptra_obf_key_dbg     = cptra_in_debug_scan_mode ? `CLP_DEBUG_MODE_OBF_KEY : cptra_obf_key_reg;
always_comb obf_uds_seed_dbg      = cptra_in_debug_scan_mode ? `CLP_DEBUG_MODE_UDS_SEED : obf_uds_seed;
always_comb obf_field_entropy_dbg = cptra_in_debug_scan_mode ? `CLP_DEBUG_MODE_FIELD_ENTROPY : obf_field_entropy;

doe_ctrl #(
    .AHB_DATA_WIDTH (`CALIPTRA_AHB_HDATA_SIZE),
    .AHB_ADDR_WIDTH (`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_DOE))
) doe (
    .clk               (clk_cg),
    .reset_n           (cptra_noncore_rst_b),
    .cptra_pwrgood     (cptra_pwrgood),
    .cptra_obf_key     (cptra_obf_key_dbg),
    .obf_uds_seed      (obf_uds_seed_dbg),
    .obf_field_entropy (obf_field_entropy_dbg),
    .haddr_i           (responder_inst[`CALIPTRA_SLAVE_SEL_DOE].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_DOE)-1:0]),
    .hwdata_i          (responder_inst[`CALIPTRA_SLAVE_SEL_DOE].hwdata),
    .hsel_i            (responder_inst[`CALIPTRA_SLAVE_SEL_DOE].hsel),
    .hwrite_i          (responder_inst[`CALIPTRA_SLAVE_SEL_DOE].hwrite),
    .hready_i          (responder_inst[`CALIPTRA_SLAVE_SEL_DOE].hready),
    .htrans_i          (responder_inst[`CALIPTRA_SLAVE_SEL_DOE].htrans),
    .hsize_i           (responder_inst[`CALIPTRA_SLAVE_SEL_DOE].hsize),
    .hresp_o           (responder_inst[`CALIPTRA_SLAVE_SEL_DOE].hresp),
    .hreadyout_o       (responder_inst[`CALIPTRA_SLAVE_SEL_DOE].hreadyout),
    .hrdata_o          (responder_inst[`CALIPTRA_SLAVE_SEL_DOE].hrdata),

    .error_intr(doe_error_intr),
    .notif_intr(doe_notif_intr),
    .clear_obf_secrets(clear_obf_secrets), //Output
    .kv_write (kv_write[KV_NUM_WRITE-1]),
    .kv_wr_resp (kv_wr_resp[KV_NUM_WRITE-1]),
    .debugUnlock_or_scan_mode_switch(debug_lock_or_scan_mode_switch)
    
);

ecc_top #(
    .AHB_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_ECC)),
    .AHB_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE)
)
ecc_top1
(
    .clk             (clk_cg),
    .reset_n         (cptra_noncore_rst_b),
    .cptra_pwrgood   (cptra_pwrgood),
    .haddr_i         (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_ECC)-1:0]),
    .hwdata_i        (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hwdata),
    .hsel_i          (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hsel),
    .hwrite_i        (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hwrite),
    .hready_i        (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hready),
    .htrans_i        (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].htrans),
    .hsize_i         (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hsize),
    .hresp_o         (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hresp),
    .hreadyout_o     (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hreadyout),
    .hrdata_o        (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hrdata),

    .kv_read         (kv_read[4:3]),
    .kv_rd_resp      (kv_rd_resp[4:3]),
    .kv_write        (kv_write[2]),
    .kv_wr_resp      (kv_wr_resp[2]),
    .pcr_signing_data(pcr_signing_data),

    .error_intr      (ecc_error_intr),
    .notif_intr      (ecc_notif_intr),
    .debugUnlock_or_scan_mode_switch(debug_lock_or_scan_mode_switch)
);

hmac_ctrl #(
     .AHB_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE),
     .AHB_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_HMAC))
)hmac (
     .clk(clk_cg),
     .reset_n       (cptra_noncore_rst_b),
     .cptra_pwrgood (cptra_pwrgood),
     .haddr_i       (responder_inst[`CALIPTRA_SLAVE_SEL_HMAC].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_HMAC)-1:0]),
     .hwdata_i      (responder_inst[`CALIPTRA_SLAVE_SEL_HMAC].hwdata),
     .hsel_i        (responder_inst[`CALIPTRA_SLAVE_SEL_HMAC].hsel),
     .hwrite_i      (responder_inst[`CALIPTRA_SLAVE_SEL_HMAC].hwrite),
     .hready_i      (responder_inst[`CALIPTRA_SLAVE_SEL_HMAC].hready),
     .htrans_i      (responder_inst[`CALIPTRA_SLAVE_SEL_HMAC].htrans),
     .hsize_i       (responder_inst[`CALIPTRA_SLAVE_SEL_HMAC].hsize),
     .hresp_o       (responder_inst[`CALIPTRA_SLAVE_SEL_HMAC].hresp),
     .hreadyout_o   (responder_inst[`CALIPTRA_SLAVE_SEL_HMAC].hreadyout),
     .hrdata_o      (responder_inst[`CALIPTRA_SLAVE_SEL_HMAC].hrdata),
     .kv_read       (kv_read[1:0]),
     .kv_write      (kv_write[0]),
     .kv_rd_resp    (kv_rd_resp[1:0]),
     .kv_wr_resp    (kv_wr_resp[0]),

     .error_intr(hmac_error_intr),
     .notif_intr(hmac_notif_intr),
     .debugUnlock_or_scan_mode_switch(debug_lock_or_scan_mode_switch)

);

kv #(
    .AHB_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_KV)),
    .AHB_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE)
)
key_vault1
(
    .clk                  (clk_cg),
    .rst_b                (cptra_noncore_rst_b),
    .core_only_rst_b      (cptra_uc_rst_b),
    .cptra_pwrgood        (cptra_pwrgood),
    .fw_update_rst_window (fw_update_rst_window),
    .haddr_i              (responder_inst[`CALIPTRA_SLAVE_SEL_KV].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_KV)-1:0]),
    .hwdata_i             (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hwdata),
    .hsel_i               (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hsel),
    .hwrite_i             (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hwrite),
    .hready_i             (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hready),
    .htrans_i             (responder_inst[`CALIPTRA_SLAVE_SEL_KV].htrans),
    .hsize_i              (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hsize),
    .hresp_o              (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hresp),
    .hreadyout_o          (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hreadyout),
    .hrdata_o             (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hrdata),

    .cptra_in_debug_scan_mode(cptra_in_debug_scan_mode),
    .debugUnlock_or_scan_mode_switch (debug_lock_or_scan_mode_switch),

    .kv_read              (kv_read),
    .kv_write             (kv_write),
    .kv_rd_resp           (kv_rd_resp),
    .kv_wr_resp           (kv_wr_resp),
    .pcr_signing_key      (pcr_signing_data.pcr_signing_privkey)
);

pv #(
    .AHB_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_PV)),
    .AHB_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE)
)
pcr_vault1
(
    .clk                  (clk_cg),
    .rst_b                (cptra_noncore_rst_b),
    .core_only_rst_b      (cptra_uc_rst_b),
    .cptra_pwrgood        (cptra_pwrgood),
    .fw_update_rst_window (fw_update_rst_window),
    .haddr_i              (responder_inst[`CALIPTRA_SLAVE_SEL_PV].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_PV)-1:0]),
    .hwdata_i             (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hwdata),
    .hsel_i               (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hsel),
    .hwrite_i             (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hwrite),
    .hready_i             (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hready),
    .htrans_i             (responder_inst[`CALIPTRA_SLAVE_SEL_PV].htrans),
    .hsize_i              (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hsize),
    .hresp_o              (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hresp),
    .hreadyout_o          (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hreadyout),
    .hrdata_o             (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hrdata),

    .pv_read              (pv_read),
    .pv_write             (pv_write),
    .pv_rd_resp           (pv_rd_resp),
    .pv_wr_resp           (pv_wr_resp)
);

dv #(
    .AHB_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_DV)),
    .AHB_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE)
)
data_vault1
(
    .clk             (clk_cg),
    .rst_b           (cptra_noncore_rst_b),
    .core_only_rst_b (cptra_uc_rst_b),
    .cptra_pwrgood (cptra_pwrgood),
    .haddr_i         (responder_inst[`CALIPTRA_SLAVE_SEL_DV].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_DV)-1:0]),
    .hwdata_i        (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hwdata),
    .hsel_i          (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hsel),
    .hwrite_i        (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hwrite),
    .hready_i        (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hready),
    .htrans_i        (responder_inst[`CALIPTRA_SLAVE_SEL_DV].htrans),
    .hsize_i         (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hsize),
    .hresp_o         (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hresp),
    .hreadyout_o     (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hreadyout),
    .hrdata_o        (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hrdata)
);

`ifdef CALIPTRA_INTERNAL_TRNG
entropy_src_hw_if_req_t entropy_src_hw_if_req;
entropy_src_hw_if_rsp_t entropy_src_hw_if_rsp;
cs_aes_halt_req_t       csrng_cs_aes_halt_req;
cs_aes_halt_rsp_t       csrng_cs_aes_halt_rsp;
entropy_src_rng_req_t   entropy_src_rng_req;
entropy_src_rng_rsp_t   entropy_src_rng_rsp;

assign etrng_req = entropy_src_rng_req.rng_enable;
assign entropy_src_rng_rsp.rng_valid = itrng_valid;
assign entropy_src_rng_rsp.rng_b = itrng_data;

// TODO: Revisit ports and verify connectivity

csrng #(
    .AHBDataWidth(`CALIPTRA_AHB_HDATA_SIZE),
    .AHBAddrWidth(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_CSRNG))
) csrng (
    // Clock and reset connections
    .clk_i                  (clk_cg),
    .rst_ni                 (cptra_noncore_rst_b),
    // AMBA AHB Lite Interface
    .haddr_i                (responder_inst[`CALIPTRA_SLAVE_SEL_CSRNG].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_CSRNG)-1:0]),
    .hwdata_i               (responder_inst[`CALIPTRA_SLAVE_SEL_CSRNG].hwdata),
    .hsel_i                 (responder_inst[`CALIPTRA_SLAVE_SEL_CSRNG].hsel),
    .hwrite_i               (responder_inst[`CALIPTRA_SLAVE_SEL_CSRNG].hwrite),
    .hready_i               (responder_inst[`CALIPTRA_SLAVE_SEL_CSRNG].hready),
    .htrans_i               (responder_inst[`CALIPTRA_SLAVE_SEL_CSRNG].htrans),
    .hsize_i                (responder_inst[`CALIPTRA_SLAVE_SEL_CSRNG].hsize),
    .hresp_o                (responder_inst[`CALIPTRA_SLAVE_SEL_CSRNG].hresp),
    .hreadyout_o            (responder_inst[`CALIPTRA_SLAVE_SEL_CSRNG].hreadyout),
    .hrdata_o               (responder_inst[`CALIPTRA_SLAVE_SEL_CSRNG].hrdata),
     // OTP Interface
    .otp_en_csrng_sw_app_read_i(caliptra_prim_mubi_pkg::MuBi8True),
    // Lifecycle broadcast inputs
    .lc_hw_debug_en_i       (lc_ctrl_pkg::On),
    // Entropy Interface
    .entropy_src_hw_if_o    (entropy_src_hw_if_req),
    .entropy_src_hw_if_i    (entropy_src_hw_if_rsp),
    .cs_aes_halt_i          (csrng_cs_aes_halt_req),
    .cs_aes_halt_o          (csrng_cs_aes_halt_rsp),
    // Application Interfaces
    .csrng_cmd_i            ('0),
    .csrng_cmd_o            (),
    // Alerts
    .alert_tx_o             (),
    .alert_rx_i             ({caliptra_prim_alert_pkg::ALERT_RX_DEFAULT, caliptra_prim_alert_pkg::ALERT_RX_DEFAULT}),
    // Interrupt
    .intr_cs_cmd_req_done_o (),
    .intr_cs_entropy_req_o  (),
    .intr_cs_hw_inst_exc_o  (),
    .intr_cs_fatal_err_o    ()
  );

entropy_src #(
    .AHBDataWidth(`CALIPTRA_AHB_HDATA_SIZE),
    .AHBAddrWidth(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_ENTROPY_SRC))
) entropy_src (
    .clk_i                  (clk_cg),
    .rst_ni                 (cptra_noncore_rst_b),
    // AMBA AHB Lite Interface
    .haddr_i                (responder_inst[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_ENTROPY_SRC)-1:0]),
    .hwdata_i               (responder_inst[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC].hwdata),
    .hsel_i                 (responder_inst[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC].hsel),
    .hwrite_i               (responder_inst[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC].hwrite),
    .hready_i               (responder_inst[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC].hready),
    .htrans_i               (responder_inst[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC].htrans),
    .hsize_i                (responder_inst[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC].hsize),
    .hresp_o                (responder_inst[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC].hresp),
    .hreadyout_o            (responder_inst[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC].hreadyout),
    .hrdata_o               (responder_inst[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC].hrdata),
    // OTP Interface
    .otp_en_entropy_src_fw_read_i(caliptra_prim_mubi_pkg::MuBi8True),
    .otp_en_entropy_src_fw_over_i(caliptra_prim_mubi_pkg::MuBi8True),
    // RNG Interface
    .rng_fips_o                       (),
    // Entropy Interface
    .entropy_src_hw_if_i              (entropy_src_hw_if_req),
    .entropy_src_hw_if_o              (entropy_src_hw_if_rsp),
    // RNG Interface
    .entropy_src_rng_o                (entropy_src_rng_req),
    .entropy_src_rng_i                (entropy_src_rng_rsp),
    // CSRNG Interface
    .cs_aes_halt_o                    (csrng_cs_aes_halt_req),
    .cs_aes_halt_i                    (csrng_cs_aes_halt_rsp),
    // External Health Test Interface
    .entropy_src_xht_o                (),
    .entropy_src_xht_i                (entropy_src_xht_rsp_t'('0)),
    // Alerts
    .alert_rx_i                       ({caliptra_prim_alert_pkg::ALERT_RX_DEFAULT, caliptra_prim_alert_pkg::ALERT_RX_DEFAULT}),
    .alert_tx_o                       (),
    // Interrupts
    .intr_es_entropy_valid_o          (),
    .intr_es_health_test_failed_o     (),
    .intr_es_observe_fifo_ready_o     (),
    .intr_es_fatal_err_o              ()
    );

`endif


`ifdef CALIPTRA_INTERNAL_QSPI

  logic                               cio_sck_o;
  logic                               cio_sck_en_o;
  logic [`CALIPTRA_QSPI_CS_WIDTH-1:0] cio_csb_o;
  logic [`CALIPTRA_QSPI_CS_WIDTH-1:0] cio_csb_en_o;

  assign qspi_clk_o = cio_sck_en_o ? cio_sck_o : 1'b0;
  for (genvar ii = 0; ii < `CALIPTRA_QSPI_CS_WIDTH; ii += 1) begin : gen_qspi_cs
    assign qspi_cs_no[ii] = cio_csb_en_o[ii] ? cio_csb_o[ii] : 1'b1;
  end

spi_host #(
    .AHBDataWidth(`CALIPTRA_AHB_HDATA_SIZE),
    .AHBAddrWidth(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_QSPI))
) spi_host (
    // Clock and reset connections
    .clk_i                  (clk_cg),
    .rst_ni                 (cptra_noncore_rst_b),
    // AMBA AHB Lite Interface
    .haddr_i                (responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_QSPI)-1:0]),
    .hwdata_i               (responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hwdata),
    .hsel_i                 (responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hsel),
    .hwrite_i               (responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hwrite),
    .hready_i               (responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hready),
    .htrans_i               (responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].htrans),
    .hsize_i                (responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hsize),
    .hresp_o                (responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hresp),
    .hreadyout_o            (responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hreadyout),
    .hrdata_o               (responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hrdata),
    // Alerts
    .alert_rx_i(caliptra_prim_alert_pkg::ALERT_RX_DEFAULT),
    .alert_tx_o(),
    // SPI Interface
    .cio_sck_o    (cio_sck_o),
    .cio_sck_en_o (cio_sck_en_o),
    .cio_csb_o    (cio_csb_o),
    .cio_csb_en_o (cio_csb_en_o),
    .cio_sd_o     (qspi_d_o),
    .cio_sd_en_o  (qspi_d_en_o),
    .cio_sd_i     (qspi_d_i),
    .intr_error_o(),
    .intr_spi_event_o()
  );
`else
//QSPI Tie Off
assign qspi_clk_o = '0;
assign qspi_cs_no = '0;
assign qspi_d_o = '0;
assign qspi_d_en_o = '0;
`endif

`ifdef CALIPTRA_INTERNAL_UART
uart #(
    .AHBDataWidth(`CALIPTRA_AHB_HDATA_SIZE),
    .AHBAddrWidth(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_UART))
) uart (
    .clk_i       (clk_cg),
    .rst_ni      (cptra_noncore_rst_b),
    // AMBA AHB Lite Interface
    .haddr_i     (responder_inst[`CALIPTRA_SLAVE_SEL_UART].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_UART)-1:0]),
    .hwdata_i    (responder_inst[`CALIPTRA_SLAVE_SEL_UART].hwdata),
    .hsel_i      (responder_inst[`CALIPTRA_SLAVE_SEL_UART].hsel),
    .hwrite_i    (responder_inst[`CALIPTRA_SLAVE_SEL_UART].hwrite),
    .hready_i    (responder_inst[`CALIPTRA_SLAVE_SEL_UART].hready),
    .htrans_i    (responder_inst[`CALIPTRA_SLAVE_SEL_UART].htrans),
    .hsize_i     (responder_inst[`CALIPTRA_SLAVE_SEL_UART].hsize),
    .hresp_o     (responder_inst[`CALIPTRA_SLAVE_SEL_UART].hresp),
    .hreadyout_o (responder_inst[`CALIPTRA_SLAVE_SEL_UART].hreadyout),
    .hrdata_o    (responder_inst[`CALIPTRA_SLAVE_SEL_UART].hrdata),
    // Alerts
    .alert_rx_i  (),
    .alert_tx_o  (),
    // Generic IO
    .cio_rx_i(uart_rx),
    .cio_tx_o(uart_tx),
    .cio_tx_en_o(),
    // Interrupts
    .intr_tx_watermark_o(),
    .intr_rx_watermark_o(),
    .intr_tx_empty_o(),
    .intr_rx_overflow_o(),
    .intr_rx_frame_err_o(),
    .intr_rx_break_err_o(),
    .intr_rx_timeout_o(),
    .intr_rx_parity_err_o()
  );
`endif

soc_ifc_top #(
    .AHB_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
    .AHB_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE),
    .APB_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
    .APB_DATA_WIDTH(`CALIPTRA_APB_DATA_WIDTH),
    .APB_USER_WIDTH(`CALIPTRA_APB_USER_WIDTH)
    )
soc_ifc_top1 
    (
    .clk(clk),
    .clk_cg(clk_cg),
    .soc_ifc_clk_cg(soc_ifc_clk_cg),
    .rdc_clk_cg(rdc_clk_cg),
    .cptra_pwrgood(cptra_pwrgood), 
    .cptra_rst_b(cptra_rst_b),
    .ready_for_fuses(ready_for_fuses),
    .ready_for_fw_push(ready_for_fw_push),
    .ready_for_runtime(ready_for_runtime),
    .mailbox_data_avail(mailbox_data_avail),
    .mailbox_flow_done(mailbox_flow_done),

    .security_state(cptra_security_state_Latched),
    
    .BootFSM_BrkPoint (BootFSM_BrkPoint),
    
    .generic_input_wires(generic_input_wires),
    .generic_output_wires(generic_output_wires),

    //SRAM interface
    .mbox_sram_req(mbox_sram_req),
    .mbox_sram_resp(mbox_sram_resp),

    // RV ECC Status Interface
    .rv_ecc_sts(rv_ecc_sts),

    //APB Interface with SoC
    .paddr_i(PADDR[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)-1:0]),
    .psel_i(PSEL),
    .penable_i(PENABLE),
    .pwrite_i(PWRITE),
    .pwdata_i(PWDATA),
    .pauser_i(PAUSER),
    .pready_o(PREADY),
    .prdata_o(PRDATA),
    .pslverr_o(PSLVERR),
    //AHB Interface with uC
    .haddr_i    (responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)-1:0]), 
    .hwdata_i   (responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hwdata), 
    .hsel_i     (responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hsel), 
    .hwrite_i   (responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hwrite),
    .hready_i   (responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hready),
    .htrans_i   (responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].htrans),
    .hsize_i    (responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hsize),
    .hresp_o    (responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hresp),
    .hreadyout_o(responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hreadyout),
    .hrdata_o   (responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hrdata),
    //SoC Interrupts
    .cptra_error_fatal    (cptra_error_fatal),
    .cptra_error_non_fatal(cptra_error_non_fatal),
`ifdef CALIPTRA_INTERNAL_TRNG
    .trng_req             (),
`else
    .trng_req             (etrng_req),
`endif
    // uC Interrupts
    .soc_ifc_error_intr(soc_ifc_error_intr),
    .soc_ifc_notif_intr(soc_ifc_notif_intr),
    .sha_error_intr(sha_error_intr),
    .sha_notif_intr(sha_notif_intr),
    .timer_intr(timer_int),
    //Obfuscated UDS and FE
    .clear_obf_secrets(clear_obf_secrets_debugScanQ), //input - includes debug & scan modes to do the register clearing
    .scan_mode(scan_mode),
    .cptra_obf_key(cptra_obf_key),
    .cptra_obf_key_reg(cptra_obf_key_reg),
    .obf_field_entropy(obf_field_entropy),
    .obf_uds_seed(obf_uds_seed),
    // NMI Vector 
    .nmi_vector(nmi_vector),
    .nmi_intr(nmi_int),
    // ICCM Lock
    .iccm_lock       (iccm_lock                                    ),
    .iccm_axs_blocked(ahb_lite_resp_access_blocked[`CALIPTRA_SLAVE_SEL_IDMA]),
    //uC reset
    .cptra_noncore_rst_b (cptra_noncore_rst_b),
    .cptra_uc_rst_b (cptra_uc_rst_b),
    //Clock gating en
    .clk_gating_en(clk_gating_en),
    .rdc_clk_dis(rdc_clk_dis),
    .fw_update_rst_window(fw_update_rst_window),

    //caliptra uncore jtag ports
    .cptra_uncore_dmi_reg_en   ( cptra_uncore_dmi_reg_en ),
    .cptra_uncore_dmi_reg_wr_en( cptra_uncore_dmi_reg_wr_en ),
    .cptra_uncore_dmi_reg_rdata( cptra_uncore_dmi_reg_rdata ),
    .cptra_uncore_dmi_reg_addr ( cptra_uncore_dmi_reg_addr ),
    .cptra_uncore_dmi_reg_wdata( cptra_uncore_dmi_reg_wdata )
);

//TIE OFF slaves
always_comb begin: tie_off_slaves
`ifndef CALIPTRA_INTERNAL_QSPI
    responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hresp = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hreadyout = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hrdata = '0;
`endif
`ifndef CALIPTRA_INTERNAL_UART
    responder_inst[`CALIPTRA_SLAVE_SEL_UART].hresp = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_UART].hreadyout = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_UART].hrdata = '0;
`endif
    responder_inst[`CALIPTRA_SLAVE_SEL_I3C].hresp = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_I3C].hreadyout = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_I3C].hrdata = '0;

`ifndef CALIPTRA_INTERNAL_TRNG
    responder_inst[`CALIPTRA_SLAVE_SEL_CSRNG].hresp = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_CSRNG].hreadyout = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_CSRNG].hrdata = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC].hresp = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC].hreadyout = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_ENTROPY_SRC].hrdata = '0;
`endif
end

genvar sva_i;
generate
  for(sva_i= 0; sva_i<`CALIPTRA_AHB_SLAVES_NUM; sva_i=sva_i+1)
  begin: gen_caliptra_asserts
    `CALIPTRA_ASSERT_KNOWN(AHB_SLAVE_HADDR_X,        responder_inst[sva_i].haddr,       clk, cptra_noncore_rst_b)
    `CALIPTRA_ASSERT_KNOWN(AHB_SLAVE_HWDATA_X,       responder_inst[sva_i].hwdata,      clk, cptra_noncore_rst_b)
    `CALIPTRA_ASSERT_KNOWN(AHB_SLAVE_HSEL_X,         responder_inst[sva_i].hsel,        clk, cptra_noncore_rst_b)
    `CALIPTRA_ASSERT_KNOWN(AHB_SLAVE_HWRITE_X,       responder_inst[sva_i].hwrite,      clk, cptra_noncore_rst_b)
    `CALIPTRA_ASSERT_KNOWN(AHB_SLAVE_HREADY_X,       responder_inst[sva_i].hready,      clk, cptra_noncore_rst_b)
    `CALIPTRA_ASSERT_KNOWN(AHB_SLAVE_HTRANS_X,       responder_inst[sva_i].htrans,      clk, cptra_noncore_rst_b)
    `CALIPTRA_ASSERT_KNOWN(AHB_SLAVE_HSIZE_X,        responder_inst[sva_i].hsize,       clk, cptra_noncore_rst_b)
    `CALIPTRA_ASSERT_KNOWN(AHB_SLAVE_HRESP_X,        responder_inst[sva_i].hresp,       clk, cptra_noncore_rst_b)
    `CALIPTRA_ASSERT_KNOWN(AHB_SLAVE_HREADYOUT_X,    responder_inst[sva_i].hreadyout,   clk, cptra_noncore_rst_b)
    `CALIPTRA_ASSERT_KNOWN(AHB_SLAVE_HRDATA_X,       responder_inst[sva_i].hreadyout ? responder_inst[sva_i].hrdata : '0,      clk, cptra_noncore_rst_b)
  end
endgenerate

`CALIPTRA_ASSERT_KNOWN(AHB_MASTER_HADDR_X,        initiator_inst.haddr,       clk, cptra_noncore_rst_b)
`CALIPTRA_ASSERT_KNOWN(AHB_MASTER_HWDATA_X,       initiator_inst.hwdata,      clk, cptra_noncore_rst_b)
`CALIPTRA_ASSERT_KNOWN(AHB_MASTER_HWRITE_X,       initiator_inst.hwrite,      clk, cptra_noncore_rst_b)
`CALIPTRA_ASSERT_KNOWN(AHB_MASTER_HREADY_X,       initiator_inst.hready,      clk, cptra_noncore_rst_b)
`CALIPTRA_ASSERT_KNOWN(AHB_MASTER_HTRANS_X,       initiator_inst.htrans,      clk, cptra_noncore_rst_b)
`CALIPTRA_ASSERT_KNOWN(AHB_MASTER_HSIZE_X,        initiator_inst.hsize,       clk, cptra_noncore_rst_b)
`CALIPTRA_ASSERT_KNOWN(AHB_MASTER_HRESP_X,        initiator_inst.hresp,       clk, cptra_noncore_rst_b)
`CALIPTRA_ASSERT_KNOWN(AHB_MASTER_HRDATA_X,       initiator_inst.hready ? initiator_inst.hrdata : '0,      clk, cptra_noncore_rst_b)
`CALIPTRA_ASSERT_NEVER(AHB_MASTER_HTRANS_BUSY,    initiator_inst.htrans == 2'b01, clk, cptra_noncore_rst_b)

`CALIPTRA_ASSERT_KNOWN(APB_MASTER_PADDR_X,        PADDR,                clk, cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(APB_MASTER_PWDATA_X,       PWDATA,               clk, cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(APB_MASTER_PWRITE_X,       PWRITE,               clk, cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(APB_MASTER_PREADY_X,       PREADY,               clk, cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(APB_MASTER_PENABLE_X,      PENABLE,              clk, cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(APB_MASTER_PSEL_X,         PSEL,                 clk, cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(APB_MASTER_PPROT_X,        PPROT,                clk, cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(APB_MASTER_PAUSER_X,       PAUSER,               clk, cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(APB_MASTER_PSLVERR_X,      PSLVERR,              clk, cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(APB_MASTER_PRDATA_X,       PREADY ? PRDATA : '0, clk, cptra_rst_b)

`CALIPTRA_ASSERT_NEVER(APB_MASTER_PPROT_ACTIVE,   PPROT !== 3'b000, clk, cptra_rst_b)

// Check that the mode has been properly defined at compile time by attempting
// an illegal construct if no mode is detected
`ifndef CALIPTRA_MODE_CORE
 `ifndef CALIPTRA_MODE_SEED
  ERROR_NO_CALIPTRA_MODE_DEFINED_AT_COMPILE TIME();
  `CALIPTRA_ASSERT_I(NO_CALIPTRA_MODE_DEF, 0)
 `endif
`endif
`ifdef CALIPTRA_MODE_CORE
 `ifdef CALIPTRA_MODE_SEED
  ERROR_MULTIPLE_CALIPTRA_MODES_DEFINED_AT_COMPILE TIME();
  `CALIPTRA_ASSERT_I(MULTI_CALIPTRA_MODE_DEF, 0)
 `endif
`endif

endmodule
