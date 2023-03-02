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
    (
    input logic                        clk,

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
    input  logic [`CALIPTRA_APB_ADDR_WIDTH-1:0] PADDR,
    input  logic [2:0]                 PPROT,
    input  logic                       PSEL,
    input  logic                       PENABLE,
    input  logic                       PWRITE,
    input  logic [`CALIPTRA_APB_DATA_WIDTH-1:0] PWDATA,
    input  logic [`CALIPTRA_APB_USER_WIDTH-1:0] PAUSER,

    output logic                       PREADY,
    output logic                       PSLVERR,
    output logic [`CALIPTRA_APB_DATA_WIDTH-1:0] PRDATA,

    //QSPI Interface
    output logic                       qspi_clk_o,
    output logic [`CALIPTRA_QSPI_CS_WIDTH-1:0]  qspi_cs_no,
    inout  wire  [`CALIPTRA_QSPI_IO_WIDTH-1:0]  qspi_d_io,

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
    output logic             trng_req,

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
    logic                       clk_cg          ;
    logic                       soc_ifc_clk_cg  ;

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
    kv_wr_resp_t [KV_NUM_READ-1:0] kv_wr_resp;

    pv_read_t [PV_NUM_READ-1:0]  pv_read;
    pv_write_t [PV_NUM_WRITE-1:0]  pv_write;
    pv_rd_resp_t [PV_NUM_READ-1:0] pv_rd_resp;
    pv_wr_resp_t [PV_NUM_READ-1:0] pv_wr_resp;

    //mailbox sram gasket
    mbox_sram_req_t mbox_sram_req;
    mbox_sram_resp_t mbox_sram_resp;

    logic clear_obf_secrets;
    logic clear_secrets;
    
    logic cptra_security_state_captured, scan_mode_f, scan_mode_ff, scan_mode_switch;
    logic debugUnlock_or_scan_mode_switch, clear_obf_secrets_debugScanQ, cptra_scan_mode_Latched, debug_lock_to_unlock_switch;
    var security_state_t security_state_f, security_state_ff;
    
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
    responder_inst[`CALIPTRA_AHB_SLAVES_NUM-1:0]();

    //========================================================================
    // AHB Master ports
    //========================================================================
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


   //=========================================================================-
   // RTL instance
   //=========================================================================-
//FIXME TIE OFFS
logic [31:0] jtag_id;
logic [31:0] reset_vector;
logic [31:0] nmi_vector;
logic nmi_int;
logic soft_int;
logic timer_int;

assign jtag_id[31:28] = 4'b1;
assign jtag_id[27:12] = '0;
assign jtag_id[11:1]  = 11'h45;
assign reset_vector = `RV_RESET_VEC;
assign nmi_int      = 1'b0;
assign soft_int     = 1'b0;
assign timer_int    = 1'b0;

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
    .rst_l                  ( cptra_uc_rst_b),
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

    .soft_int               (soft_int),
    .core_id                ('0),
    .scan_mode              ( cptra_scan_mode_Latched ), // To enable scan mode
    .mbist_mode             ( 1'b0 )        // to enable mbist

);
    // Duplicate ICCM/DCCM accesses, using only hsel to differentiate
    always_comb responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hrdata    = responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hrdata;
    always_comb responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hresp     = responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hresp;
    always_comb responder_inst[`CALIPTRA_SLAVE_SEL_IDMA].hreadyout = responder_inst[`CALIPTRA_SLAVE_SEL_DDMA].hreadyout;

    // Security State value captured on a Caliptra reset deassertion (0->1 signal transition)
    always_ff @(posedge clk or negedge cptra_rst_b) begin
        if (~cptra_rst_b) begin
            cptra_security_state_Latched <= '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1}; //Setting the default value to be debug locked and in production mode
            security_state_f <= '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1}; //Setting the default value to be debug locked and in production mode
            cptra_security_state_captured <= 0;
            scan_mode_f <= 0;
        end
        else if(!cptra_security_state_captured) begin
            cptra_security_state_Latched <= security_state;
            cptra_scan_mode_Latched <= scan_mode;
            cptra_security_state_captured <= 1;
        end
        else begin
            // Latched State is different than flopped value of security state
            // Latched State is used if we want to open the JTAG and is
            // determined to do so only at reset exit time
            // Asset flushing happens 'anytime' switch happens for safe side
            security_state_f  <= security_state;
            security_state_ff  <= security_state_f;
            scan_mode_f  <= scan_mode;
            scan_mode_ff <= scan_mode_f;
        end
    end

    // When scan mode goes from 0->1, generate a pulse to clear the assets
    // Note that when scan goes to '1, Caliptra state as well as SOC state
    // gets messed up. So switch to scan is destructive (obvious! Duh!)
    assign scan_mode_switch = ~scan_mode_ff & scan_mode_f;
    // 1->0 transition (Debug locked to unlocked)
    assign debug_lock_to_unlock_switch = security_state_ff.debug_locked & ~security_state_f.debug_locked;
    assign debugUnlock_or_scan_mode_switch = debug_lock_to_unlock_switch | scan_mode_switch;
    assign clear_obf_secrets_debugScanQ = clear_obf_secrets | debugUnlock_or_scan_mode_switch;

//=========================================================================-
// Clock gating instance
//=========================================================================-
clk_gate cg (
    .clk(clk),
    .cptra_rst_b(cptra_noncore_rst_b),
    .psel(PSEL),
    .clk_gate_en(clk_gating_en),
    .cpu_halt_status(o_cpu_halt_status),
    .clk_cg (clk_cg),
    .soc_ifc_clk_cg (soc_ifc_clk_cg),
    .generic_input_wires(generic_input_wires)
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
    .hreset_n       (cptra_noncore_rst_b),
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
    .hreset_n   (cptra_noncore_rst_b),
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
    .AHB_DATA_WIDTH (64),
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

    .error_intr(sha512_error_intr),
    .notif_intr(sha512_notif_intr)
);

sha256_ctrl #(
    .AHB_DATA_WIDTH (64),
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
    .notif_intr(sha256_notif_intr)
);

//override device secrets with debug values in Debug or Scan Mode
always_comb cptra_in_debug_scan_mode = ~security_state_f.debug_locked | scan_mode_f;
always_comb cptra_obf_key_dbg     = cptra_in_debug_scan_mode ? `CLP_DEBUG_MODE_OBF_KEY : cptra_obf_key_reg;
always_comb obf_uds_seed_dbg      = cptra_in_debug_scan_mode ? `CLP_DEBUG_MODE_UDS_SEED : obf_uds_seed;
always_comb obf_field_entropy_dbg = cptra_in_debug_scan_mode ? `CLP_DEBUG_MODE_FIELD_ENTROPY : obf_field_entropy;

doe_ctrl #(
    .AHB_DATA_WIDTH (64),
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
    .kv_wr_resp (kv_wr_resp[KV_NUM_WRITE-1])

    
);

ecc_top #(
    .AHB_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_ECC)),
    .AHB_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE)
)
ecc_top1
(
    .clk           (clk_cg),
    .reset_n       (cptra_noncore_rst_b),
    .cptra_pwrgood (cptra_pwrgood),
    .haddr_i       (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_ECC)-1:0]),
    .hwdata_i      (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hwdata),
    .hsel_i        (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hsel),
    .hwrite_i      (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hwrite),
    .hready_i      (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hready),
    .htrans_i      (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].htrans),
    .hsize_i       (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hsize),
    .hresp_o       (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hresp),
    .hreadyout_o   (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hreadyout),
    .hrdata_o      (responder_inst[`CALIPTRA_SLAVE_SEL_ECC].hrdata),

    .kv_read        (kv_read[5:3]),
    .kv_rd_resp     (kv_rd_resp[5:3]),
    .kv_write       (kv_write[2]),
    .kv_wr_resp     (kv_wr_resp[2]),

    .error_intr    (ecc_error_intr),
    .notif_intr    (ecc_notif_intr)
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
     .notif_intr(hmac_notif_intr)

);

kv #(
    .AHB_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_KV)),
    .AHB_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE)
)
key_vault1
(
    .clk              (clk_cg),
    .rst_b            (cptra_noncore_rst_b),
    .core_only_rst_b  (cptra_uc_rst_b),
    .cptra_pwrgood    (cptra_pwrgood),
    .haddr_i          (responder_inst[`CALIPTRA_SLAVE_SEL_KV].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_KV)-1:0]),
    .hwdata_i         (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hwdata),
    .hsel_i           (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hsel),
    .hwrite_i         (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hwrite),
    .hready_i         (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hready),
    .htrans_i         (responder_inst[`CALIPTRA_SLAVE_SEL_KV].htrans),
    .hsize_i          (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hsize),
    .hresp_o          (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hresp),
    .hreadyout_o      (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hreadyout),
    .hrdata_o         (responder_inst[`CALIPTRA_SLAVE_SEL_KV].hrdata),

    .debugUnlock_or_scan_mode_switch (debugUnlock_or_scan_mode_switch),

    .kv_read          (kv_read),
    .kv_write         (kv_write),
    .kv_rd_resp       (kv_rd_resp),
    .kv_wr_resp       (kv_wr_resp)
);

pv #(
    .AHB_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_PV)),
    .AHB_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE)
)
pcr_vault1
(
    .clk           (clk_cg),
    .rst_b         (cptra_noncore_rst_b),
    .cptra_pwrgood (cptra_pwrgood),
    .haddr_i       (responder_inst[`CALIPTRA_SLAVE_SEL_PV].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_PV)-1:0]),
    .hwdata_i      (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hwdata),
    .hsel_i        (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hsel),
    .hwrite_i      (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hwrite),
    .hready_i      (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hready),
    .htrans_i      (responder_inst[`CALIPTRA_SLAVE_SEL_PV].htrans),
    .hsize_i       (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hsize),
    .hresp_o       (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hresp),
    .hreadyout_o   (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hreadyout),
    .hrdata_o      (responder_inst[`CALIPTRA_SLAVE_SEL_PV].hrdata),

    .pv_read       (pv_read),
    .pv_write      (pv_write),
    .pv_rd_resp    (pv_rd_resp),
    .pv_wr_resp    (pv_wr_resp)
);

dv #(
    .AHB_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_DV)),
    .AHB_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE)
)
data_vault1
(
    .clk           (clk_cg),
    .rst_b         (cptra_noncore_rst_b),
    .cptra_pwrgood (cptra_pwrgood),
    .haddr_i       (responder_inst[`CALIPTRA_SLAVE_SEL_DV].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_DV)-1:0]),
    .hwdata_i      (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hwdata),
    .hsel_i        (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hsel),
    .hwrite_i      (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hwrite),
    .hready_i      (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hready),
    .htrans_i      (responder_inst[`CALIPTRA_SLAVE_SEL_DV].htrans),
    .hsize_i       (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hsize),
    .hresp_o       (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hresp),
    .hreadyout_o   (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hreadyout),
    .hrdata_o      (responder_inst[`CALIPTRA_SLAVE_SEL_DV].hrdata)
);

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
    .cptra_pwrgood(cptra_pwrgood), 
    .cptra_rst_b(cptra_rst_b),
    .ready_for_fuses(ready_for_fuses),
    .ready_for_fw_push(ready_for_fw_push),
    .ready_for_runtime(ready_for_runtime),
    .mailbox_data_avail(mailbox_data_avail),
    .mailbox_flow_done(mailbox_flow_done),

    .security_state(security_state_f),
    
    .BootFSM_BrkPoint (BootFSM_BrkPoint),
    
    .generic_input_wires(generic_input_wires),
    .generic_output_wires(generic_output_wires),

    //SRAM interface
    .mbox_sram_req(mbox_sram_req),
    .mbox_sram_resp(mbox_sram_resp),

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
    .trng_req             (trng_req),
    // uC Interrupts
    .soc_ifc_error_intr(soc_ifc_error_intr),
    .soc_ifc_notif_intr(soc_ifc_notif_intr),
    .sha_error_intr(sha_error_intr),
    .sha_notif_intr(sha_notif_intr),
    //Obfuscated UDS and FE
    .clear_obf_secrets(clear_obf_secrets_debugScanQ), //input - includes debug & scan modes to do the register clearing
    .scan_mode_f(scan_mode_f),
    .cptra_obf_key(cptra_obf_key),
    .cptra_obf_key_reg(cptra_obf_key_reg),
    .obf_field_entropy(obf_field_entropy),
    .obf_uds_seed(obf_uds_seed),
    // NMI Vector 
    .nmi_vector(nmi_vector),
    // ICCM Lock
    .iccm_lock       (iccm_lock                                    ),
    .iccm_axs_blocked(ahb_lite_resp_access_blocked[`CALIPTRA_SLAVE_SEL_IDMA]),
    //uC reset
    .cptra_noncore_rst_b (cptra_noncore_rst_b),
    .cptra_uc_rst_b (cptra_uc_rst_b),
    //Clock gating en
    .clk_gating_en(clk_gating_en),

    //caliptra uncore jtag ports
    .cptra_uncore_dmi_reg_en   ( cptra_uncore_dmi_reg_en ),
    .cptra_uncore_dmi_reg_wr_en( cptra_uncore_dmi_reg_wr_en ),
    .cptra_uncore_dmi_reg_rdata( cptra_uncore_dmi_reg_rdata ),
    .cptra_uncore_dmi_reg_addr ( cptra_uncore_dmi_reg_addr ),
    .cptra_uncore_dmi_reg_wdata( cptra_uncore_dmi_reg_wdata )
);

//TIE OFF slaves
always_comb begin: tie_off_slaves
    responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hresp = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hreadyout = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_QSPI].hrdata = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_UART].hresp = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_UART].hreadyout = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_UART].hrdata = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_I3C].hresp = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_I3C].hreadyout = '0;
    responder_inst[`CALIPTRA_SLAVE_SEL_I3C].hrdata = '0;
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

endmodule
