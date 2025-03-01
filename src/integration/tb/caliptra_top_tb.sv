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
`default_nettype none

`include "common_defines.sv"
`include "config_defines.svh"
`include "caliptra_reg_defines.svh"
`include "caliptra_reg_field_defines.svh"
`include "caliptra_macros.svh"

`ifndef VERILATOR
module caliptra_top_tb;
`else
module caliptra_top_tb (
    input bit core_clk,
    input bit rst_l
    );
`endif

    import axi_pkg::*;
    import soc_ifc_pkg::*;
    import caliptra_top_tb_pkg::*;

`ifndef VERILATOR
    // Time formatting for %t in display tasks
    // -9 = ns units
    // 3  = 3 bits of precision (to the ps)
    // "ns" = nanosecond suffix for output time values
    // 15 = 15 bits minimum field width
    initial $timeformat(-9, 3, " ns", 15); // up to 99ms representable in this width
`endif

`ifndef VERILATOR
    bit                         core_clk;
`endif

    int                         cycleCnt;


    logic                       cptra_pwrgood;
    logic                       cptra_rst_b;
    logic                       BootFSM_BrkPoint;
    logic                       scan_mode;

    logic [`CLP_OBF_KEY_DWORDS-1:0][31:0]          cptra_obf_key;
    
    logic [`CLP_CSR_HMAC_KEY_DWORDS-1:0][31:0]     cptra_csr_hmac_key;

    logic [0:`CLP_OBF_UDS_DWORDS-1][31:0]          cptra_uds_rand;
    logic [0:`CLP_OBF_FE_DWORDS-1][31:0]           cptra_fe_rand;
    logic [0:`CLP_OBF_KEY_DWORDS-1][31:0]          cptra_obf_key_tb;

    //jtag interface
    logic                       jtag_tck;    // JTAG clk
    logic                       jtag_tms;    // JTAG TMS
    logic                       jtag_tdi;    // JTAG tdi
    logic                       jtag_trst_n; // JTAG Reset
    logic                       jtag_tdo;    // JTAG TDO
    logic                       jtag_tdoEn;  // JTAG TDO enable

    // AXI Interface
    axi_if #(
        .AW(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) m_axi_bfm_if (.clk(core_clk), .rst_n(cptra_rst_b));
    axi_if #(
        .AW(`CALIPTRA_AXI_DMA_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH),
        .IW(CPTRA_AXI_DMA_ID_WIDTH),
        .UW(CPTRA_AXI_DMA_USER_WIDTH)
    ) m_axi_if (.clk(core_clk), .rst_n(cptra_rst_b));
    axi_if #(
        .AW(AXI_SRAM_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH),
        .IW(CPTRA_AXI_DMA_ID_WIDTH),
        .UW(CPTRA_AXI_DMA_USER_WIDTH)
    ) axi_sram_if (.clk(core_clk), .rst_n(cptra_rst_b));
    axi_if #(
        .AW(AXI_FIFO_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH),
        .IW(CPTRA_AXI_DMA_ID_WIDTH),
        .UW(CPTRA_AXI_DMA_USER_WIDTH)
    ) axi_fifo_if (.clk(core_clk), .rst_n(cptra_rst_b));

    logic ready_for_fuses;
    logic ready_for_mb_processing;
    logic mailbox_data_avail;
    logic mbox_sram_cs;
    logic mbox_sram_we;
    logic [CPTRA_MBOX_ADDR_W-1:0] mbox_sram_addr;
    logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] mbox_sram_wdata;
    logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] mbox_sram_rdata;

    logic imem_cs;
    logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] imem_addr;
    logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] imem_rdata;

    //device lifecycle
    security_state_t security_state;

    ras_test_ctrl_t ras_test_ctrl;
    logic [63:0] generic_input_wires;
    logic        etrng_req;
    logic  [3:0] itrng_data;
    logic        itrng_valid;

    logic cptra_error_fatal;
    logic cptra_error_non_fatal;

    //Interrupt flags
    logic int_flag;
    logic cycleCnt_smpl_en;

    //Reset flags
    logic assert_hard_rst_flag;
    logic deassert_hard_rst_flag;
    logic assert_rst_flag_from_service;
    logic deassert_rst_flag_from_service;

    el2_mem_if el2_mem_export ();
    mldsa_mem_if mldsa_memory_export();

`ifndef VERILATOR
    always
    begin : clk_gen
      core_clk = #5ns ~core_clk;
    end // clk_gen
`endif
    

caliptra_top_tb_soc_bfm soc_bfm_inst (
    .core_clk        (core_clk        ),

    .cptra_pwrgood   (cptra_pwrgood   ),
    .cptra_rst_b     (cptra_rst_b     ),

    .BootFSM_BrkPoint(BootFSM_BrkPoint),
    .cycleCnt        (cycleCnt        ),

    .cptra_obf_key      (cptra_obf_key   ),
    .cptra_csr_hmac_key (cptra_csr_hmac_key),

    .cptra_uds_rand  (cptra_uds_rand  ),
    .cptra_fe_rand   (cptra_fe_rand   ),
    .cptra_obf_key_tb(cptra_obf_key_tb),

    .m_axi_bfm_if(m_axi_bfm_if),

    .ready_for_fuses         (ready_for_fuses         ),
    .ready_for_mb_processing (ready_for_mb_processing ),
    .mailbox_data_avail(mailbox_data_avail),

    .ras_test_ctrl(ras_test_ctrl),

    .generic_input_wires(generic_input_wires),

    .cptra_error_fatal(cptra_error_fatal),
    .cptra_error_non_fatal(cptra_error_non_fatal),
    
    //Interrupt flags
    .int_flag(int_flag),
    .cycleCnt_smpl_en(cycleCnt_smpl_en),

    .assert_hard_rst_flag(assert_hard_rst_flag),
    .deassert_hard_rst_flag(deassert_hard_rst_flag),
    .assert_rst_flag_from_service(assert_rst_flag_from_service),
    .deassert_rst_flag_from_service(deassert_rst_flag_from_service)

);
    
// JTAG DPI
jtagdpi #(
    .Name           ("jtag0"),
    .ListenPort     (5000)
) jtagdpi (
    .clk_i          (core_clk),
    .rst_ni         (cptra_rst_b),
    .jtag_tck       (jtag_tck),
    .jtag_tms       (jtag_tms),
    .jtag_tdi       (jtag_tdi),
    .jtag_tdo       (jtag_tdo),
    .jtag_trst_n    (jtag_trst_n),
    .jtag_srst_n    ()
);

   //=========================================================================-
   // DUT instance
   //=========================================================================-
caliptra_top caliptra_top_dut (
    .cptra_pwrgood              (cptra_pwrgood),
    .cptra_rst_b                (cptra_rst_b),
    .clk                        (core_clk),

    .cptra_obf_key              (cptra_obf_key),
    .cptra_obf_uds_seed_vld     ('0), //TODO
    .cptra_obf_uds_seed         ('0), //TODO
    .cptra_obf_field_entropy_vld('0), //TODO
    .cptra_obf_field_entropy    ('0), //TODO
    .cptra_csr_hmac_key         (cptra_csr_hmac_key),

    .jtag_tck(jtag_tck),
    .jtag_tdi(jtag_tdi),
    .jtag_tms(jtag_tms),
    .jtag_trst_n(jtag_trst_n),
    .jtag_tdo(jtag_tdo),
    .jtag_tdoEn(jtag_tdoEn),
    
    //SoC AXI Interface
    .s_axi_w_if(m_axi_bfm_if.w_sub),
    .s_axi_r_if(m_axi_bfm_if.r_sub),

    //AXI DMA Interface
    .m_axi_w_if(m_axi_if.w_mgr),
    .m_axi_r_if(m_axi_if.r_mgr),

    .el2_mem_export(el2_mem_export.veer_sram_src),
    .mldsa_memory_export(mldsa_memory_export.req),
    
    .ready_for_fuses(ready_for_fuses),
    .ready_for_mb_processing(ready_for_mb_processing),
    .ready_for_runtime(),

    .mbox_sram_cs(mbox_sram_cs),
    .mbox_sram_we(mbox_sram_we),
    .mbox_sram_addr(mbox_sram_addr),
    .mbox_sram_wdata(mbox_sram_wdata),
    .mbox_sram_rdata(mbox_sram_rdata),
        
    .imem_cs(imem_cs),
    .imem_addr(imem_addr),
    .imem_rdata(imem_rdata),

    .mailbox_data_avail(mailbox_data_avail),
    .mailbox_flow_done(),
    .BootFSM_BrkPoint(BootFSM_BrkPoint),

    .recovery_data_avail(1'b1/*TODO*/),
    .recovery_image_activated(1'b0/*TODO*/),

    //SoC Interrupts
    .cptra_error_fatal    (cptra_error_fatal    ),
    .cptra_error_non_fatal(cptra_error_non_fatal),

`ifdef CALIPTRA_INTERNAL_TRNG
    .etrng_req             (etrng_req),
    .itrng_data            (itrng_data),
    .itrng_valid           (itrng_valid),
`else
    .etrng_req             (),
    .itrng_data            (4'b0),
    .itrng_valid           (1'b0),
`endif

    // Subsystem mode straps TODO
    .strap_ss_caliptra_base_addr                            (64'hba5e_ba11),
    .strap_ss_mci_base_addr                                 (64'h0),
    .strap_ss_recovery_ifc_base_addr                        (64'h0),
    .strap_ss_otp_fc_base_addr                              (64'h0),
    .strap_ss_uds_seed_base_addr                            (64'h0),
    .strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset(32'h0),
    .strap_ss_num_of_prod_debug_unlock_auth_pk_hashes       (32'h0),
    .strap_ss_caliptra_dma_axi_user                         (32'h0),
    .strap_ss_strap_generic_0                               (32'h0),
    .strap_ss_strap_generic_1                               (32'h0),
    .strap_ss_strap_generic_2                               (32'h0),
    .strap_ss_strap_generic_3                               (32'h0),
    .ss_debug_intent                                        ( 1'b0),

    // Subsystem mode debug outputs
    .ss_dbg_manuf_enable    (/*TODO*/),
    .ss_soc_dbg_unlock_level(/*TODO*/),

    // Subsystem mode firmware execution control
    .ss_generic_fw_exec_ctrl(/*TODO*/),

    .generic_input_wires (generic_input_wires),
    .generic_output_wires(                   ),

    // RISC-V Trace Ports
    .trace_rv_i_insn_ip     (), // TODO
    .trace_rv_i_address_ip  (), // TODO
    .trace_rv_i_valid_ip    (), // TODO
    .trace_rv_i_exception_ip(), // TODO
    .trace_rv_i_ecause_ip   (), // TODO
    .trace_rv_i_interrupt_ip(), // TODO
    .trace_rv_i_tval_ip     (), // TODO

    .security_state(security_state),
    .scan_mode     (scan_mode)
);


`ifdef CALIPTRA_INTERNAL_TRNG
    //=========================================================================-
    // Physical RNG used for Internal TRNG
    //=========================================================================-
physical_rng physical_rng (
    .clk    (core_clk),
    .enable (etrng_req),
    .data   (itrng_data),
    .valid  (itrng_valid)
);
`endif

   //=========================================================================-
   // Services for SRAM exports, STDOUT, etc
   //=========================================================================-
caliptra_top_tb_services #(
    .UVM_TB(0)
) tb_services_i (
    .clk(core_clk),

    .cptra_rst_b(cptra_rst_b),

    // Caliptra Memory Export Interface
    .el2_mem_export (el2_mem_export.veer_sram_sink),
    .mldsa_memory_export (mldsa_memory_export.resp),

    //SRAM interface for mbox
    .mbox_sram_cs   (mbox_sram_cs   ),
    .mbox_sram_we   (mbox_sram_we   ),
    .mbox_sram_addr (mbox_sram_addr ),
    .mbox_sram_wdata(mbox_sram_wdata),
    .mbox_sram_rdata(mbox_sram_rdata),

    //SRAM interface for imem
    .imem_cs   (imem_cs   ),
    .imem_addr (imem_addr ),
    .imem_rdata(imem_rdata),

    // Security State
    .security_state(security_state),

    //Scan mode
    .scan_mode(scan_mode),

    // TB Controls
    .ras_test_ctrl(ras_test_ctrl),
    .cycleCnt(cycleCnt),

    //Interrupt flags
    .int_flag(int_flag),
    .cycleCnt_smpl_en(cycleCnt_smpl_en),

    //Reset flags
    .assert_hard_rst_flag(assert_hard_rst_flag),
    .deassert_hard_rst_flag(deassert_hard_rst_flag),

    .assert_rst_flag(assert_rst_flag_from_service),
    .deassert_rst_flag(deassert_rst_flag_from_service),
    
    .cptra_uds_tb(cptra_uds_rand),
    .cptra_fe_tb(cptra_fe_rand),
    .cptra_obf_key_tb(cptra_obf_key_tb)

);

//=========================================================================-
// Dummy interconnect
//=========================================================================-
// --------------------- MUX Endpoints ---------------------
logic [1:0] sram_r_active;
logic       sram_ar_hshake;
logic       sram_rlast_hshake;

logic [1:0] sram_w_active;
logic       sram_aw_hshake;
logic       sram_b_hshake;

logic [1:0] fifo_r_active;
logic       fifo_ar_hshake;
logic       fifo_rlast_hshake;

logic [1:0] fifo_w_active;
logic       fifo_aw_hshake;
logic       fifo_b_hshake;

always_comb begin
    // AXI AR
    m_axi_if.arready          = (m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH]) ? axi_sram_if.arready :
                                (m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH]) ? axi_fifo_if.arready :
                                                                                                                                                                                  1'b0;
                                                
    // AXI R                                    
    m_axi_if.rdata            = sram_r_active ? axi_sram_if.rdata :
                                fifo_r_active ? axi_fifo_if.rdata :
                                                '0;
    m_axi_if.rresp            = sram_r_active ? axi_sram_if.rresp :
                                fifo_r_active ? axi_fifo_if.rresp :
                                                '0;
    m_axi_if.rid              = sram_r_active ? axi_sram_if.rid   :
                                fifo_r_active ? axi_fifo_if.rid   :
                                                '0;
    m_axi_if.ruser            = sram_r_active ? axi_sram_if.ruser :
                                fifo_r_active ? axi_fifo_if.ruser :
                                                '0;
    m_axi_if.rlast            = sram_r_active ? axi_sram_if.rlast :
                                fifo_r_active ? axi_fifo_if.rlast :
                                                '0;
    m_axi_if.ruser            = sram_r_active ? axi_sram_if.ruser :
                                fifo_r_active ? axi_fifo_if.ruser :
                                                '0;
    m_axi_if.rvalid           = sram_r_active ? axi_sram_if.rvalid :
                                fifo_r_active ? axi_fifo_if.rvalid :
                                                '0;
                                                
    // AXI AW                                   
    m_axi_if.awready          = (m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH]) ? axi_sram_if.awready :
                                (m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH]) ? axi_fifo_if.awready :
                                                                                                                                                                                  1'b0;
                                                
    // AXI W                                    
    m_axi_if.wready           = sram_w_active ? axi_sram_if.wready :
                                fifo_w_active ? axi_fifo_if.wready :
                                                1'b0;
                                                
    // AXI B                                    
    m_axi_if.bresp            = sram_w_active ? axi_sram_if.bresp :
                                fifo_w_active ? axi_fifo_if.bresp :
                                                '0;
    m_axi_if.bid              = sram_w_active ? axi_sram_if.bid :
                                fifo_w_active ? axi_fifo_if.bid :
                                                '0;
    m_axi_if.buser            = sram_w_active ? axi_sram_if.buser :
                                fifo_w_active ? axi_fifo_if.buser :
                                                '0;
    m_axi_if.bvalid           = sram_w_active ? axi_sram_if.bvalid :
                                fifo_w_active ? axi_fifo_if.bvalid :
                                                '0;
end

// --------------------- SRAM Endpoint ---------------------
always_comb begin
    sram_ar_hshake    = axi_sram_if.arvalid && axi_sram_if.arready;
    sram_rlast_hshake = axi_sram_if.rvalid  && axi_sram_if.rready && axi_sram_if.rlast;
end
always_ff@(posedge core_clk or negedge cptra_rst_b) begin
    if (!cptra_rst_b) begin
        sram_r_active <= 2'b0;;
    end
    else begin
        case ({sram_ar_hshake,sram_rlast_hshake}) inside
            2'b00:
                sram_r_active <= sram_r_active;
            2'b01:
                if (sram_r_active)
                    sram_r_active <= sram_r_active - 2'b1;
                else
                    $fatal("Read data with last, but no reads outstanding!");
            2'b10:
                sram_r_active <= sram_r_active + 2'b1;
            2'b11:
                sram_r_active <= sram_r_active;
        endcase
    end
end
`CALIPTRA_ASSERT_NEVER(SRAM_GT2_RD_PENDING, sram_r_active > 2, core_clk, !cptra_rst_b)
always_comb begin
    sram_aw_hshake    = axi_sram_if.awvalid && axi_sram_if.awready;
    sram_b_hshake     = axi_sram_if.bvalid  && axi_sram_if.bready;
end
always_ff@(posedge core_clk or negedge cptra_rst_b) begin
    if (!cptra_rst_b) begin
        sram_w_active <= 2'b0;;
    end
    else begin
        case ({sram_aw_hshake,sram_b_hshake}) inside
            2'b00:
                sram_w_active <= sram_w_active;
            2'b01:
                if (sram_w_active)
                    sram_w_active <= sram_w_active - 2'b1;
                else
                    $fatal("Write response, but no writes outstanding!");
            2'b10:
                sram_w_active <= sram_w_active + 2'b1;
            2'b11:
                sram_w_active <= sram_w_active;
        endcase
    end
end
`CALIPTRA_ASSERT_NEVER(SRAM_GT2_WR_PENDING, sram_w_active > 2, core_clk, !cptra_rst_b)
always_comb begin
    // AXI AR
    axi_sram_if.arvalid       = m_axi_if.arvalid && m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH];
    axi_sram_if.araddr        = m_axi_if.araddr[AXI_SRAM_ADDR_WIDTH-1:0];
    axi_sram_if.arburst       = m_axi_if.arburst;
    axi_sram_if.arsize        = m_axi_if.arsize ;
    axi_sram_if.arlen         = m_axi_if.arlen  ;
    axi_sram_if.aruser        = m_axi_if.aruser ;
    axi_sram_if.arid          = m_axi_if.arid   ;
    axi_sram_if.arlock        = m_axi_if.arlock ;
                                                
    // AXI R                                    
    axi_sram_if.rready        = sram_r_active ? m_axi_if.rready : '0;
                                                
    // AXI AW                                   
    axi_sram_if.awvalid       = m_axi_if.awvalid && m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH];
    axi_sram_if.awaddr        = m_axi_if.awaddr[AXI_SRAM_ADDR_WIDTH-1:0];
    axi_sram_if.awburst       = m_axi_if.awburst;
    axi_sram_if.awsize        = m_axi_if.awsize ;
    axi_sram_if.awlen         = m_axi_if.awlen  ;
    axi_sram_if.awuser        = m_axi_if.awuser ;
    axi_sram_if.awid          = m_axi_if.awid   ;
    axi_sram_if.awlock        = m_axi_if.awlock ;
                                                
    // AXI W                                    
    axi_sram_if.wvalid        = sram_w_active ? m_axi_if.wvalid : '0;
    axi_sram_if.wdata         = sram_w_active ? m_axi_if.wdata  : '0;
    axi_sram_if.wstrb         = sram_w_active ? m_axi_if.wstrb  : '0;
    axi_sram_if.wuser         = sram_w_active ? m_axi_if.wuser  : '0;
    axi_sram_if.wlast         = sram_w_active ? m_axi_if.wlast  : '0;
    axi_sram_if.wuser         = sram_w_active ? m_axi_if.wuser  : '0;

    // AXI B
    axi_sram_if.bready        = sram_w_active ? m_axi_if.bready : '0;
end

// Fake "MCU" SRAM block
caliptra_axi_sram #(
    .AW   (AXI_SRAM_ADDR_WIDTH     ),
    .DW   (CPTRA_AXI_DMA_DATA_WIDTH),
    .UW   (CPTRA_AXI_DMA_USER_WIDTH),
    .IW   (CPTRA_AXI_DMA_ID_WIDTH  ),
    .EX_EN(0                       )
) i_axi_sram (
    .clk(core_clk),
    .rst_n(cptra_rst_b),

    // AXI INF
    .s_axi_w_if(axi_sram_if.w_sub),
    .s_axi_r_if(axi_sram_if.r_sub)
);
`ifdef VERILATOR
initial i_axi_sram.i_sram.ram = '{default:'{default:8'h00}};
`else
initial i_axi_sram.i_sram.ram = '{default:8'h00};
`endif

// --------------------- FIFO Endpoint ---------------------
always_comb begin
    fifo_ar_hshake    = axi_fifo_if.arvalid && axi_fifo_if.arready;
    fifo_rlast_hshake = axi_fifo_if.rvalid  && axi_fifo_if.rready && axi_fifo_if.rlast;
end
always_ff@(posedge core_clk or negedge cptra_rst_b) begin
    if (!cptra_rst_b) begin
        fifo_r_active <= 2'b0;;
    end
    else begin
        case ({fifo_ar_hshake,fifo_rlast_hshake}) inside
            2'b00:
                fifo_r_active <= fifo_r_active;
            2'b01:
                if (fifo_r_active)
                    fifo_r_active <= fifo_r_active - 2'b1;
                else
                    $fatal("Read data with last, but no reads outstanding!");
            2'b10:
                fifo_r_active <= fifo_r_active + 2'b1;
            2'b11:
                fifo_r_active <= fifo_r_active;
        endcase
    end
end
`CALIPTRA_ASSERT_NEVER(FIFO_GT2_RD_PENDING, fifo_r_active > 2, core_clk, !cptra_rst_b)
always_comb begin
    fifo_aw_hshake    = axi_fifo_if.awvalid && axi_fifo_if.awready;
    fifo_b_hshake     = axi_fifo_if.bvalid  && axi_fifo_if.bready;
end
always_ff@(posedge core_clk or negedge cptra_rst_b) begin
    if (!cptra_rst_b) begin
        fifo_w_active <= 2'b0;;
    end
    else begin
        case ({fifo_aw_hshake,fifo_b_hshake}) inside
            2'b00:
                fifo_w_active <= fifo_w_active;
            2'b01:
                if (fifo_w_active)
                    fifo_w_active <= fifo_w_active - 2'b1;
                else
                    $fatal("Write response, but no writes outstanding!");
            2'b10:
                fifo_w_active <= fifo_w_active + 2'b1;
            2'b11:
                fifo_w_active <= fifo_w_active;
        endcase
    end
end
`CALIPTRA_ASSERT_NEVER(FIFO_GT2_WR_PENDING, fifo_w_active > 2, core_clk, !cptra_rst_b)
always_comb begin
    // AXI AR
    axi_fifo_if.arvalid       = m_axi_if.arvalid && m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH];
    axi_fifo_if.araddr        = m_axi_if.araddr[AXI_FIFO_ADDR_WIDTH-1:0];
    axi_fifo_if.arburst       = m_axi_if.arburst;
    axi_fifo_if.arsize        = m_axi_if.arsize ;
    axi_fifo_if.arlen         = m_axi_if.arlen  ;
    axi_fifo_if.aruser        = m_axi_if.aruser ;
    axi_fifo_if.arid          = m_axi_if.arid   ;
    axi_fifo_if.arlock        = m_axi_if.arlock ;
                                                
    // AXI R                                    
    axi_fifo_if.rready        = fifo_r_active ? m_axi_if.rready : '0;
                                                
    // AXI AW                                   
    axi_fifo_if.awvalid       = m_axi_if.awvalid && m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH];
    axi_fifo_if.awaddr        = m_axi_if.awaddr[AXI_FIFO_ADDR_WIDTH-1:0];
    axi_fifo_if.awburst       = m_axi_if.awburst;
    axi_fifo_if.awsize        = m_axi_if.awsize ;
    axi_fifo_if.awlen         = m_axi_if.awlen  ;
    axi_fifo_if.awuser        = m_axi_if.awuser ;
    axi_fifo_if.awid          = m_axi_if.awid   ;
    axi_fifo_if.awlock        = m_axi_if.awlock ;
                                                
    // AXI W                                    
    axi_fifo_if.wvalid        = fifo_w_active ? m_axi_if.wvalid : '0;
    axi_fifo_if.wdata         = fifo_w_active ? m_axi_if.wdata  : '0;
    axi_fifo_if.wstrb         = fifo_w_active ? m_axi_if.wstrb  : '0;
    axi_fifo_if.wuser         = fifo_w_active ? m_axi_if.wuser  : '0;
    axi_fifo_if.wlast         = fifo_w_active ? m_axi_if.wlast  : '0;
    axi_fifo_if.wuser         = fifo_w_active ? m_axi_if.wuser  : '0;
                                                
    // AXI B                                    
    axi_fifo_if.bready        = fifo_w_active ? m_axi_if.bready : '0;
end
`CALIPTRA_ASSERT_NEVER(FIFO_RD_NOT_FIXED, fifo_ar_hshake && (axi_fifo_if.arburst != AXI_BURST_FIXED), core_clk, !cptra_rst_b)
`CALIPTRA_ASSERT_NEVER(FIFO_WR_NOT_FIXED, fifo_aw_hshake && (axi_fifo_if.awburst != AXI_BURST_FIXED), core_clk, !cptra_rst_b)

caliptra_top_tb_axi_fifo #(
    .AW(AXI_FIFO_ADDR_WIDTH     ),
    .DW(CPTRA_AXI_DMA_DATA_WIDTH),
    .UW(CPTRA_AXI_DMA_USER_WIDTH),         // User Width
    .IW(CPTRA_AXI_DMA_ID_WIDTH  ),         // ID Width
    .DEPTH(AXI_FIFO_SIZE_BYTES  )
) i_axi_fifo (
    .clk  (core_clk   ),
    .rst_n(cptra_rst_b),

    // AXI INF
    .s_axi_w_if(axi_fifo_if.w_sub),
    .s_axi_r_if(axi_fifo_if.r_sub)
);

// --------------------- REG Endpoint ---------------------

`CALIPTRA_ASSERT_MUTEX(DMA_NO_SIMULT_RD, {|sram_r_active,|fifo_r_active/*TODO*/}, core_clk, !cptra_rst_b)
`CALIPTRA_ASSERT_MUTEX(DMA_NO_SIMULT_WR, {|sram_w_active,|fifo_w_active/*TODO*/}, core_clk, !cptra_rst_b)

//=========================================================================-
// Dummy interconnect
//=========================================================================-
caliptra_top_sva sva();

endmodule
