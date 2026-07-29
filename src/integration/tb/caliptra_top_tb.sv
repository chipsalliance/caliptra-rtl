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
    import kv_defines_pkg::*;
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


    logic [15:0] strap_ss_key_release_key_size;
    logic [63:0] strap_ss_key_release_base_addr;

    logic                       cptra_pwrgood;
    logic                       cptra_rst_b;
    logic                       BootFSM_BrkPoint;
    logic                       scan_mode;

    logic                       recovery_data_avail;

    logic [`CLP_OBF_KEY_DWORDS-1:0][31:0]          cptra_obf_key;
    
    logic [`CLP_CSR_HMAC_KEY_DWORDS-1:0][31:0]     cptra_csr_hmac_key;

    logic [0:`CLP_OBF_UDS_DWORDS-1][31:0]          cptra_uds_rand;
    logic [0:`CLP_OBF_FE_DWORDS-1][31:0]           cptra_fe_rand;
    logic [0:OCP_LOCK_HEK_NUM_DWORDS-1][31:0]      cptra_hek_rand;
    logic [0:`CLP_OBF_KEY_DWORDS-1][31:0]          cptra_obf_key_tb;

    //jtag interface
    logic                       jtag_tck;    // JTAG clk
    logic                       jtag_tms;    // JTAG TMS
    logic                       jtag_tdi;    // JTAG tdi
    logic                       jtag_trst_n; // JTAG Reset
    logic                       jtag_tdo;    // JTAG TDO
    logic                       jtag_tdoEn;  // JTAG TDO enable

    logic                       axi_error_inj_en;

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

    logic ss_ocp_lock_en;

    logic [31:0] strap_ss_strap_generic_0;
    logic [31:0] strap_ss_strap_generic_1;
    logic [31:0] strap_ss_strap_generic_2;
    logic [31:0] strap_ss_strap_generic_3;

    ras_test_ctrl_t ras_test_ctrl;
    axi_complex_ctrl_t axi_complex_ctrl;
    logic [63:0] generic_input_wires;
    logic        etrng0_req;
    logic        etrng1_req;
    logic  [3:0] itrng_data;
    logic        itrng_valid;
    logic        itrng1_en;
    logic        second_RNG_triggered;
    logic  [3:0] itrng_data1;
    logic        itrng_valid1;

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
    abr_mem_if abr_memory_export();

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

    .strap_ss_key_release_key_size,
    .strap_ss_key_release_base_addr,
    .ss_ocp_lock_en,
    .itrng1_en,
    .etrng1_req, // ES1 entropy request observed by the BFM to time second_RNG_triggered
    .second_RNG_triggered, // To control when the second RNG triggers, for testing the combiner. The first RNG is always triggered by the DUT.
    .strap_ss_strap_generic_0,
    .strap_ss_strap_generic_1,
    .strap_ss_strap_generic_2,
    .strap_ss_strap_generic_3,

    .cptra_uds_rand  (cptra_uds_rand  ),
    .cptra_fe_rand   (cptra_fe_rand   ),
    .cptra_hek_rand  (cptra_hek_rand  ),
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
    .ListenPort     (0)
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
    .cptra_obf_uds_seed_vld     ('0), //validated at caliptra-ss
    .cptra_obf_uds_seed         ('0), //validated at caliptra-ss
    .cptra_obf_field_entropy_vld('0), //validated at caliptra-ss
    .cptra_obf_field_entropy    ('0), //validated at caliptra-ss
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
    .abr_memory_export(abr_memory_export.req),
    
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

    .recovery_data_avail(recovery_data_avail),
    .recovery_image_activated(1'b0),

    //SoC Interrupts
    .cptra_error_fatal    (cptra_error_fatal    ),
    .cptra_error_non_fatal(cptra_error_non_fatal),

`ifdef CALIPTRA_INTERNAL_TRNG
    .etrng0_req            (etrng0_req),
    .etrng1_req            (etrng1_req),
    .itrng0_data           (itrng_data),
    .itrng0_valid          (itrng_valid),
    .itrng1_data           (itrng_data1),
    .itrng1_valid          (itrng_valid1),
    .itrng1_en             (itrng1_en),
`else
    .etrng0_req            (),
    .etrng1_req            (),
    .itrng0_data           (4'b0),
    .itrng0_valid          (1'b0),
    .itrng1_en             (1'b0),
    .itrng1_data           (4'b0),
    .itrng1_valid          (1'b0),
`endif

    // Subsystem mode straps, tested in subsystem bench
    .strap_ss_caliptra_base_addr                            (64'hba5e_ba11),
    .strap_ss_mci_base_addr                                 (64'h0),
    .strap_ss_recovery_ifc_base_addr                        (64'h0),
    .strap_ss_external_staging_area_base_addr               (64'h0),
    .strap_ss_otp_fc_base_addr                              (64'h0),
    .strap_ss_uds_seed_base_addr                            (64'h0),
    .strap_ss_key_release_base_addr                         ,
    .strap_ss_key_release_key_size                          ,
    .strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset(32'h0),
    .strap_ss_num_of_prod_debug_unlock_auth_pk_hashes       (32'h0),
    .strap_ss_caliptra_dma_axi_user                         (32'h0),
    .strap_ss_strap_generic_0                               (strap_ss_strap_generic_0),
    .strap_ss_strap_generic_1                               (strap_ss_strap_generic_1),
    .strap_ss_strap_generic_2                               (strap_ss_strap_generic_2),
    .strap_ss_strap_generic_3                               (strap_ss_strap_generic_3),
    .ss_debug_intent                                        ( 1'b0),

    // Subsystem mode constant strap input indicating OCP LOCK configuration is enabled
    .ss_ocp_lock_en                                         (ss_ocp_lock_en),

    // Subsystem mode debug outputs
    .ss_dbg_manuf_enable    (),
    .ss_soc_dbg_unlock_level(),

    // Subsystem mode firmware execution control
    .ss_generic_fw_exec_ctrl(),

    .generic_input_wires (generic_input_wires ),
    .generic_output_wires(                    ),

    // RISC-V Trace Ports
    .trace_rv_i_insn_ip     (),
    .trace_rv_i_address_ip  (),
    .trace_rv_i_valid_ip    (),
    .trace_rv_i_exception_ip(),
    .trace_rv_i_ecause_ip   (),
    .trace_rv_i_interrupt_ip(),
    .trace_rv_i_tval_ip     (),

    .security_state(security_state),
    .scan_mode     (scan_mode)
);


`ifdef CALIPTRA_INTERNAL_TRNG
    //=========================================================================-
    // Physical RNG used for Internal TRNG
    //
    // Two RNG models are instantiated per source and MUXed by det_rng_sel:
    //   - physical_rng               : default model (InitialSeed then $urandom)
    //   - physical_rng_deterministic : fully deterministic LFSR stream, for
    //                                  reproducible conditioned / multi-seed tests
    // det_rng_sel is set by the +CLP_DETERMINISTIC_RNG plusarg, so the choice is
    // per-test. Without the plusarg the default model is selected and existing
    // tests are unaffected.
    //=========================================================================-
    logic       det_rng_sel;
    logic [3:0] itrng0_rand_data,  itrng0_det_data;
    logic       itrng0_rand_valid, itrng0_det_valid;
    logic [3:0] itrng1_rand_data,  itrng1_det_data;
    logic       itrng1_rand_valid, itrng1_det_valid;

    initial det_rng_sel = $test$plusargs("CLP_DETERMINISTIC_RNG") ? 1'b1 : 1'b0;

    // ---- Source 0 ----
    physical_rng physical_rng (
        .clk    (core_clk),
        .enable (etrng0_req),
        .data   (itrng0_rand_data),
        .valid  (itrng0_rand_valid)
    );
    physical_rng_deterministic #(
        .LfsrSeed(32'hDEADBEEF)
    ) physical_rng_det (
        .clk    (core_clk),
        .enable (etrng0_req),
        .data   (itrng0_det_data),
        .valid  (itrng0_det_valid)
    );
    assign itrng_data  = det_rng_sel ? itrng0_det_data  : itrng0_rand_data;
    assign itrng_valid = det_rng_sel ? itrng0_det_valid : itrng0_rand_valid;

    // ---- Source 1 ----
    // Secondary iTRNG source uses a distinct seed so the two entropy_src blocks
    // feed different 384-bit seeds into the entropy_combiner (combined seed is
    // SHA3-384(IS0 || IS1), not SHA3-384(IS0 || IS0)). The default-model IS1
    // matches the isolated entropy_combiner_es_csrng_tb golden vectors; the
    // deterministic model uses a distinct LFSR seed for the same reason.
    physical_rng #(
        .InitialSeed(384'h9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e9587f9e1a34b2d0c7658493a1fbe6d2c0a)
    ) physical_rng1 (
        .clk    (core_clk),
        .enable (etrng1_req & second_RNG_triggered),
        .data   (itrng1_rand_data),
        .valid  (itrng1_rand_valid)
    );
    physical_rng_deterministic #(
        .LfsrSeed(32'h12345678)
    ) physical_rng1_det (
        .clk    (core_clk),
        .enable (etrng1_req & second_RNG_triggered),
        .data   (itrng1_det_data),
        .valid  (itrng1_det_valid)
    );
    assign itrng_data1  = det_rng_sel ? itrng1_det_data  : itrng1_rand_data;
    assign itrng_valid1 = det_rng_sel ? itrng1_det_valid : itrng1_rand_valid;
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
    .abr_memory_export (abr_memory_export.resp),

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
    .axi_complex_ctrl(axi_complex_ctrl),

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
    .cptra_obf_key_tb(cptra_obf_key_tb),
    .cptra_hek_tb(cptra_hek_rand),

    .axi_error_inj_en(axi_error_inj_en)

);

caliptra_top_tb_axi_complex tb_axi_complex_i (
    .core_clk           (core_clk           ),
    .cptra_rst_b        (cptra_rst_b        ),
    .m_axi_if           (m_axi_if           ),
    .recovery_data_avail(recovery_data_avail),
    .ctrl               (axi_complex_ctrl   ),
    .axi_error_inj_en   (axi_error_inj_en)
);

//=========================================================================-
// SVA
//=========================================================================-
caliptra_top_sva sva();
kv_boot_flow_sva kv_boot_flow_sva();

endmodule
