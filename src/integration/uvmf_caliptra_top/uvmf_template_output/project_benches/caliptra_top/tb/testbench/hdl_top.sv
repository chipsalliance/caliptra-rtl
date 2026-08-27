//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------                     
//               
// Description: This top level module instantiates all synthesizable
//    static content.  This and tb_top.sv are the two top level modules
//    of the simulation.  
//
//    This module instantiates the following:
//        DUT: The Design Under Test
//        Interfaces:  Signal bundles that contain signals connected to DUT
//        Driver BFM's: BFM's that actively drive interface signals
//        Monitor BFM's: BFM's that passively monitor interface signals
//
//----------------------------------------------------------------------

//----------------------------------------------------------------------
//

module hdl_top;

import caliptra_top_parameters_pkg::*;
import soc_ifc_axi_topology_pkg::*;
import qvip_ahb_lite_slave_params_pkg::*;
//import qvip_apb5_slave_params_pkg::*;
import uvmf_base_pkg_hdl::*;
`include "avery_defines.svh"
import aaxi_pkg::*;
import aaxi_pkg_xactor::*;
import aaxi_pkg_test::*;
import aaxi_pll::*;

import uvm_pkg::*;
`include "uvm_macros.svh"
import aaxi_uvm_pkg::*;
`include "config_defines.svh"

  // pragma attribute hdl_top partition_module_xrtl                                            
  hdl_qvip_ahb_lite_slave 
      #(
        .AHB_LITE_SLAVE_0_ACTIVE(0),
        .UNIQUE_ID("uvm_test_top.environment.soc_ifc_subenv.qvip_ahb_lite_slave_subenv."),
        .EXT_CLK_RESET(1)
       ) uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl();

//  hdl_qvip_apb5_slave 
//      #(
//        .APB5_MASTER_0_ACTIVE(1),
//        .UNIQUE_ID("uvm_test_top.environment.soc_ifc_subenv.qvip_apb5_slave_subenv."),
//        .EXT_CLK_RESET(1)
//       ) uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl();

// pragma uvmf custom clock_generator begin
  bit clk;
  // Instantiate a clk driver 
  // tbx clkgen
  initial begin
//    clk = 0;
//    #0ns;
//    forever begin
//      clk = ~clk;
//      #5ns;
//    end
    clk = 0;
    forever begin
      #5ns;
      clk = ~clk;
    end
  end
// pragma uvmf custom clock_generator end

// pragma uvmf custom reset_generator begin
  bit dummy, dummy_n;
    default_reset_gen default_reset_gen
    (
        .RESET(dummy),
        .CLK_IN(clk)
    );
    always_comb dummy_n = ~dummy;
// pragma uvmf custom reset_generator end

  // pragma uvmf custom module_item_additional begin
   //=========================================================================-
   // Custom Signal Declarations
   //=========================================================================-
    import soc_ifc_pkg::*;
    import caliptra_top_tb_pkg::*;

    `include "config_defines.svh"

    // Time formatting for %t in display tasks
    // -9 = ns units
    // 3  = 3 bits of precision (to the ps)
    // "ns" = nanosecond suffix for output time values
    // 15 = 15 bits minimum field width
    initial $timeformat(-9, 3, " ns", 15); // up to 99ms representable in this width

    int                         cycleCnt;
    bit                         int_flag;
    bit                         cycleCnt_smpl_en;
    ras_test_ctrl_t             ras_test_ctrl;

    //jtag interface
    logic                       jtag_tck    = '0; // JTAG clk
    logic                       jtag_tms    = '0; // JTAG TMS
    logic                       jtag_tdi    = '0; // JTAG tdi
    logic                       jtag_trst_n = '0; // JTAG Reset
    logic                       jtag_tdo;    // JTAG TDO
    logic                       jtag_tdoEn;  // JTAG TDO enable

    cptra_mbox_sram_req_t mbox_sram_req;
    cptra_mbox_sram_resp_t mbox_sram_resp;
    logic mbox_sram_cs_stub_inactive;
    logic mbox_sram_we_stub_inactive;
    logic [CPTRA_MBOX_ADDR_W-1:0] mbox_sram_addr_stub_inactive;
    logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] mbox_sram_wdata_stub_inactive;
    logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] mbox_sram_rdata_stub_inactive;

    logic imem_cs;
    logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] imem_addr;
    logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] imem_rdata;

    logic        etrng0_req;
    logic  [3:0] itrng_data;
    logic        itrng_valid;

    //device lifecycle
    security_state_t security_state_stub_inactive;

    el2_mem_if el2_mem_export ();
    abr_mem_if abr_memory_export();

    // FIXME
    // Avery can access a null object when reset asserts in the same cycle that
    // an RVALID/RLAST response ends. Delay assertion by 1ps while allowing
    // deassertion immediately. Recheck this workaround with newer Avery VIP.
    logic cptra_rst_b_d;
    logic cptra_rst_b_dly_assert_simult_deassert;
    initial cptra_rst_b_d = 1'b0;
    always@(*) begin
        #1ps cptra_rst_b_d =
          soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_rst_b;
    end
    assign cptra_rst_b_dly_assert_simult_deassert =
      cptra_rst_b_d |
      soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_rst_b;

    pulldown (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_rst_b);
    pulldown (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_pwrgood);

    aaxi_intf #(
        .ID_WIDTH    (aaxi_pkg::AAXI_INTC_ID_WIDTH),
        .ADDR_WIDTH  (aaxi_pkg::AAXI_ADDR_WIDTH),
        .DATA_WIDTH  (CPTRA_AXI_DMA_DATA_WIDTH),
        .AWUSER_WIDTH(CPTRA_AXI_DMA_USER_WIDTH),
        .WUSER_WIDTH (CPTRA_AXI_DMA_USER_WIDTH),
        .BUSER_WIDTH (CPTRA_AXI_DMA_USER_WIDTH),
        .ARUSER_WIDTH(CPTRA_AXI_DMA_USER_WIDTH),
        .RUSER_WIDTH (CPTRA_AXI_DMA_USER_WIDTH)
    ) axi_manager_ports[AXI_FABRIC_NUM_MANAGERS] (
        .ACLK   (clk                                   ),
        .ARESETn(cptra_rst_b_dly_assert_simult_deassert),
        .CACTIVE(                                      ),
        .CSYSREQ(1'b0                                  ),
        .CSYSACK(                                      )
    );
    aaxi_intf #(
        .ID_WIDTH    (aaxi_pkg::AAXI_INTC_ID_WIDTH),
        .ADDR_WIDTH  (aaxi_pkg::AAXI_ADDR_WIDTH),
        .DATA_WIDTH  (CPTRA_AXI_DMA_DATA_WIDTH),
        .AWUSER_WIDTH(CPTRA_AXI_DMA_USER_WIDTH),
        .WUSER_WIDTH (CPTRA_AXI_DMA_USER_WIDTH),
        .BUSER_WIDTH (CPTRA_AXI_DMA_USER_WIDTH),
        .ARUSER_WIDTH(CPTRA_AXI_DMA_USER_WIDTH),
        .RUSER_WIDTH (CPTRA_AXI_DMA_USER_WIDTH)
    ) axi_subordinate_ports[AXI_FABRIC_NUM_SUBORDINATES] (
        .ACLK   (clk                                   ),
        .ARESETn(cptra_rst_b_dly_assert_simult_deassert),
        .CACTIVE(                                      ),
        .CSYSREQ(1'b0                                  ),
        .CSYSACK(                                      )
    );
    aaxi_interconnect_intf axi_interconnect_port (
        .ACLK   (clk                                   ),
        .ARESETn(cptra_rst_b_dly_assert_simult_deassert),
        .CACTIVE(                                      ),
        .CSYSREQ(1'b0                                  ),
        .CSYSACK(                                      )
    );
    soc_ifc_recovery_if recovery_if (
        .clk  (clk                                   ),
        .rst_n(cptra_rst_b_dly_assert_simult_deassert)
    );

   //=========================================================================-
   // END Custom Signals
   //=========================================================================-
  // pragma uvmf custom module_item_additional end

  // Instantiate the signal bundle, monitor bfm and driver bfm for each interface.
  // The signal bundle, _if, contains signals to be connected to the DUT.
  // The monitor, monitor_bfm, observes the bus, _if, and captures transactions.
  // The driver, driver_bfm, drives transactions onto the bus, _if.
  soc_ifc_ctrl_if  soc_ifc_subenv_soc_ifc_ctrl_agent_bus(
     // pragma uvmf custom soc_ifc_subenv_soc_ifc_ctrl_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom soc_ifc_subenv_soc_ifc_ctrl_agent_bus_connections end
     );
  cptra_ctrl_if  soc_ifc_subenv_cptra_ctrl_agent_bus(
     // pragma uvmf custom soc_ifc_subenv_cptra_ctrl_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom soc_ifc_subenv_cptra_ctrl_agent_bus_connections end
     );
  ss_mode_ctrl_if  soc_ifc_subenv_ss_mode_ctrl_agent_bus(
     // pragma uvmf custom soc_ifc_subenv_ss_mode_ctrl_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom soc_ifc_subenv_ss_mode_ctrl_agent_bus_connections end
     );
  soc_ifc_status_if  soc_ifc_subenv_soc_ifc_status_agent_bus(
     // pragma uvmf custom soc_ifc_subenv_soc_ifc_status_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom soc_ifc_subenv_soc_ifc_status_agent_bus_connections end
     );
  cptra_status_if  soc_ifc_subenv_cptra_status_agent_bus(
     // pragma uvmf custom soc_ifc_subenv_cptra_status_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom soc_ifc_subenv_cptra_status_agent_bus_connections end
     );
  ss_mode_status_if  soc_ifc_subenv_ss_mode_status_agent_bus(
     // pragma uvmf custom soc_ifc_subenv_ss_mode_status_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom soc_ifc_subenv_ss_mode_status_agent_bus_connections end
     );
  mbox_sram_if  soc_ifc_subenv_mbox_sram_agent_bus(
     // pragma uvmf custom soc_ifc_subenv_mbox_sram_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom soc_ifc_subenv_mbox_sram_agent_bus_connections end
     );
  soc_ifc_ctrl_monitor_bfm  soc_ifc_subenv_soc_ifc_ctrl_agent_mon_bfm(soc_ifc_subenv_soc_ifc_ctrl_agent_bus.monitor_port);
  cptra_ctrl_monitor_bfm  soc_ifc_subenv_cptra_ctrl_agent_mon_bfm(soc_ifc_subenv_cptra_ctrl_agent_bus.monitor_port);
  ss_mode_ctrl_monitor_bfm  soc_ifc_subenv_ss_mode_ctrl_agent_mon_bfm(soc_ifc_subenv_ss_mode_ctrl_agent_bus.monitor_port);
  soc_ifc_status_monitor_bfm  soc_ifc_subenv_soc_ifc_status_agent_mon_bfm(soc_ifc_subenv_soc_ifc_status_agent_bus.monitor_port);
  cptra_status_monitor_bfm  soc_ifc_subenv_cptra_status_agent_mon_bfm(soc_ifc_subenv_cptra_status_agent_bus.monitor_port);
  ss_mode_status_monitor_bfm  soc_ifc_subenv_ss_mode_status_agent_mon_bfm(soc_ifc_subenv_ss_mode_status_agent_bus.monitor_port);
  mbox_sram_monitor_bfm  soc_ifc_subenv_mbox_sram_agent_mon_bfm(soc_ifc_subenv_mbox_sram_agent_bus.monitor_port);
  soc_ifc_ctrl_driver_bfm  soc_ifc_subenv_soc_ifc_ctrl_agent_drv_bfm(soc_ifc_subenv_soc_ifc_ctrl_agent_bus.initiator_port);
  ss_mode_ctrl_driver_bfm  soc_ifc_subenv_ss_mode_ctrl_agent_drv_bfm(soc_ifc_subenv_ss_mode_ctrl_agent_bus.initiator_port);
  soc_ifc_status_driver_bfm  soc_ifc_subenv_soc_ifc_status_agent_drv_bfm(soc_ifc_subenv_soc_ifc_status_agent_bus.responder_port);
  ss_mode_status_driver_bfm  soc_ifc_subenv_ss_mode_status_agent_drv_bfm(soc_ifc_subenv_ss_mode_status_agent_bus.responder_port);
  mbox_sram_driver_bfm  soc_ifc_subenv_mbox_sram_agent_drv_bfm(soc_ifc_subenv_mbox_sram_agent_bus.responder_port);

  // pragma uvmf custom dut_instantiation begin
  // AHB Clock/reset
  assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.default_clk_gen_CLK     = clk;
  assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.default_reset_gen_RESET = caliptra_top_dut.cptra_noncore_rst_b;
//  assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.default_clk_gen_CLK         = clk;
//  assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.default_reset_gen_RESET     = caliptra_top_dut.cptra_noncore_rst_b;


    //=========================================================================-
    // DUT instance
    //=========================================================================-
    // AXI Interface
    axi_if #(
        .AW(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH                               ),
        .IW(`CALIPTRA_AXI_ID_WIDTH                                 ),
        .UW(`CALIPTRA_AXI_USER_WIDTH                               )
    ) s_axi_if (.clk(clk), .rst_n(soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_rst_b));
    axi_if #(
        .AW(`CALIPTRA_AXI_DMA_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH    ),
        .IW(CPTRA_AXI_DMA_ID_WIDTH      ),
        .UW(CPTRA_AXI_DMA_USER_WIDTH    )
    ) m_axi_if (.clk(clk), .rst_n(soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_rst_b));

    caliptra_top caliptra_top_dut (
        .cptra_pwrgood              (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_pwrgood),
        .cptra_rst_b                (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_rst_b  ),
        .clk                        (clk),

        .cptra_obf_key              (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_obf_key              ),
        .cptra_csr_hmac_key         ('0/* TODO */                                                     ),
        .cptra_obf_field_entropy_vld(soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_obf_field_entropy_vld),
        .cptra_obf_field_entropy    (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_obf_field_entropy    ),
        .cptra_obf_uds_seed_vld     (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_obf_uds_seed_vld     ),
        .cptra_obf_uds_seed         (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_obf_uds_seed         ),

        .jtag_tck   (jtag_tck   ),
        .jtag_tdi   (jtag_tdi   ),
        .jtag_tms   (jtag_tms   ),
        .jtag_trst_n(jtag_trst_n),
        .jtag_tdo   (jtag_tdo   ),
        .jtag_tdoEn (jtag_tdoEn ),
        
        //AXI Interface with SoC
        .s_axi_w_if(s_axi_if.w_sub),
        .s_axi_r_if(s_axi_if.r_sub),

        // AXI Manager INF
        .m_axi_w_if(m_axi_if.w_mgr),
        .m_axi_r_if(m_axi_if.r_mgr),

        .el2_mem_export(el2_mem_export.veer_sram_src),
        .abr_memory_export(abr_memory_export.req),

        .mbox_sram_cs   (mbox_sram_req.cs   ),
        .mbox_sram_we   (mbox_sram_req.we   ),
        .mbox_sram_addr (mbox_sram_req.addr ),
        .mbox_sram_wdata(mbox_sram_req.wdata),
        .mbox_sram_rdata(mbox_sram_resp.rdata),

        .imem_cs        (imem_cs        ),
        .imem_addr      (imem_addr      ),
        .imem_rdata     (imem_rdata     ),

        .ready_for_fuses        (soc_ifc_subenv_soc_ifc_status_agent_bus.ready_for_fuses         ),
        .ready_for_mb_processing(soc_ifc_subenv_soc_ifc_status_agent_bus.ready_for_mb_processing ),
        .ready_for_runtime      (soc_ifc_subenv_soc_ifc_status_agent_bus.ready_for_runtime       ),

        .mailbox_data_avail(soc_ifc_subenv_soc_ifc_status_agent_bus.mailbox_data_avail),
        .mailbox_flow_done (soc_ifc_subenv_soc_ifc_status_agent_bus.mailbox_flow_done ),

        .recovery_data_avail     (recovery_if.recovery_data_avail                                 ),
        .recovery_image_activated(recovery_if.recovery_image_activated                             ),

        .BootFSM_BrkPoint  (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.BootFSM_BrkPoint),

        //SoC Interrupts
        .cptra_error_fatal    (soc_ifc_subenv_soc_ifc_status_agent_bus.cptra_error_fatal),
        .cptra_error_non_fatal(soc_ifc_subenv_soc_ifc_status_agent_bus.cptra_error_non_fatal),
        // External TRNG
`ifdef CALIPTRA_INTERNAL_TRNG
        .etrng0_req            (etrng0_req),
        .etrng1_req            (), // ES1 unused in this UVM bench (dual-iTRNG combine disabled)
        // Internal TRNG
        .itrng0_data           (itrng_data ),
        .itrng0_valid          (itrng_valid),
        .itrng1_data           (4'h0),
        .itrng1_valid          (1'b0),
        .itrng1_en             (1'b0),
`else
        .etrng0_req            (soc_ifc_subenv_soc_ifc_status_agent_bus.trng_req),
        .etrng1_req            (),
        // Internal TRNG
        .itrng0_data           (4'h0),
        .itrng0_valid          (1'b0),
        .itrng1_data           (4'h0),
        .itrng1_valid          (1'b0),
        .itrng1_en             (1'b0),
`endif

        // Subsystem mode straps
        .strap_ss_caliptra_base_addr                            (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_caliptra_base_addr                            ),
        .strap_ss_mci_base_addr                                 (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_mci_base_addr                                 ),
        .strap_ss_recovery_ifc_base_addr                        (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_recovery_ifc_base_addr                        ),
        .strap_ss_external_staging_area_base_addr               (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_external_staging_area_base_addr                        ),
        .strap_ss_otp_fc_base_addr                              (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_otp_fc_base_addr                              ),
        .strap_ss_uds_seed_base_addr                            (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_uds_seed_base_addr                            ),
        .strap_ss_key_release_base_addr                         (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_key_release_base_addr                         ),
        .strap_ss_key_release_key_size                          (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_key_release_key_size                          ),
        .strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset(soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset),
        .strap_ss_num_of_prod_debug_unlock_auth_pk_hashes       (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_num_of_prod_debug_unlock_auth_pk_hashes       ),
        .strap_ss_caliptra_dma_axi_user                         (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_caliptra_dma_axi_user                         ),
        .strap_ss_strap_generic_0                               (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_strap_generic_0                               ),
        .strap_ss_strap_generic_1                               (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_strap_generic_1                               ),
        .strap_ss_strap_generic_2                               (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_strap_generic_2                               ),
        .strap_ss_strap_generic_3                               (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_strap_generic_3                               ),
        .ss_debug_intent                                        (soc_ifc_subenv_ss_mode_ctrl_agent_bus.ss_debug_intent                                        ),

        // Subsystem mode constant strap input indicating OCP LOCK configuration is enabled
        .ss_ocp_lock_en(1'b0), // TODO

        // Subsystem mode debug outputs
        .ss_dbg_manuf_enable    (soc_ifc_subenv_ss_mode_status_agent_bus.ss_dbg_manuf_enable    ),
        .ss_soc_dbg_unlock_level(soc_ifc_subenv_ss_mode_status_agent_bus.ss_soc_dbg_unlock_level),

        // Subsystem mode firmware execution control
        .ss_generic_fw_exec_ctrl(soc_ifc_subenv_ss_mode_status_agent_bus.ss_generic_fw_exec_ctrl),

        .generic_input_wires (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.generic_input_wires),
        .generic_output_wires(soc_ifc_subenv_soc_ifc_status_agent_bus.generic_output_wires),

        // RISC-V Trace Ports
        .trace_rv_i_insn_ip     (), // TODO
        .trace_rv_i_address_ip  (), // TODO
        .trace_rv_i_valid_ip    (), // TODO
        .trace_rv_i_exception_ip(), // TODO
        .trace_rv_i_ecause_ip   (), // TODO
        .trace_rv_i_interrupt_ip(), // TODO
        .trace_rv_i_tval_ip     (), // TODO

        .security_state(soc_ifc_subenv_soc_ifc_ctrl_agent_bus.security_state),
        .scan_mode     (1'b0) // TODO
    );
    assign soc_ifc_subenv_ss_mode_status_agent_bus.cptra_ss_debug_intent = caliptra_top_dut.cptra_ss_debug_intent;
    // Internal AHB monitor connections [soc_ifc slave]
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HADDR     = caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].haddr[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)-1:0];
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWDATA    = caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hwdata   ;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HSEL      = caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hsel     ;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWRITE    = caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hwrite   ;
//    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HREADYOUT = caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hreadyout;
//    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0.ahb_if.HREADYin = caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hreadyout;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HTRANS    = caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hsel ? 
                                                                                                                    caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].htrans : '0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HSIZE     = caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hsize    ;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRESP     = caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hresp    ;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HREADY    = caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hready   ;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRDATA    = caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_SOC_IFC].hrdata   ;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HBURST    = 3'b0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HPROT     = 7'b0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HMASTLOCK = 1'b0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HNONSEC   = 1'b0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HAUSER    = 64'b0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWUSER    = 64'b0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRUSER    = 64'b0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_mult_HSEL = 16'b0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HEXCL     = 1'b0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HMASTER   = 16'b0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HEXOKAY   = 1'b0;

    always_comb begin
        s_axi_if.araddr   = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].ARADDR[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)-1:0];
        s_axi_if.arburst  = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].ARBURST;
        s_axi_if.arsize   = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].ARSIZE;
        s_axi_if.arlen    = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].ARLEN;
        s_axi_if.aruser   = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].ARUSER;
        s_axi_if.arid     = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].ARID;
        s_axi_if.arlock   = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].ARLOCK;
        s_axi_if.arcache  = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].ARCACHE;
        s_axi_if.arprot   = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].ARPROT;
        s_axi_if.arqos    = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].ARQOS;
        s_axi_if.arregion = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].ARREGION;
        s_axi_if.arvalid  = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].ARVALID;
        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].ARREADY = s_axi_if.arready;

        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].RDATA  = s_axi_if.rdata;
        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].RRESP  = s_axi_if.rresp;
        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].RID    = s_axi_if.rid;
        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].RUSER  = s_axi_if.ruser;
        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].RLAST  = s_axi_if.rlast;
        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].RVALID = s_axi_if.rvalid;
        s_axi_if.rready = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].RREADY;

        s_axi_if.awaddr   = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].AWADDR[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)-1:0];
        s_axi_if.awburst  = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].AWBURST;
        s_axi_if.awsize   = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].AWSIZE;
        s_axi_if.awlen    = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].AWLEN;
        s_axi_if.awuser   = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].AWUSER;
        s_axi_if.awid     = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].AWID;
        s_axi_if.awlock   = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].AWLOCK;
        s_axi_if.awcache  = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].AWCACHE;
        s_axi_if.awprot   = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].AWPROT;
        s_axi_if.awqos    = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].AWQOS;
        s_axi_if.awregion = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].AWREGION;
        s_axi_if.awvalid  = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].AWVALID;
        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].AWREADY = s_axi_if.awready;

        s_axi_if.wdata  = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].WDATA;
        s_axi_if.wstrb  = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].WSTRB;
        s_axi_if.wuser  = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].WUSER;
        s_axi_if.wvalid = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].WVALID;
        s_axi_if.wlast  = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].WLAST;
        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].WREADY = s_axi_if.wready;

        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].BRESP  = s_axi_if.bresp;
        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].BID    = s_axi_if.bid;
        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].BUSER  = s_axi_if.buser;
        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].BVALID = s_axi_if.bvalid;
        s_axi_if.bready = axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX].BREADY;

        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].ARADDR   = m_axi_if.araddr;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].ARBURST  = m_axi_if.arburst;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].ARSIZE   = m_axi_if.arsize;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].ARLEN    = m_axi_if.arlen;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].ARUSER   = m_axi_if.aruser;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].ARID     = aaxi_pkg::AAXI_INTC_ID_WIDTH'(m_axi_if.arid);
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].ARLOCK   = m_axi_if.arlock;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].ARCACHE  = m_axi_if.arcache;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].ARPROT   = m_axi_if.arprot;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].ARQOS    = m_axi_if.arqos;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].ARREGION = m_axi_if.arregion;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].ARVALID  = m_axi_if.arvalid;
        m_axi_if.arready = axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].ARREADY;

        m_axi_if.rdata  = axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].RDATA;
        m_axi_if.rresp  = axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].RRESP;
        m_axi_if.rid    = CPTRA_AXI_DMA_ID_WIDTH'(axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].RID);
        m_axi_if.ruser  = axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].RUSER;
        m_axi_if.rlast  = axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].RLAST;
        m_axi_if.rvalid = axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].RVALID;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].RREADY = m_axi_if.rready;

        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].AWADDR   = m_axi_if.awaddr;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].AWBURST  = m_axi_if.awburst;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].AWSIZE   = m_axi_if.awsize;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].AWLEN    = m_axi_if.awlen;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].AWUSER   = m_axi_if.awuser;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].AWID     = aaxi_pkg::AAXI_INTC_ID_WIDTH'(m_axi_if.awid);
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].AWLOCK   = m_axi_if.awlock;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].AWCACHE  = m_axi_if.awcache;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].AWPROT   = m_axi_if.awprot;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].AWQOS    = m_axi_if.awqos;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].AWREGION = m_axi_if.awregion;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].AWVALID  = m_axi_if.awvalid;
        m_axi_if.awready = axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].AWREADY;

        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].WDATA  = m_axi_if.wdata;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].WSTRB  = m_axi_if.wstrb;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].WUSER  = m_axi_if.wuser;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].WVALID = m_axi_if.wvalid;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].WLAST  = m_axi_if.wlast;
        m_axi_if.wready = axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].WREADY;

        m_axi_if.bresp  = axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].BRESP;
        m_axi_if.bid    = CPTRA_AXI_DMA_ID_WIDTH'(axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].BID);
        m_axi_if.buser  = axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].BUSER;
        m_axi_if.bvalid = axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].BVALID;
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX].BREADY = m_axi_if.bready;
    end

    assign soc_ifc_subenv_cptra_status_agent_bus.cptra_noncore_rst_b = caliptra_top_dut.cptra_noncore_rst_b;
    assign soc_ifc_subenv_cptra_status_agent_bus.cptra_obf_key_reg = caliptra_top_dut.cptra_obf_key_reg;
    assign soc_ifc_subenv_cptra_status_agent_bus.cptra_uc_rst_b = caliptra_top_dut.cptra_uc_rst_b;
    assign soc_ifc_subenv_cptra_status_agent_bus.fw_update_rst_window = caliptra_top_dut.fw_update_rst_window;
    assign soc_ifc_subenv_cptra_status_agent_bus.iccm_lock = caliptra_top_dut.iccm_lock;
    assign soc_ifc_subenv_cptra_status_agent_bus.nmi_vector = caliptra_top_dut.nmi_vector;
    assign soc_ifc_subenv_cptra_status_agent_bus.nmi_intr = caliptra_top_dut.nmi_int;
    assign soc_ifc_subenv_cptra_status_agent_bus.obf_field_entropy = caliptra_top_dut.obf_field_entropy;
    assign soc_ifc_subenv_cptra_status_agent_bus.obf_uds_seed = caliptra_top_dut.obf_uds_seed;
    assign soc_ifc_subenv_cptra_status_agent_bus.obf_hek_seed = caliptra_top_dut.obf_hek_seed;
    assign soc_ifc_subenv_cptra_status_agent_bus.sha_error_intr = caliptra_top_dut.sha_error_intr;
    assign soc_ifc_subenv_cptra_status_agent_bus.sha_notif_intr = caliptra_top_dut.sha_notif_intr;
    assign soc_ifc_subenv_cptra_status_agent_bus.soc_ifc_error_intr = caliptra_top_dut.soc_ifc_error_intr;
    assign soc_ifc_subenv_cptra_status_agent_bus.soc_ifc_notif_intr = caliptra_top_dut.soc_ifc_notif_intr;
    assign soc_ifc_subenv_cptra_status_agent_bus.timer_intr = caliptra_top_dut.timer_int;

    assign soc_ifc_subenv_cptra_ctrl_agent_bus.clear_obf_secrets = caliptra_top_dut.clear_obf_secrets_debugScanQ;
    assign soc_ifc_subenv_cptra_ctrl_agent_bus.iccm_axs_blocked = caliptra_top_dut.ahb_lite_resp_access_blocked[`CALIPTRA_SLAVE_SEL_IDMA];
    assign soc_ifc_subenv_cptra_ctrl_agent_bus.rv_ecc_sts = caliptra_top_dut.rv_ecc_sts;

    assign soc_ifc_subenv_mbox_sram_agent_bus.mbox_sram_req = mbox_sram_req;
    assign mbox_sram_resp = soc_ifc_subenv_mbox_sram_agent_bus.mbox_sram_resp;

`ifdef CALIPTRA_INTERNAL_TRNG
    //=========================================================================-
    // Physical RNG used for Internal TRNG
    //=========================================================================-
    physical_rng physical_rng_i (
        .clk    (clk),
        .enable (etrng0_req),
        .data   (itrng_data),
        .valid  (itrng_valid)
    );

    assign soc_ifc_subenv_soc_ifc_status_agent_bus.trng_req = 1'b0;
`endif

    //=========================================================================-
    // Services for SRAM exports, STDOUT, etc
    //=========================================================================-
    caliptra_top_tb_services #(
        .UVM_TB(1)
    ) tb_services_i (
        .clk(clk),

        .cptra_rst_b(soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_rst_b  ),

        // Caliptra Memory Export Interface
        .el2_mem_export (el2_mem_export.veer_sram_sink),
        .abr_memory_export (abr_memory_export.resp),

        //SRAM interface for mbox
        .mbox_sram_cs   (mbox_sram_cs_stub_inactive   ),
        .mbox_sram_we   (mbox_sram_we_stub_inactive   ),
        .mbox_sram_addr (mbox_sram_addr_stub_inactive ),
        .mbox_sram_wdata(mbox_sram_wdata_stub_inactive),
        .mbox_sram_rdata(mbox_sram_rdata_stub_inactive),

        //SRAM interface for imem
        .imem_cs   (imem_cs   ),
        .imem_addr (imem_addr ),
        .imem_rdata(imem_rdata),

        // Security State
        .security_state(security_state_stub_inactive),

        // TB Controls
        .ras_test_ctrl(ras_test_ctrl),
        .cycleCnt(cycleCnt),
        .cycleCnt_smpl_en(cycleCnt_smpl_en),

        //Interrupt flags
        .int_flag(int_flag)
    );

  caliptra_top_sva sva();
  kv_boot_flow_sva kv_boot_flow_sva();
  // pragma uvmf custom dut_instantiation end

  initial begin      // tbx vif_binding_block 
    import uvm_pkg::uvm_config_db;
    // The monitor_bfm and driver_bfm for each interface is placed into the uvm_config_db.
    // They are placed into the uvm_config_db using the string names defined in the parameters package.
    // The string names are passed to the agent configurations by test_top through the top level configuration.
    // They are retrieved by the agents configuration class for use by the agent.
    uvm_config_db #( virtual soc_ifc_ctrl_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_soc_ifc_ctrl_agent_BFM , soc_ifc_subenv_soc_ifc_ctrl_agent_mon_bfm ); 
    uvm_config_db #( virtual cptra_ctrl_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_cptra_ctrl_agent_BFM , soc_ifc_subenv_cptra_ctrl_agent_mon_bfm ); 
    uvm_config_db #( virtual ss_mode_ctrl_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_ss_mode_ctrl_agent_BFM , soc_ifc_subenv_ss_mode_ctrl_agent_mon_bfm ); 
    uvm_config_db #( virtual soc_ifc_status_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_soc_ifc_status_agent_BFM , soc_ifc_subenv_soc_ifc_status_agent_mon_bfm ); 
    uvm_config_db #( virtual cptra_status_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_cptra_status_agent_BFM , soc_ifc_subenv_cptra_status_agent_mon_bfm ); 
    uvm_config_db #( virtual ss_mode_status_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_ss_mode_status_agent_BFM , soc_ifc_subenv_ss_mode_status_agent_mon_bfm ); 
    uvm_config_db #( virtual mbox_sram_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_mbox_sram_agent_BFM , soc_ifc_subenv_mbox_sram_agent_mon_bfm ); 
    uvm_config_db #( virtual soc_ifc_ctrl_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_soc_ifc_ctrl_agent_BFM , soc_ifc_subenv_soc_ifc_ctrl_agent_drv_bfm  );
    uvm_config_db #( virtual ss_mode_ctrl_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_ss_mode_ctrl_agent_BFM , soc_ifc_subenv_ss_mode_ctrl_agent_drv_bfm  );
    uvm_config_db #( virtual soc_ifc_status_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_soc_ifc_status_agent_BFM , soc_ifc_subenv_soc_ifc_status_agent_drv_bfm  );
    uvm_config_db #( virtual ss_mode_status_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_ss_mode_status_agent_BFM , soc_ifc_subenv_ss_mode_status_agent_drv_bfm  );
    uvm_config_db #( virtual mbox_sram_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_mbox_sram_agent_BFM , soc_ifc_subenv_mbox_sram_agent_drv_bfm ); 
    uvm_config_db #(virtual soc_ifc_recovery_if)::set(
        null, UVMF_VIRTUAL_INTERFACES,
        soc_ifc_env_pkg::SOC_IFC_RECOVERY_VIF, recovery_if);
    uvm_config_db #(virtual aaxi_intf)::set(
        null, "*", AXI_FABRIC_SOC_MANAGER_VIF,
        axi_manager_ports[AXI_FABRIC_SOC_MANAGER_IDX]);
    uvm_config_db #(virtual aaxi_intf)::set(
        null, "*", AXI_FABRIC_DMA_MANAGER_VIF,
        axi_manager_ports[AXI_FABRIC_DMA_MANAGER_IDX]);
    uvm_config_db #(virtual aaxi_intf)::set(
        null, "*", AXI_FABRIC_CALIPTRA_SUBORDINATE_VIF,
        axi_subordinate_ports[AXI_FABRIC_CALIPTRA_SUBORDINATE_IDX]);
    uvm_config_db #(virtual aaxi_intf)::set(
        null, "*", AXI_FABRIC_SRAM_SUBORDINATE_VIF,
        axi_subordinate_ports[AXI_FABRIC_SRAM_SUBORDINATE_IDX]);
    uvm_config_db #(virtual aaxi_intf)::set(
        null, "*", AXI_FABRIC_RECOVERY_SUBORDINATE_VIF,
        axi_subordinate_ports[AXI_FABRIC_RECOVERY_SUBORDINATE_IDX]);
    uvm_config_db #(virtual aaxi_interconnect_intf)::set(
        null, "*", AXI_FABRIC_INTERCONNECT_VIF, axi_interconnect_port);
  end

endmodule

// pragma uvmf custom external begin
// pragma uvmf custom external end
