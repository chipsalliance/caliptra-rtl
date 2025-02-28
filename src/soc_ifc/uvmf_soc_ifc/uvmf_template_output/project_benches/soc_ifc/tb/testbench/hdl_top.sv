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

import soc_ifc_parameters_pkg::*;
import qvip_ahb_lite_slave_params_pkg::*;
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
        .AHB_LITE_SLAVE_0_ACTIVE(1),
        .UNIQUE_ID("uvm_test_top.environment.qvip_ahb_lite_slave_subenv."),
        .EXT_CLK_RESET(1)
       ) uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl();

// pragma uvmf custom clock_generator begin
  bit clk;
  // Instantiate a clk driver 
  // tbx clkgen
  initial begin
    clk = 0;
    #0ns;
    forever begin
      clk = ~clk;
      #5ns;
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
  //uc
  aaxi_uvm_container  uc;             //VAR: UVM container

  // FIXME
  // This reset timing hack is necessary to work around a race condition bug
  // in Avery VIP that results in Null Object Access error when reset asserts
  // on the same clock cycle that a Read request is ending (RVALID == 1, RLAST == 1)
  // Applied when using Avery 2024.3. Might be able to remove it by 2025.1+
  logic cptra_rst_b_d;
  logic cptra_rst_b_dly_assert_simult_deassert;
  initial cptra_rst_b_d = 1'b0;
  always@(*) begin
      #1ps cptra_rst_b_d = soc_ifc_ctrl_agent_bus.cptra_rst_b;
  end
  assign cptra_rst_b_dly_assert_simult_deassert = cptra_rst_b_d | soc_ifc_ctrl_agent_bus.cptra_rst_b;

  aaxi_intf #(
      .MCB_INPUT (aaxi_pkg::AAXI_MCB_INPUT ),
      .MCB_OUTPUT(aaxi_pkg::AAXI_MCB_OUTPUT),
      .SCB_INPUT (aaxi_pkg::AAXI_SCB_INPUT ),
      .SCB_OUTPUT(aaxi_pkg::AAXI_SCB_OUTPUT)
  ) ports[1] (
      .ACLK   (clk                                   ),
      .ARESETn(cptra_rst_b_dly_assert_simult_deassert),
      .CACTIVE(                                      ),
      .CSYSREQ(1'b0                                  ),
      .CSYSACK(                                      )
  );
  aaxi_monitor_wrapper monitor0 (ports[0]);
  defparam monitor0.ID_WIDTH= AAXI_ID_WIDTH;
  defparam monitor0.BUS_DATA_WIDTH=aaxi_pkg::AAXI_DATA_WIDTH;
  // enable the support of all user-defined signaling
  defparam monitor0.USER_SUPPORT= 5'b11111;
  defparam monitor0.VER= "AXI4";
  defparam monitor0.checker0.MAXWAITS = 'd100;

  initial begin
    uc = new();
    uvm_config_db #(aaxi_uvm_container)::set(uvm_root::get(), "*", "intf_uc", uc);

    uc.ports = ports[0];
    //uvm_config_db #(virtual aaxi_intf)::set(uvm_root::get(), "intf_uc", "ports", ports[0]);
  end
  // pragma uvmf custom module_item_additional end

  // Instantiate the signal bundle, monitor bfm and driver bfm for each interface.
  // The signal bundle, _if, contains signals to be connected to the DUT.
  // The monitor, monitor_bfm, observes the bus, _if, and captures transactions.
  // The driver, driver_bfm, drives transactions onto the bus, _if.
  soc_ifc_ctrl_if  soc_ifc_ctrl_agent_bus(
     // pragma uvmf custom soc_ifc_ctrl_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom soc_ifc_ctrl_agent_bus_connections end
     );
  cptra_ctrl_if  cptra_ctrl_agent_bus(
     // pragma uvmf custom cptra_ctrl_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom cptra_ctrl_agent_bus_connections end
     );
  ss_mode_ctrl_if  ss_mode_ctrl_agent_bus(
     // pragma uvmf custom ss_mode_ctrl_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom ss_mode_ctrl_agent_bus_connections end
     );
  soc_ifc_status_if  soc_ifc_status_agent_bus(
     // pragma uvmf custom soc_ifc_status_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom soc_ifc_status_agent_bus_connections end
     );
  cptra_status_if  cptra_status_agent_bus(
     // pragma uvmf custom cptra_status_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom cptra_status_agent_bus_connections end
     );
  ss_mode_status_if  ss_mode_status_agent_bus(
     // pragma uvmf custom ss_mode_status_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom ss_mode_status_agent_bus_connections end
     );
  mbox_sram_if  mbox_sram_agent_bus(
     // pragma uvmf custom mbox_sram_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom mbox_sram_agent_bus_connections end
     );
  soc_ifc_ctrl_monitor_bfm  soc_ifc_ctrl_agent_mon_bfm(soc_ifc_ctrl_agent_bus.monitor_port);
  cptra_ctrl_monitor_bfm  cptra_ctrl_agent_mon_bfm(cptra_ctrl_agent_bus.monitor_port);
  ss_mode_ctrl_monitor_bfm  ss_mode_ctrl_agent_mon_bfm(ss_mode_ctrl_agent_bus.monitor_port);
  soc_ifc_status_monitor_bfm  soc_ifc_status_agent_mon_bfm(soc_ifc_status_agent_bus.monitor_port);
  cptra_status_monitor_bfm  cptra_status_agent_mon_bfm(cptra_status_agent_bus.monitor_port);
  ss_mode_status_monitor_bfm  ss_mode_status_agent_mon_bfm(ss_mode_status_agent_bus.monitor_port);
  mbox_sram_monitor_bfm  mbox_sram_agent_mon_bfm(mbox_sram_agent_bus.monitor_port);
  soc_ifc_ctrl_driver_bfm  soc_ifc_ctrl_agent_drv_bfm(soc_ifc_ctrl_agent_bus.initiator_port);
  cptra_ctrl_driver_bfm  cptra_ctrl_agent_drv_bfm(cptra_ctrl_agent_bus.initiator_port);
  ss_mode_ctrl_driver_bfm  ss_mode_ctrl_agent_drv_bfm(ss_mode_ctrl_agent_bus.initiator_port);
  soc_ifc_status_driver_bfm  soc_ifc_status_agent_drv_bfm(soc_ifc_status_agent_bus.responder_port);
  cptra_status_driver_bfm  cptra_status_agent_drv_bfm(cptra_status_agent_bus.responder_port);
  ss_mode_status_driver_bfm  ss_mode_status_agent_drv_bfm(ss_mode_status_agent_bus.responder_port);
  mbox_sram_driver_bfm  mbox_sram_agent_drv_bfm(mbox_sram_agent_bus.responder_port);

  // pragma uvmf custom dut_instantiation begin
  // AHB Clock/reset
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.default_clk_gen_CLK     = clk;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.default_reset_gen_RESET = cptra_status_agent_bus.cptra_noncore_rst_b;

    // AXI Interface
    axi_if #(
        .AW(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH                               ),
        .IW(`CALIPTRA_AXI_ID_WIDTH                                 ),
        .UW(`CALIPTRA_AXI_USER_WIDTH                               )
    ) s_axi_if (.clk(clk), .rst_n(soc_ifc_ctrl_agent_bus.cptra_rst_b));
    axi_if #(
        .AW(`CALIPTRA_AXI_DMA_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH    ),
        .IW(CPTRA_AXI_DMA_ID_WIDTH      ),
        .UW(CPTRA_AXI_DMA_USER_WIDTH    )
    ) m_axi_if (.clk(clk), .rst_n(soc_ifc_ctrl_agent_bus.cptra_rst_b));

    // DUT
    soc_ifc_top #(
        .AXI_ADDR_WIDTH (`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .AXI_DATA_WIDTH (`CALIPTRA_AXI_DATA_WIDTH                               ),
        .AXI_ID_WIDTH   (`CALIPTRA_AXI_ID_WIDTH                                 ),
        .AXI_USER_WIDTH (`CALIPTRA_AXI_USER_WIDTH                               ),
        .AHB_ADDR_WIDTH (`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .AHB_DATA_WIDTH (`CALIPTRA_AHB_HDATA_SIZE),
        .AXIM_ADDR_WIDTH(`CALIPTRA_AXI_DMA_ADDR_WIDTH),
        .AXIM_DATA_WIDTH(CPTRA_AXI_DMA_DATA_WIDTH    ),
        .AXIM_ID_WIDTH  (CPTRA_AXI_DMA_ID_WIDTH      ),
        .AXIM_USER_WIDTH(CPTRA_AXI_DMA_USER_WIDTH    )
        )
        dut
        (
        .clk               (clk               ),
        .clk_cg            (clk               ),
        .soc_ifc_clk_cg    (clk               ),
        .rdc_clk_cg        (clk               ),

        .cptra_pwrgood           (soc_ifc_ctrl_agent_bus.cptra_pwrgood             ),
        .cptra_rst_b             (soc_ifc_ctrl_agent_bus.cptra_rst_b               ),

        .ready_for_fuses         (soc_ifc_status_agent_bus.ready_for_fuses         ),
        .ready_for_mb_processing (soc_ifc_status_agent_bus.ready_for_mb_processing ),
        .ready_for_runtime       (soc_ifc_status_agent_bus.ready_for_runtime       ),

        .mailbox_data_avail      (soc_ifc_status_agent_bus.mailbox_data_avail      ),
        .mailbox_flow_done       (soc_ifc_status_agent_bus.mailbox_flow_done       ),

        .recovery_data_avail     (soc_ifc_ctrl_agent_bus.recovery_data_avail       ),
        .recovery_image_activated(soc_ifc_ctrl_agent_bus.recovery_image_activated  ),

        .security_state    (soc_ifc_ctrl_agent_bus.security_state),

        .generic_input_wires (soc_ifc_ctrl_agent_bus.generic_input_wires ),
        .BootFSM_BrkPoint    (soc_ifc_ctrl_agent_bus.BootFSM_BrkPoint),
        .generic_output_wires(soc_ifc_status_agent_bus.generic_output_wires),

        //AXI Interface with SoC
        .s_axi_w_if(s_axi_if.w_sub),
        .s_axi_r_if(s_axi_if.r_sub),

        //AHB Interface with uC
        .haddr_i    (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HADDR[`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)-1:0]),
        .hwdata_i   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWDATA     ),
        .hsel_i     (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HSEL       ),
        .hwrite_i   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWRITE     ),
        .hready_i   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HREADYOUT  ),
        .htrans_i   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HTRANS     ),
        .hsize_i    (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HSIZE      ),
        .hresp_o    (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRESP      ),
        .hreadyout_o(uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HREADY     ),
        .hrdata_o   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRDATA     ),

        // AXI Manager INF
        .m_axi_w_if(m_axi_if.w_mgr),
        .m_axi_r_if(m_axi_if.r_mgr),

        //SoC Interrupts
        .cptra_error_fatal    (soc_ifc_status_agent_bus.cptra_error_fatal    ),
        .cptra_error_non_fatal(soc_ifc_status_agent_bus.cptra_error_non_fatal),
        .trng_req             (soc_ifc_status_agent_bus.trng_req             ),

        // uC Interrupts
        .soc_ifc_error_intr(cptra_status_agent_bus.soc_ifc_error_intr),
        .soc_ifc_notif_intr(cptra_status_agent_bus.soc_ifc_notif_intr),
        .sha_error_intr    (cptra_status_agent_bus.sha_error_intr    ),
        .sha_notif_intr    (cptra_status_agent_bus.sha_notif_intr    ),
        .dma_error_intr    (cptra_status_agent_bus.dma_error_intr    ), // TODO
        .dma_notif_intr    (cptra_status_agent_bus.dma_notif_intr    ), // TODO
        .timer_intr        (cptra_status_agent_bus.timer_intr        ),

        //SRAM interface
        .mbox_sram_req(mbox_sram_agent_bus.mbox_sram_req),
        .mbox_sram_resp(mbox_sram_agent_bus.mbox_sram_resp),

        // RV ECC Status Interface
        .rv_ecc_sts(cptra_ctrl_agent_bus.rv_ecc_sts),

        //Obfuscated UDS and FE
        .clear_obf_secrets          (cptra_ctrl_agent_bus.clear_obf_secrets          ),
        .scan_mode                  (1'b0                                            ),
        .cptra_obf_key              (soc_ifc_ctrl_agent_bus.cptra_obf_key            ),
        .cptra_obf_key_reg          (cptra_status_agent_bus.cptra_obf_key_reg        ),
        .cptra_obf_field_entropy_vld(soc_ifc_ctrl_agent_bus.cptra_obf_field_entropy_vld),
        .cptra_obf_field_entropy    (soc_ifc_ctrl_agent_bus.cptra_obf_field_entropy    ),
        .obf_field_entropy          (cptra_status_agent_bus.obf_field_entropy        ),
        .cptra_obf_uds_seed_vld     (soc_ifc_ctrl_agent_bus.cptra_obf_uds_seed_vld     ),
        .cptra_obf_uds_seed         (soc_ifc_ctrl_agent_bus.cptra_obf_uds_seed         ),
        .obf_uds_seed               (cptra_status_agent_bus.obf_uds_seed             ),

        // Subsystem mode straps
        .strap_ss_caliptra_base_addr                            (ss_mode_ctrl_agent_bus.strap_ss_caliptra_base_addr                            ),
        .strap_ss_mci_base_addr                                 (ss_mode_ctrl_agent_bus.strap_ss_mci_base_addr                                 ),
        .strap_ss_recovery_ifc_base_addr                        (ss_mode_ctrl_agent_bus.strap_ss_recovery_ifc_base_addr                        ),
        .strap_ss_otp_fc_base_addr                              (ss_mode_ctrl_agent_bus.strap_ss_otp_fc_base_addr                              ),
        .strap_ss_uds_seed_base_addr                            (ss_mode_ctrl_agent_bus.strap_ss_uds_seed_base_addr                            ),
        .strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset(ss_mode_ctrl_agent_bus.strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset),
        .strap_ss_num_of_prod_debug_unlock_auth_pk_hashes       (ss_mode_ctrl_agent_bus.strap_ss_num_of_prod_debug_unlock_auth_pk_hashes       ),
        .strap_ss_strap_generic_0                               (ss_mode_ctrl_agent_bus.strap_ss_strap_generic_0                               ),
        .strap_ss_strap_generic_1                               (ss_mode_ctrl_agent_bus.strap_ss_strap_generic_1                               ),
        .strap_ss_strap_generic_2                               (ss_mode_ctrl_agent_bus.strap_ss_strap_generic_2                               ),
        .strap_ss_strap_generic_3                               (ss_mode_ctrl_agent_bus.strap_ss_strap_generic_3                               ),
        .strap_ss_caliptra_dma_axi_user                         (ss_mode_ctrl_agent_bus.strap_ss_caliptra_dma_axi_user                         ),
        .ss_debug_intent                                        (ss_mode_ctrl_agent_bus.ss_debug_intent                                        ),
        .cptra_ss_debug_intent                                  (ss_mode_status_agent_bus.cptra_ss_debug_intent                                ),

        // Subsystem mode debug outputs
        .ss_dbg_manuf_enable    (ss_mode_status_agent_bus.ss_dbg_manuf_enable    ),
        .ss_soc_dbg_unlock_level(ss_mode_status_agent_bus.ss_soc_dbg_unlock_level),

        // Subsystem mode firmware execution control
        .ss_generic_fw_exec_ctrl(ss_mode_status_agent_bus.ss_generic_fw_exec_ctrl),

        // NMI Vector 
        .nmi_vector(cptra_status_agent_bus.nmi_vector),
        .nmi_intr(cptra_status_agent_bus.nmi_intr),

        // ICCM Lock
        .iccm_lock(cptra_status_agent_bus.iccm_lock),
        .iccm_axs_blocked(cptra_ctrl_agent_bus.iccm_axs_blocked),

        //Other blocks reset
        .cptra_noncore_rst_b (cptra_status_agent_bus.cptra_noncore_rst_b),
        //uC reset
        .cptra_uc_rst_b (cptra_status_agent_bus.cptra_uc_rst_b),
        //Clock gating
        .clk_gating_en        (                                           ), // TODO
        .rdc_clk_dis          (                                           ), // TODO
        .fw_update_rst_window (cptra_status_agent_bus.fw_update_rst_window),
        .crypto_error         (cptra_ctrl_agent_bus.crypto_error          ),

        //caliptra uncore jtag ports
        .cptra_uncore_dmi_reg_en   (1'b0 ),
        .cptra_uncore_dmi_reg_wr_en(1'b0 ),
        .cptra_uncore_dmi_reg_rdata(     ),
        .cptra_uncore_dmi_reg_addr (7'h0 ),
        .cptra_uncore_dmi_reg_wdata(32'h0)
    );
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HBURST    = 3'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HPROT     = 7'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HMASTLOCK = 1'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HNONSEC   = 1'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HAUSER    = 64'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWUSER    = 64'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRUSER    = 64'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_mult_HSEL = 16'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HEXCL     = 1'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HMASTER   = 16'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HEXOKAY   = 1'b0;
    always_comb begin
        // Clock control placeholders
        ports[0].CACTIVE_m = 1'b0;
        ports[0].CACTIVE_s = 1'b0;
        ports[0].CSYSACK_m = 1'b0;
        ports[0].CSYSACK_s = 1'b0;

        // AXI AR
        s_axi_if.araddr  = ports[0].ARADDR;
        s_axi_if.arburst = ports[0].ARBURST;
        s_axi_if.arsize  = ports[0].ARSIZE;
        s_axi_if.arlen   = ports[0].ARLEN;
        s_axi_if.aruser  = ports[0].ARUSER;
        s_axi_if.arid    = ports[0].ARID;
        s_axi_if.arlock  = ports[0].ARLOCK;
        s_axi_if.arvalid = ports[0].ARVALID;
        ports[0].ARREADY = s_axi_if.arready;

        // AXI R
        ports[0].RDATA  = s_axi_if.rdata ;
        ports[0].RRESP  = s_axi_if.rresp ;
        ports[0].RID    = s_axi_if.rid   ;
        ports[0].RUSER  = s_axi_if.ruser ;
        ports[0].RLAST  = s_axi_if.rlast ;
        ports[0].RVALID = s_axi_if.rvalid;
        s_axi_if.rready = ports[0].RREADY;

        // AXI AW
        s_axi_if.awaddr  = ports[0].AWADDR;
        s_axi_if.awburst = ports[0].AWBURST;
        s_axi_if.awsize  = ports[0].AWSIZE;
        s_axi_if.awlen   = ports[0].AWLEN;
        s_axi_if.awuser  = ports[0].AWUSER;
        s_axi_if.awid    = ports[0].AWID;
        s_axi_if.awlock  = ports[0].AWLOCK;
        s_axi_if.awvalid = ports[0].AWVALID;
        ports[0].AWREADY = s_axi_if.awready;

        // AXI W
        s_axi_if.wdata  = ports[0].WDATA;
        s_axi_if.wstrb  = ports[0].WSTRB;
        s_axi_if.wuser  = ports[0].WUSER;
        s_axi_if.wvalid = ports[0].WVALID;
        s_axi_if.wlast  = ports[0].WLAST;
        ports[0].WREADY = s_axi_if.wready;

        // AXI B
        ports[0].BRESP  = s_axi_if.bresp ;
        ports[0].BID    = s_axi_if.bid   ;
        ports[0].BUSER  = s_axi_if.buser ;
        ports[0].BVALID = s_axi_if.bvalid;
        s_axi_if.bready = ports[0].BREADY;
    end
    // TODO
    always_comb begin
        // AXI AR
//        ports[0].ARADDR  = m_axi_if.araddr;
//        ports[0].ARBURST = m_axi_if.arburst;
//        ports[0].ARSIZE  = m_axi_if.arsize;
//        ports[0].ARLEN   = m_axi_if.arlen;
//        ports[0].ARUSER  = m_axi_if.aruser;
//        ports[0].ARID    = m_axi_if.arid;
//        ports[0].ARLOCK  = m_axi_if.arlock;
//        ports[0].ARVALID = m_axi_if.arvalid;
        m_axi_if.arready = '0;//ports[0].ARREADY;

        // AXI R
        m_axi_if.rdata  = '0; //ports[0].RDATA;
        m_axi_if.rresp  = '0; //ports[0].RRESP;
        m_axi_if.rid    = '0; //ports[0].RID;
        m_axi_if.rlast  = '0; //ports[0].RLAST;
        m_axi_if.rvalid = '0; //ports[0].RVALID;
//        ports[0].RREADY = s_axi_if.rready;

        // AXI AW
//        ports[0].AWADDR  = m_axi_if.awaddr;
//        ports[0].AWBURST = m_axi_if.awburst;
//        ports[0].AWSIZE  = m_axi_if.awsize;
//        ports[0].AWLEN   = m_axi_if.awlen;
//        ports[0].AWUSER  = m_axi_if.awuser;
//        ports[0].AWID    = m_axi_if.awid;
//        ports[0].AWLOCK  = m_axi_if.awlock;
//        ports[0].AWVALID = m_axi_if.awvalid;
        m_axi_if.awready = '0; //ports[0].AWREADY;

        // AXI W
//        ports[0].WDATA  = m_axi_if.wdata;
//        ports[0].WSTRB  = m_axi_if.wstrb;
//        ports[0].WVALID = m_axi_if.wvalid;
//        ports[0].WLAST  = m_axi_if.wlast;
        m_axi_if.wready = '0; //ports[0].WREADY;

        // AXI B
        m_axi_if.bresp  = '0; //ports[0].BRESP;
        m_axi_if.bid    = '0; //ports[0].BID;
        m_axi_if.bvalid = '0; //ports[0].BVALID;
//        ports[0].BREADY = m_axi_if.bready;
    end


  soc_ifc_cov_bind i_soc_ifc_cov_bind();  
  // pragma uvmf custom dut_instantiation end

  initial begin      // tbx vif_binding_block 
    import uvm_pkg::uvm_config_db;
    // The monitor_bfm and driver_bfm for each interface is placed into the uvm_config_db.
    // They are placed into the uvm_config_db using the string names defined in the parameters package.
    // The string names are passed to the agent configurations by test_top through the top level configuration.
    // They are retrieved by the agents configuration class for use by the agent.
    uvm_config_db #( virtual soc_ifc_ctrl_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_ctrl_agent_BFM , soc_ifc_ctrl_agent_mon_bfm ); 
    uvm_config_db #( virtual cptra_ctrl_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , cptra_ctrl_agent_BFM , cptra_ctrl_agent_mon_bfm ); 
    uvm_config_db #( virtual ss_mode_ctrl_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , ss_mode_ctrl_agent_BFM , ss_mode_ctrl_agent_mon_bfm ); 
    uvm_config_db #( virtual soc_ifc_status_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_status_agent_BFM , soc_ifc_status_agent_mon_bfm ); 
    uvm_config_db #( virtual cptra_status_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , cptra_status_agent_BFM , cptra_status_agent_mon_bfm ); 
    uvm_config_db #( virtual ss_mode_status_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , ss_mode_status_agent_BFM , ss_mode_status_agent_mon_bfm ); 
    uvm_config_db #( virtual mbox_sram_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , mbox_sram_agent_BFM , mbox_sram_agent_mon_bfm ); 
    uvm_config_db #( virtual soc_ifc_ctrl_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_ctrl_agent_BFM , soc_ifc_ctrl_agent_drv_bfm  );
    uvm_config_db #( virtual cptra_ctrl_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , cptra_ctrl_agent_BFM , cptra_ctrl_agent_drv_bfm  );
    uvm_config_db #( virtual ss_mode_ctrl_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , ss_mode_ctrl_agent_BFM , ss_mode_ctrl_agent_drv_bfm  );
    uvm_config_db #( virtual soc_ifc_status_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_status_agent_BFM , soc_ifc_status_agent_drv_bfm  );
    uvm_config_db #( virtual cptra_status_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , cptra_status_agent_BFM , cptra_status_agent_drv_bfm  );
    uvm_config_db #( virtual ss_mode_status_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , ss_mode_status_agent_BFM , ss_mode_status_agent_drv_bfm  );
    uvm_config_db #( virtual mbox_sram_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , mbox_sram_agent_BFM , mbox_sram_agent_drv_bfm  );
  end

endmodule

// pragma uvmf custom external begin
// pragma uvmf custom external end

