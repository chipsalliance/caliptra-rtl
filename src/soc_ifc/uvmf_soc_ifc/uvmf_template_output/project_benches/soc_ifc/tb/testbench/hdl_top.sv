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
import soc_ifc_pkg::*;
import soc_ifc_axi_topology_pkg::*;

import uvm_pkg::*;
`include "uvm_macros.svh"
import aaxi_uvm_pkg::*;
`ifdef CALIPTRA_MODE_SUBSYSTEM
import pv_defines_pkg::*;
`endif
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

  // Two manager ports: active SoC stimulus and the RTL DMA manager. Interfaces
  // use Avery's expanded interconnect ID width; explicit casts below isolate
  // the narrower native DMA ID width at the DUT boundary.
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
  // Three subordinate ports: Caliptra RTL, SRAM model, and recovery FIFO.
  // Caliptra is connected directly to RTL, while Avery actively responds for
  // the two testbench-owned storage endpoints.
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
  // Avery uses a dedicated control interface to connect all fabric ports.
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

`ifdef CALIPTRA_MODE_SUBSYSTEM
    // PCR-vault plumbing for the subsystem ICCM-content-hash flow.
    pv_read_t                     dut_pv_read;    // DUT PCR read request  (output)
    pv_write_t                    dut_pv_write;   // DUT PCR write request (output)
    logic                         dut_iccm_unlock;// DUT iccm_unlock_o      (output)
    pv_read_t    [PV_NUM_READ-1:0]  pv_read_arr;
    pv_write_t   [PV_NUM_WRITE-1:0] pv_write_arr;
    pv_rd_resp_t [PV_NUM_READ-1:0]  pv_rd_resp_arr;
    pv_wr_resp_t [PV_NUM_WRITE-1:0] pv_wr_resp_arr;
`endif

    // Construct the HW fatal error struct from UVMF interface signals
    cptra_hw_fatal_error_t cptra_hw_fatal_errors_i;
    assign cptra_hw_fatal_errors_i.crypto_err = cptra_ctrl_agent_bus.crypto_error;
    assign cptra_hw_fatal_errors_i.kv_error   = 1'b0;
    assign cptra_hw_fatal_errors_i.fsm_error  = 1'b0;

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

        .recovery_data_avail     (recovery_if.recovery_data_avail                  ),
        .recovery_image_activated(recovery_if.recovery_image_activated              ),

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

        // Clear KeyVault secrets
        .debugUnlock_or_scan_mode_switch(1'b0), // TODO currently not driving debug/scan tests in UVM

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
        .obf_hek_seed               (cptra_status_agent_bus.obf_hek_seed             ),

        .aes_input_ready (1'b0              ), // \
        .aes_output_valid(1'b0              ), //  \
        .aes_status_idle (1'b0              ), //   \
        .aes_req_dv      (                  ), //   |----- TODO
        .aes_req_hold    (1'b0              ), //   /
        .aes_req_data    (                  ), //  /
        .aes_rdata       (SOC_IFC_DATA_W'(0)), // /
        .aes_error       (1'b0              ), ///

        // kv interface
        .kv_read   (  /*TODO*/),
        .kv_rd_resp('0/*TODO*/),

        // Subsystem mode straps
        .strap_ss_caliptra_base_addr                            (ss_mode_ctrl_agent_bus.strap_ss_caliptra_base_addr                            ),
        .strap_ss_mci_base_addr                                 (ss_mode_ctrl_agent_bus.strap_ss_mci_base_addr                                 ),
        .strap_ss_recovery_ifc_base_addr                        (ss_mode_ctrl_agent_bus.strap_ss_recovery_ifc_base_addr                        ),
        .strap_ss_external_staging_area_base_addr               (ss_mode_ctrl_agent_bus.strap_ss_external_staging_area_base_addr                        ),
        .strap_ss_otp_fc_base_addr                              (ss_mode_ctrl_agent_bus.strap_ss_otp_fc_base_addr                              ),
        .strap_ss_uds_seed_base_addr                            (ss_mode_ctrl_agent_bus.strap_ss_uds_seed_base_addr                            ),
        .strap_ss_key_release_base_addr                         (ss_mode_ctrl_agent_bus.strap_ss_key_release_base_addr                         ),
        .strap_ss_key_release_key_size                          (ss_mode_ctrl_agent_bus.strap_ss_key_release_key_size                          ),
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

        // Subsystem mode OCP LOCK status
        .ss_ocp_lock_en         (1'b0/*TODO*/),
        .ss_ocp_lock_in_progress(    /*TODO*/),
        .ss_key_release_key_size(    /*TODO*/),

        // Dual iTRNG enable strap in / CPTRA_HW_CONFIG.dual_iTRNG_en value out
        .dual_itrng_en          (1'b0/*TODO*/),
        .dual_itrng_en_o        (    /*TODO*/),

        .stable_owner_key_en(       /*TODO*/),

        // NMI Vector 
        .nmi_vector(cptra_status_agent_bus.nmi_vector),
        .nmi_intr(cptra_status_agent_bus.nmi_intr),

        // ICCM Lock
        .iccm_lock(cptra_status_agent_bus.iccm_lock),
        .iccm_axs_blocked(cptra_ctrl_agent_bus.iccm_axs_blocked),

        // ICCM hash mode
        .iccm_hash_dv(1'b0),
        .iccm_hash_data(32'b0),
`ifdef CALIPTRA_MODE_SUBSYSTEM
        .pv_write(dut_pv_write),
        .iccm_unlock_o(dut_iccm_unlock),
        // ICCM PCR extend
        .pv_read(dut_pv_read),
        .pv_rd_resp(pv_rd_resp_arr[1]),
`else
        .pv_write(),
        .iccm_unlock_o(),
        .pv_read(),
        .pv_rd_resp('0),
`endif

        //Other blocks reset
        .cptra_noncore_rst_b (cptra_status_agent_bus.cptra_noncore_rst_b),
        //uC reset
        .cptra_uc_rst_b (cptra_status_agent_bus.cptra_uc_rst_b),
        //Clock gating
        .clk_gating_en        (                                           ), // TODO
        .rdc_clk_dis          (                                           ), // TODO
        .fw_update_rst_window (cptra_status_agent_bus.fw_update_rst_window),
        .cptra_hw_fatal_errors(cptra_hw_fatal_errors_i                  ),
        .iccm_fmc_start_addr  (                                           ),
        .iccm_fmc_end_addr    (                                           ),
        .iccm_rt_start_addr   (                                           ),
        .iccm_rt_end_addr     (                                           ),
        .iccm_region_lock     (                                           ),

        //caliptra uncore jtag ports
        .cptra_uncore_dmi_reg_en   (1'b0 ),
        .cptra_uncore_dmi_reg_wr_en(1'b0 ),
        .cptra_uncore_dmi_reg_rdata(     ),
        .cptra_uncore_dmi_reg_addr (7'h0 ),
        .cptra_uncore_dmi_reg_wdata(32'h0)
    );

    soc_ifc_sha_status_if sha_status_if (
        .clk     (clk                                           ),
        .sha_lock(dut.i_sha512_acc_top.hwif_out.LOCK.LOCK.value )
    );

`ifdef CALIPTRA_MODE_SUBSYSTEM
    // -----------------------------------------------------------------------
    // PCR Vault (pcrvault) instance.
    //
    // In subsystem mode the SHA accelerator boots LOCKED (RDL LOCK=1) and the
    // HW ICCM-content-hash flow (sha512_acc_iccm_hash) releases it only after it
    // measures ICCM and extends PCR4/PCR5 to EXTEND_DONE. That PCR extend needs a
    // PCR vault to answer reads and accept writes. This instance provides it so
    // the explicitly requested reset flow can unlock the SHA accelerator.
    //
    // soc_ifc presents a single PCR read/write client; connect it to client index
    // 1 (matching caliptra_top) and tie off the unused client and the SW AHB
    // interface.
    // -----------------------------------------------------------------------
    always_comb begin
        pv_read_arr        = '0;
        pv_write_arr       = '0;
        pv_read_arr[1]     = dut_pv_read;
        pv_write_arr[1]    = dut_pv_write;
    end

    pv #(
        .AHB_ADDR_WIDTH(PV_ADDR_W),
        .AHB_DATA_WIDTH(32)
    ) i_pv (
        .clk                 (clk                                        ),
        .rst_b               (cptra_status_agent_bus.cptra_noncore_rst_b ),
        .core_only_rst_b     (cptra_status_agent_bus.cptra_uc_rst_b      ),
        .cptra_pwrgood       (soc_ifc_ctrl_agent_bus.cptra_pwrgood       ),
        .fw_update_rst_window(cptra_status_agent_bus.fw_update_rst_window),
        // SW AHB interface tied off (no firmware PCR configuration in this bench)
        .haddr_i             ('0    ),
        .hwdata_i            ('0    ),
        .hsel_i              (1'b0  ),
        .hwrite_i            (1'b0  ),
        .hready_i            (1'b1  ),
        .htrans_i            (2'b0  ),
        .hsize_i             (3'b0  ),
        .hresp_o             (      ),
        .hreadyout_o         (      ),
        .hrdata_o            (      ),
        .pv_read             (pv_read_arr    ),
        .pv_write            (pv_write_arr   ),
        .pv_rd_resp          (pv_rd_resp_arr ),
        .pv_wr_resp          (pv_wr_resp_arr ),
        .iccm_unlock         (dut_iccm_unlock)
    );
`endif

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
        // Interconnect Caliptra subordinate to the DUT AXI subordinate. Address
        // slicing is safe because this port is restricted to the Caliptra
        // aperture by the fabric address map.
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

        // Connect the DUT DMA manager to the fabric manager port. ID casts are
        // limited to this boundary: requests expand into the interconnect width
        // and responses contract back to the native DMA width.
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


  soc_ifc_cov_bind i_soc_ifc_cov_bind();
  axi_dma_top_cov_bind i_axi_dma_top_cov_bind();
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
    uvm_config_db #( virtual soc_ifc_sha_status_if )::set(
        null, UVMF_VIRTUAL_INTERFACES,
        soc_ifc_env_pkg::SOC_IFC_SHA_STATUS_VIF, sha_status_if);
    // Publish each static interface under the names in the fabric config.
    // Runtime components retrieve virtual interfaces by these names rather than
    // depending on hdl_top hierarchy paths.
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
    `uvm_info("SOC_IFC_HDL_TOP",
      "Published the 2x3 AXI fabric, recovery, and SHA virtual interfaces",
      UVM_LOW)
  end

endmodule

// pragma uvmf custom external begin
// pragma uvmf custom external end
