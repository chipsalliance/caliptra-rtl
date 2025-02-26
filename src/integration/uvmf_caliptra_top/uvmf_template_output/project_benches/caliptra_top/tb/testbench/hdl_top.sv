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
import caliptra_aaxi_uvm_pkg::*;
`include "config_defines.svh"

  // pragma attribute hdl_top partition_module_xrtl                                            
  hdl_qvip_ahb_lite_slave 
      #(
        .AHB_LITE_SLAVE_0_ACTIVE(0),
        .UNIQUE_ID("uvm_test_top.environment.soc_ifc_subenv.qvip_ahb_lite_slave_subenv."),
        .EXT_CLK_RESET(1)
       ) uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl();

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

    logic        etrng_req;
    logic  [3:0] itrng_data;
    logic        itrng_valid;

    //device lifecycle
    security_state_t security_state_stub_inactive;

    el2_mem_if el2_mem_export ();
    mldsa_mem_if mldsa_memory_export();

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

  // pragma uvmf custom avery_vip_components begin
    // Avery VIP signals
    //uc
    caliptra_aaxi_uvm_container  uc;             //VAR: UVM container

    aaxi_intf #(
        .MCB_INPUT (aaxi_pkg::AAXI_MCB_INPUT ),
        .MCB_OUTPUT(aaxi_pkg::AAXI_MCB_OUTPUT),
        .SCB_INPUT (aaxi_pkg::AAXI_SCB_INPUT ),
        .SCB_OUTPUT(aaxi_pkg::AAXI_SCB_OUTPUT)
    ) m_ports_arr[1] (
        .ACLK   (clk                                              ),
        .ARESETn(soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_rst_b/*1'b1*/),
        .CACTIVE(                                                 ),
        .CSYSREQ(1'b0                                             ),
        .CSYSACK(                                                 )
    );
    aaxi_intf #(
        .MCB_INPUT (aaxi_pkg::AAXI_MCB_INPUT ),
        .MCB_OUTPUT(aaxi_pkg::AAXI_MCB_OUTPUT),
        .SCB_INPUT (aaxi_pkg::AAXI_SCB_INPUT ),
        .SCB_OUTPUT(aaxi_pkg::AAXI_SCB_OUTPUT)
    ) s_ports_arr[1] (
        .ACLK   (clk                                              ),
        .ARESETn(soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_rst_b),
        .CACTIVE(                                                 ),
        .CSYSREQ(1'b0                                             ),
        .CSYSACK(                                                 )
    );
    aaxi_monitor_wrapper monitor0 (m_ports_arr[0]);
    defparam monitor0.ID_WIDTH= AAXI_ID_WIDTH;
    defparam monitor0.BUS_DATA_WIDTH=aaxi_pkg::AAXI_DATA_WIDTH;
    // enable the support of all user-defined signaling
    defparam monitor0.USER_SUPPORT= 5'b11111;
    defparam monitor0.VER= "AXI4";

    aaxi_monitor_wrapper monitor1 (s_ports_arr[0]);
    defparam monitor1.ID_WIDTH= AAXI_ID_WIDTH;
    defparam monitor1.BUS_DATA_WIDTH=aaxi_pkg::AAXI_DATA_WIDTH;
    // enable the support of all user-defined signaling
    defparam monitor1.USER_SUPPORT= 5'b11111;
    defparam monitor1.VER= "AXI4";

    initial begin
      uc = new();
      uvm_config_db #(caliptra_aaxi_uvm_container)::set(uvm_root::get(), "*", "intf_uc", uc);

      uc.m_ports_arr = m_ports_arr;
      uc.s_ports_arr = s_ports_arr;
      //uvm_config_db #(virtual aaxi_intf)::set(uvm_root::get(), "intf_uc", "ports", ports[0]);
    end
  // pragma uvmf custom avery_vip_components end

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
        .mldsa_memory_export(mldsa_memory_export.req),

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

        .recovery_data_avail     (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.recovery_data_avail       ),
        .recovery_image_activated(soc_ifc_subenv_soc_ifc_ctrl_agent_bus.recovery_image_activated  ),

        .BootFSM_BrkPoint  (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.BootFSM_BrkPoint),

        //SoC Interrupts
        .cptra_error_fatal    (soc_ifc_subenv_soc_ifc_status_agent_bus.cptra_error_fatal),
        .cptra_error_non_fatal(soc_ifc_subenv_soc_ifc_status_agent_bus.cptra_error_non_fatal),
        // External TRNG
`ifdef CALIPTRA_INTERNAL_TRNG
        .etrng_req             (etrng_req),
        // Internal TRNG
        .itrng_data            (itrng_data ),
        .itrng_valid           (itrng_valid),
`else
        .etrng_req             (soc_ifc_subenv_soc_ifc_status_agent_bus.trng_req),
        // Internal TRNG
        .itrng_data            (4'h0),
        .itrng_valid           (1'b0),
`endif

        // Subsystem mode straps
        .strap_ss_caliptra_base_addr                            (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_caliptra_base_addr                            ),
        .strap_ss_mci_base_addr                                 (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_mci_base_addr                                 ),
        .strap_ss_recovery_ifc_base_addr                        (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_recovery_ifc_base_addr                        ),
        .strap_ss_otp_fc_base_addr                              (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_otp_fc_base_addr                              ),
        .strap_ss_uds_seed_base_addr                            (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_uds_seed_base_addr                            ),
        .strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset(soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset),
        .strap_ss_num_of_prod_debug_unlock_auth_pk_hashes       (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_num_of_prod_debug_unlock_auth_pk_hashes       ),
        .strap_ss_caliptra_dma_axi_user                         (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_caliptra_dma_axi_user                         ),
        .strap_ss_strap_generic_0                               (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_strap_generic_0                               ),
        .strap_ss_strap_generic_1                               (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_strap_generic_1                               ),
        .strap_ss_strap_generic_2                               (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_strap_generic_2                               ),
        .strap_ss_strap_generic_3                               (soc_ifc_subenv_ss_mode_ctrl_agent_bus.strap_ss_strap_generic_3                               ),
        .ss_debug_intent                                        (soc_ifc_subenv_ss_mode_ctrl_agent_bus.ss_debug_intent                                        ),

        // Subsystem mode debug outputs
        .ss_dbg_manuf_enable    (soc_ifc_subenv_ss_mode_status_agent_bus.ss_dbg_manuf_enable    ),
        .ss_soc_dbg_unlock_level(soc_ifc_subenv_ss_mode_status_agent_bus.ss_soc_dbg_unlock_level),

        // Subsystem mode firmware execution control
        .ss_generic_fw_exec_ctrl(soc_ifc_subenv_ss_mode_status_agent_bus.ss_generic_fw_exec_ctrl),

        .generic_input_wires (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.generic_input_wires),
        .generic_output_wires(soc_ifc_subenv_soc_ifc_status_agent_bus.generic_output_wires),

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
        // Clock control placeholders
        m_ports_arr[0].CACTIVE_m = 1'b0;
        m_ports_arr[0].CACTIVE_s = 1'b0;
        m_ports_arr[0].CSYSACK_m = 1'b0;
        m_ports_arr[0].CSYSACK_s = 1'b0;

        // AXI AR
        s_axi_if.araddr  = m_ports_arr[0].ARADDR;
        s_axi_if.arburst = m_ports_arr[0].ARBURST;
        s_axi_if.arsize  = m_ports_arr[0].ARSIZE;
        s_axi_if.arlen   = m_ports_arr[0].ARLEN;
        s_axi_if.aruser  = m_ports_arr[0].ARUSER;
        s_axi_if.arid    = m_ports_arr[0].ARID;
        s_axi_if.arlock  = m_ports_arr[0].ARLOCK;
        s_axi_if.arvalid = m_ports_arr[0].ARVALID;
        m_ports_arr[0].ARREADY = s_axi_if.arready;

        // AXI R
        m_ports_arr[0].RDATA  = s_axi_if.rdata ;
        m_ports_arr[0].RRESP  = s_axi_if.rresp ;
        m_ports_arr[0].RID    = s_axi_if.rid   ;
        m_ports_arr[0].RUSER  = s_axi_if.ruser ;
        m_ports_arr[0].RLAST  = s_axi_if.rlast ;
        m_ports_arr[0].RVALID = s_axi_if.rvalid;
        s_axi_if.rready = m_ports_arr[0].RREADY;

        // AXI AW
        s_axi_if.awaddr  = m_ports_arr[0].AWADDR;
        s_axi_if.awburst = m_ports_arr[0].AWBURST;
        s_axi_if.awsize  = m_ports_arr[0].AWSIZE;
        s_axi_if.awlen   = m_ports_arr[0].AWLEN;
        s_axi_if.awuser  = m_ports_arr[0].AWUSER;
        s_axi_if.awid    = m_ports_arr[0].AWID;
        s_axi_if.awlock  = m_ports_arr[0].AWLOCK;
        s_axi_if.awvalid = m_ports_arr[0].AWVALID;
        m_ports_arr[0].AWREADY = s_axi_if.awready;

        // AXI W
        s_axi_if.wdata  = m_ports_arr[0].WDATA;
        s_axi_if.wstrb  = m_ports_arr[0].WSTRB;
        s_axi_if.wuser  = m_ports_arr[0].WUSER;
        s_axi_if.wvalid = m_ports_arr[0].WVALID;
        s_axi_if.wlast  = m_ports_arr[0].WLAST;
        m_ports_arr[0].WREADY = s_axi_if.wready;

        // AXI B
        m_ports_arr[0].BRESP  = s_axi_if.bresp ;
        m_ports_arr[0].BID    = s_axi_if.bid   ;
        m_ports_arr[0].BUSER  = s_axi_if.buser ;
        m_ports_arr[0].BVALID = s_axi_if.bvalid;
        s_axi_if.bready = m_ports_arr[0].BREADY;
    end
    always_comb begin
        // Clock control placeholders
        s_ports_arr[0].CACTIVE_m = 1'b0;
        s_ports_arr[0].CACTIVE_s = 1'b0;
        s_ports_arr[0].CSYSACK_m = 1'b0;
        s_ports_arr[0].CSYSACK_s = 1'b0;

        // AXI AR
        s_ports_arr[0].ARADDR  = m_axi_if.araddr;
        s_ports_arr[0].ARBURST = m_axi_if.arburst;
        s_ports_arr[0].ARSIZE  = m_axi_if.arsize;
        s_ports_arr[0].ARLEN   = m_axi_if.arlen;
        s_ports_arr[0].ARUSER  = m_axi_if.aruser;
        s_ports_arr[0].ARID    = m_axi_if.arid;
        s_ports_arr[0].ARLOCK  = m_axi_if.arlock;
        s_ports_arr[0].ARVALID = m_axi_if.arvalid;
        m_axi_if.arready = s_ports_arr[0].ARREADY;
        s_ports_arr[0].ARCACHE  = '0;
        s_ports_arr[0].ARPROT   = '0;
        s_ports_arr[0].ARQOS    = '0;
        s_ports_arr[0].ARREGION = '0;

        // AXI R
        m_axi_if.rdata  = s_ports_arr[0].RDATA;
        m_axi_if.rresp  = s_ports_arr[0].RRESP;
        m_axi_if.rid    = s_ports_arr[0].RID;
        m_axi_if.ruser  = s_ports_arr[0].RUSER;
        m_axi_if.rlast  = s_ports_arr[0].RLAST;
        m_axi_if.rvalid = s_ports_arr[0].RVALID;
        s_ports_arr[0].RREADY = m_axi_if.rready;

        // AXI AW
        s_ports_arr[0].AWADDR  = m_axi_if.awaddr;
        s_ports_arr[0].AWBURST = m_axi_if.awburst;
        s_ports_arr[0].AWSIZE  = m_axi_if.awsize;
        s_ports_arr[0].AWLEN   = m_axi_if.awlen;
        s_ports_arr[0].AWUSER  = m_axi_if.awuser;
        s_ports_arr[0].AWID    = m_axi_if.awid;
        s_ports_arr[0].AWLOCK  = m_axi_if.awlock;
        s_ports_arr[0].AWVALID = m_axi_if.awvalid;
        m_axi_if.awready = s_ports_arr[0].AWREADY;
        s_ports_arr[0].AWCACHE  = '0;
        s_ports_arr[0].AWPROT   = '0;
        s_ports_arr[0].AWQOS    = '0;
        s_ports_arr[0].AWREGION = '0;

        // AXI W
        s_ports_arr[0].WDATA  = m_axi_if.wdata;
        s_ports_arr[0].WSTRB  = m_axi_if.wstrb;
        s_ports_arr[0].WUSER  = m_axi_if.wuser;
        s_ports_arr[0].WVALID = m_axi_if.wvalid;
        s_ports_arr[0].WLAST  = m_axi_if.wlast;
        m_axi_if.wready = s_ports_arr[0].WREADY;

        // AXI B
        m_axi_if.bresp  = s_ports_arr[0].BRESP;
        m_axi_if.bid    = s_ports_arr[0].BID;
        m_axi_if.buser  = s_ports_arr[0].BUSER;
        m_axi_if.bvalid = s_ports_arr[0].BVALID;
        s_ports_arr[0].BREADY = m_axi_if.bready;
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
        .enable (etrng_req),
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
        .mldsa_memory_export (mldsa_memory_export.resp),

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
  end

endmodule

// pragma uvmf custom external begin
// pragma uvmf custom external end

