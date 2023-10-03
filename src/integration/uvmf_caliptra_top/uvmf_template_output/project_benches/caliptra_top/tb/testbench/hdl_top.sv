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
import qvip_apb5_slave_params_pkg::*;
import uvmf_base_pkg_hdl::*;

  // pragma attribute hdl_top partition_module_xrtl                                            
  hdl_qvip_ahb_lite_slave 
      #(
        .AHB_LITE_SLAVE_0_ACTIVE(0),
        .UNIQUE_ID("uvm_test_top.environment.soc_ifc_subenv.qvip_ahb_lite_slave_subenv."),
        .EXT_CLK_RESET(1)
       ) uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl();

  hdl_qvip_apb5_slave 
      #(
        .APB5_MASTER_0_ACTIVE(1),
        .UNIQUE_ID("uvm_test_top.environment.soc_ifc_subenv.qvip_apb5_slave_subenv."),
        .EXT_CLK_RESET(1)
       ) uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl();

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

    mbox_sram_req_t mbox_sram_req;
    mbox_sram_resp_t mbox_sram_resp;
    logic mbox_sram_cs_stub_inactive;
    logic mbox_sram_we_stub_inactive;
    logic [14:0] mbox_sram_addr_stub_inactive;
    logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_wdata_stub_inactive;
    logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_rdata_stub_inactive;

    logic imem_cs;
    logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] imem_addr;
    logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] imem_rdata;

    logic        etrng_req;
    logic  [3:0] itrng_data;
    logic        itrng_valid;

    //device lifecycle
    security_state_t security_state_stub_inactive;

    el2_mem_if el2_mem_export ();

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
  mbox_sram_if  soc_ifc_subenv_mbox_sram_agent_bus(
     // pragma uvmf custom soc_ifc_subenv_mbox_sram_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom soc_ifc_subenv_mbox_sram_agent_bus_connections end
     );
  soc_ifc_ctrl_monitor_bfm  soc_ifc_subenv_soc_ifc_ctrl_agent_mon_bfm(soc_ifc_subenv_soc_ifc_ctrl_agent_bus.monitor_port);
  cptra_ctrl_monitor_bfm  soc_ifc_subenv_cptra_ctrl_agent_mon_bfm(soc_ifc_subenv_cptra_ctrl_agent_bus.monitor_port);
  soc_ifc_status_monitor_bfm  soc_ifc_subenv_soc_ifc_status_agent_mon_bfm(soc_ifc_subenv_soc_ifc_status_agent_bus.monitor_port);
  cptra_status_monitor_bfm  soc_ifc_subenv_cptra_status_agent_mon_bfm(soc_ifc_subenv_cptra_status_agent_bus.monitor_port);
  mbox_sram_monitor_bfm  soc_ifc_subenv_mbox_sram_agent_mon_bfm(soc_ifc_subenv_mbox_sram_agent_bus.monitor_port);
  soc_ifc_ctrl_driver_bfm  soc_ifc_subenv_soc_ifc_ctrl_agent_drv_bfm(soc_ifc_subenv_soc_ifc_ctrl_agent_bus.initiator_port);
  soc_ifc_status_driver_bfm  soc_ifc_subenv_soc_ifc_status_agent_drv_bfm(soc_ifc_subenv_soc_ifc_status_agent_bus.responder_port);
  mbox_sram_driver_bfm  soc_ifc_subenv_mbox_sram_agent_drv_bfm(soc_ifc_subenv_mbox_sram_agent_bus.responder_port);

  // pragma uvmf custom dut_instantiation begin
  // AHB Clock/reset
  assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.default_clk_gen_CLK     = clk;
  assign uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_qvip_hdl.default_reset_gen_RESET = caliptra_top_dut.cptra_noncore_rst_b;
  assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.default_clk_gen_CLK         = clk;
  assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.default_reset_gen_RESET     = caliptra_top_dut.cptra_noncore_rst_b;


    //=========================================================================-
    // DUT instance
    //=========================================================================-
    caliptra_top caliptra_top_dut (
        .cptra_pwrgood              (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_pwrgood),
        .cptra_rst_b                (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_rst_b  ),
        .clk                        (clk),

        .cptra_obf_key              (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_obf_key),

        .jtag_tck   (jtag_tck   ),
        .jtag_tdi   (jtag_tdi   ),
        .jtag_tms   (jtag_tms   ),
        .jtag_trst_n(jtag_trst_n),
        .jtag_tdo   (jtag_tdo   ),
        
        .PADDR  (uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PADDR      ),
        .PPROT  (3'b000/*FIXME*/                                                                                  ),
        .PAUSER (uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PAUSER     ),
        .PENABLE(uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PENABLE    ),
        .PRDATA (uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PRDATA     ),
        .PREADY (uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PREADY     ),
        .PSEL   (uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PSEL       ),
        .PSLVERR(uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PSLVERR    ),
        .PWDATA (uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PWDATA     ),
        .PWRITE (uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PWRITE     ),

        .qspi_clk_o  (/*TODO*/),
        .qspi_cs_no  (/*TODO*/),
        .qspi_d_i    (/*TODO*/),
        .qspi_d_o    (/*TODO*/),
        .qspi_d_en_o (/*TODO*/),

        .el2_mem_export(el2_mem_export.veer_sram_src),

        .ready_for_fuses  (soc_ifc_subenv_soc_ifc_status_agent_bus.ready_for_fuses   ),
        .ready_for_fw_push(soc_ifc_subenv_soc_ifc_status_agent_bus.ready_for_fw_push ),
        .ready_for_runtime(soc_ifc_subenv_soc_ifc_status_agent_bus.ready_for_runtime ),

        .mbox_sram_cs   (mbox_sram_req.cs   ),
        .mbox_sram_we   (mbox_sram_req.we   ),
        .mbox_sram_addr (mbox_sram_req.addr ),
        .mbox_sram_wdata(mbox_sram_req.wdata),
        .mbox_sram_rdata(mbox_sram_resp.rdata),

        .imem_cs        (imem_cs        ),
        .imem_addr      (imem_addr      ),
        .imem_rdata     (imem_rdata     ),

        .mailbox_data_avail(soc_ifc_subenv_soc_ifc_status_agent_bus.mailbox_data_avail),
        .mailbox_flow_done (soc_ifc_subenv_soc_ifc_status_agent_bus.mailbox_flow_done ),
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

        .generic_input_wires (soc_ifc_subenv_soc_ifc_ctrl_agent_bus.generic_input_wires),
        .generic_output_wires(soc_ifc_subenv_soc_ifc_status_agent_bus.generic_output_wires),

        .security_state(soc_ifc_subenv_soc_ifc_ctrl_agent_bus.security_state),
        .scan_mode     (1'b0) // TODO
    );
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PWUSER           = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PRUSER           = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PBUSER           = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PWAKEUP          = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PADDRCHK         = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PCTRLCHK         = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PSELxCHK         = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PENABLECHK       = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PWDATACHK        = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PSTRBCHK         = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PWAKEUPCHK       = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PAUSERCHK        = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PWUSERCHK        = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PREADYCHK        = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PRDATACHK        = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PSLVERRCHK       = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PRUSERCHK        = 0;
    assign uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_qvip_hdl.apb5_master_0_PBUSERCHK        = 0;
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

  // pragma uvmf custom dut_instantiation end

  initial begin      // tbx vif_binding_block 
    import uvm_pkg::uvm_config_db;
    // The monitor_bfm and driver_bfm for each interface is placed into the uvm_config_db.
    // They are placed into the uvm_config_db using the string names defined in the parameters package.
    // The string names are passed to the agent configurations by test_top through the top level configuration.
    // They are retrieved by the agents configuration class for use by the agent.
    uvm_config_db #( virtual soc_ifc_ctrl_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_soc_ifc_ctrl_agent_BFM , soc_ifc_subenv_soc_ifc_ctrl_agent_mon_bfm ); 
    uvm_config_db #( virtual cptra_ctrl_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_cptra_ctrl_agent_BFM , soc_ifc_subenv_cptra_ctrl_agent_mon_bfm ); 
    uvm_config_db #( virtual soc_ifc_status_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_soc_ifc_status_agent_BFM , soc_ifc_subenv_soc_ifc_status_agent_mon_bfm ); 
    uvm_config_db #( virtual cptra_status_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_cptra_status_agent_BFM , soc_ifc_subenv_cptra_status_agent_mon_bfm ); 
    uvm_config_db #( virtual mbox_sram_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_mbox_sram_agent_BFM , soc_ifc_subenv_mbox_sram_agent_mon_bfm ); 
    uvm_config_db #( virtual soc_ifc_ctrl_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_soc_ifc_ctrl_agent_BFM , soc_ifc_subenv_soc_ifc_ctrl_agent_drv_bfm  );
    uvm_config_db #( virtual soc_ifc_status_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_soc_ifc_status_agent_BFM , soc_ifc_subenv_soc_ifc_status_agent_drv_bfm  );
    uvm_config_db #( virtual mbox_sram_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , soc_ifc_subenv_mbox_sram_agent_BFM , soc_ifc_subenv_mbox_sram_agent_drv_bfm ); 
  end

endmodule

// pragma uvmf custom external begin
// pragma uvmf custom external end

