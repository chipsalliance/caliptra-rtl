//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
// Description: Synthesizable top of the HMAC256 UVMF bench. Instantiates
//    the QVIP AHB master, the DUT (hmac256_ctrl), and the coverage
//    bind. HMAC-256 has no KeyVault or CSR_MODE interface, so the
//    corresponding ports/signals present on hmac_ctrl are absent here.
//
//----------------------------------------------------------------------

module hdl_top;

import HMAC256_parameters_pkg::*;
import qvip_ahb_lite_slave_params_pkg::*;
import uvmf_base_pkg_hdl::*;
import uvm_pkg::*;
`include "uvm_macros.svh"

  // pragma attribute hdl_top partition_module_xrtl
  hdl_qvip_ahb_lite_slave
      #(
        .AHB_LITE_SLAVE_0_ACTIVE(1),
        .UNIQUE_ID("uvm_test_top.environment.qvip_ahb_lite_slave_subenv."),
        .EXT_CLK_RESET(1)
       ) uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl();

// pragma uvmf custom clock_generator begin
  bit clk;
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
  // abr/mldsa-style reset: bit rst is wired directly to the DUT's
  // reset_n and cptra_pwrgood ports (and to the QVIP's reset). The
  // hmac256_rst agent below is kept as infrastructure for the
  // predictor's monitor hook but does not drive any DUT pin.
  // uvm_event "ev_rst" is used by the otf_reset test to inject
  // mid-sim resets.
  bit rst;
  uvm_event ev_rst;
  initial begin
    ev_rst = uvm_event_pool::get_global("ev_rst");
    rst = 1'b0;
    #200ns;
    rst = 1'b1;
    forever begin
      ev_rst.wait_trigger();
      `uvm_info("HDL_TOP", "ev_rst triggered -- pulsing rst low for 200ns", UVM_LOW)
      rst = 1'b0;
      #200ns;
      rst = 1'b1;
    end
  end
// pragma uvmf custom reset_generator end

  // pragma uvmf custom module_item_additional begin
  // pragma uvmf custom module_item_additional end

  // hmac256_rst_agent_bus kept so the rst agent class definitions
  // compile and the uvm_config_db::set below works, but the bus's
  // reset/pwrgood signals are not connected to the DUT (see assigns
  // below). The .dummy(1'b1) drives the wait_for_reset sentinel high
  // so the bench's wait_for_reset() returns immediately.
  HMAC256_rst_if  hmac256_rst_agent_bus(
     .clk(clk), .dummy(1'b1)
     );
  HMAC256_rst_monitor_bfm  hmac256_rst_agent_mon_bfm(hmac256_rst_agent_bus.monitor_port);
  HMAC256_rst_driver_bfm   hmac256_rst_agent_drv_bfm(hmac256_rst_agent_bus.initiator_port);

  // pragma uvmf custom dut_instantiation begin
  // AHB Clock/reset -- drive QVIP RESET directly from bit rst (abr pattern).
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.default_clk_gen_CLK     = clk;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.default_reset_gen_RESET = rst;

  hmac256_ctrl #(
      .AHB_ADDR_WIDTH(32),
      .AHB_DATA_WIDTH(64)
  ) dut (
      .clk          (clk),
      .reset_n      (rst),
      .cptra_pwrgood(rst),

      .haddr_i    (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HADDR    ),
      .hwdata_i   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWDATA   ),
      .hsel_i     (1'b1                                                                                   ),
      .hwrite_i   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWRITE   ),
      .hready_i   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HREADYOUT),
      .htrans_i   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HTRANS   ),
      .hsize_i    (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HSIZE    ),
      .hresp_o    (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRESP    ),
      .hreadyout_o(uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HREADY   ),
      .hrdata_o   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRDATA   ),

      .busy_o     (),
      .error_intr (),
      .notif_intr (),

      .debugUnlock_or_scan_mode_switch('0)
  );

  // QVIP AHB master defaults (not driven by hmac256_ctrl).
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HBURST    = 3'b0;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HPROT     = 7'b0;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HMASTLOCK = 1'b0;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HSEL      = 1'b0;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HNONSEC   = 1'b0;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HAUSER    = 64'b0;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWUSER    = 64'b0;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRUSER    = 64'b0;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_mult_HSEL = 16'b0;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HEXCL     = 1'b0;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HMASTER   = 16'b0;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HEXOKAY   = 1'b0;

  hmac256_ctrl_cov_bind i_hmac256_ctrl_cov_bind();
  // pragma uvmf custom dut_instantiation end

  initial begin      // tbx vif_binding_block
    import uvm_pkg::uvm_config_db;
    uvm_config_db #( virtual HMAC256_rst_monitor_bfm )::set( null , UVMF_VIRTUAL_INTERFACES , hmac256_rst_agent_BFM , hmac256_rst_agent_mon_bfm );
    uvm_config_db #( virtual HMAC256_rst_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , hmac256_rst_agent_BFM , hmac256_rst_agent_drv_bfm );
  end

endmodule

// pragma uvmf custom external begin
// pragma uvmf custom external end
