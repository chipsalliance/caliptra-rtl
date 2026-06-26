//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
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

import HMAC_parameters_pkg::*;
import qvip_ahb_lite_slave_params_pkg::*;
import uvmf_base_pkg_hdl::*;
// Pulled in for `uvm_event` / `uvm_event_pool` used by the abr-style
// on-the-fly reset mechanism in the reset_generator pragma block below.
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
  // abr/mldsa-style reset: bit rst is wired DIRECTLY to the DUT's
  // reset_n and cptra_pwrgood ports (and to the QVIP's reset). The
  // hmac_rst agent below is kept as infrastructure for the predictor's
  // monitor hook, but does NOT drive any DUT pin. uvm_event "ev_rst"
  // is used by future otf_reset_test to inject mid-sim resets, same
  // as ML_DSA_randomized_reset_sequence.
  bit rst;
  uvm_event ev_rst;
  initial begin
    ev_rst = uvm_event_pool::get_global("ev_rst");
    rst = 1'b0;
    #200ns;
    rst = 1'b1;
    // On-the-fly reset loop: when a sequence triggers ev_rst, pulse rst
    // low for 200ns, then back high. Matches abr hdl_top.
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

  // Instantiate the signal bundle, monitor bfm and driver bfm for each interface.
  // NOTE (abr-style rewire): hmac_rst_agent_bus is kept so the rst agent
  // class definitions compile and uvm_config_db::set below works, but
  // the bus's reset/pwrgood signals are NOT connected to the DUT --
  // see assign block below. The .dummy(1'b1) drives the wait_for_reset
  // sentinel high so the bench's wait_for_reset() returns immediately.
  HMAC_rst_if  hmac_rst_agent_bus(
     // pragma uvmf custom hmac_rst_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom hmac_rst_agent_bus_connections end
     );
  HMAC_rst_monitor_bfm  hmac_rst_agent_mon_bfm(hmac_rst_agent_bus.monitor_port);
  HMAC_rst_driver_bfm  hmac_rst_agent_drv_bfm(hmac_rst_agent_bus.initiator_port);

  // pragma uvmf custom dut_instantiation begin
  // AHB Clock/reset -- drive QVIP RESET directly from bit rst (abr pattern).
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.default_clk_gen_CLK     = clk;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.default_reset_gen_RESET = rst;

  // KV ports tied off at unit level (abr/ecc/sha512 convention).
  // KV interactions are validated by firmware test_suites running the
  // full caliptra_top.
  import kv_defines_pkg::*;
  var kv_rd_resp_t [1:0] kv_rd_resp_stub = '{default:0};
  var kv_wr_resp_t       kv_wr_resp_stub = '{default:0};

  hmac_ctrl #(
      .AHB_ADDR_WIDTH(32),
      .AHB_DATA_WIDTH(64)
  ) dut (
      .clk          (clk),
      // abr-style: reset_n + cptra_pwrgood driven DIRECTLY from bit rst
      // (NOT from hmac_rst_agent_bus). Bit rst goes high at 200ns and
      // stays there unless an otf_reset test triggers ev_rst.
      .reset_n      (rst),
      .cptra_pwrgood(rst),

      .cptra_csr_hmac_key('0), //TODO drive from a CSR-mode sequence

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

      .kv_read    (),
      .kv_write   (),
      .kv_rd_resp (kv_rd_resp_stub),
      .kv_wr_resp (kv_wr_resp_stub),

      .busy_o     (),
      .error_intr (),
      .notif_intr (),

      .ocp_lock_in_progress           (1'b0),
      // abr-style: tie debug_scan low here (no fuzzing). The hmac_rst
      // monitor's any_signal_changed() still tracks bus values, which
      // is fine since bus.debugUnlock_or_scan_mode_switch is hi-z and
      // never changes.
      .debugUnlock_or_scan_mode_switch('0)
  );

  // QVIP AHB master defaults (not driven by hmac_ctrl).
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

  hmac_ctrl_cov_bind i_hmac_ctrl_cov_bind();
  // pragma uvmf custom dut_instantiation end

  initial begin      // tbx vif_binding_block 
    import uvm_pkg::uvm_config_db;
    // The monitor_bfm and driver_bfm for each interface is placed into the uvm_config_db.
    // They are placed into the uvm_config_db using the string names defined in the parameters package.
    // The string names are passed to the agent configurations by test_top through the top level configuration.
    // They are retrieved by the agents configuration class for use by the agent.
    uvm_config_db #( virtual HMAC_rst_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , hmac_rst_agent_BFM , hmac_rst_agent_mon_bfm ); 
    uvm_config_db #( virtual HMAC_rst_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , hmac_rst_agent_BFM , hmac_rst_agent_drv_bfm  );
  end

endmodule

// pragma uvmf custom external begin
// pragma uvmf custom external end

