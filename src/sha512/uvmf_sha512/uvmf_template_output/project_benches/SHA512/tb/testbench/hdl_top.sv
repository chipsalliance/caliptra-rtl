//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
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

import SHA512_parameters_pkg::*;
import uvmf_base_pkg_hdl::*;

  // pragma attribute hdl_top partition_module_xrtl                                            
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
  bit rst;
  // Instantiate a rst driver
  // tbx clkgen
  initial begin
    rst = 0; 
    #200ns;
    rst =  1; 
  end
// pragma uvmf custom reset_generator end

  // pragma uvmf custom module_item_additional begin
  wire read_flag_monitor_top;
  // pragma uvmf custom module_item_additional end

  // Instantiate the signal bundle, monitor bfm and driver bfm for each interface.
  // The signal bundle, _if, contains signals to be connected to the DUT.
  // The monitor, monitor_bfm, observes the bus, _if, and captures transactions.
  // The driver, driver_bfm, drives transactions onto the bus, _if.
  SHA512_in_if  SHA512_in_agent_bus(
     // pragma uvmf custom SHA512_in_agent_bus_connections begin
     .clk(clk), .rst(rst), .transaction_flag_in_monitor(read_flag_monitor_top)
     // pragma uvmf custom SHA512_in_agent_bus_connections end
     );
  SHA512_out_if  SHA512_out_agent_bus(
     // pragma uvmf custom SHA512_out_agent_bus_connections begin
     .clk(clk), .rst(rst), .read_flag_monitor(read_flag_monitor_top)
     // pragma uvmf custom SHA512_out_agent_bus_connections end
     );
  SHA512_in_monitor_bfm  SHA512_in_agent_mon_bfm(SHA512_in_agent_bus.monitor_port);
  SHA512_out_monitor_bfm  SHA512_out_agent_mon_bfm(SHA512_out_agent_bus.monitor_port);
  SHA512_in_driver_bfm  SHA512_in_agent_drv_bfm(SHA512_in_agent_bus.initiator_port);

  // pragma uvmf custom dut_instantiation begin
  // UVMF_CHANGE_ME : Add DUT and connect to signals in _bus interfaces listed above
  // Instantiate your DUT here
  // These DUT's instantiated to show verilog and vhdl instantiation
  sha512_ctrl #(
             .AHB_DATA_WIDTH(32),
             .AHB_ADDR_WIDTH(32)
            )
            dut (
             .clk(SHA512_in_agent_bus.clk),
             .reset_n(SHA512_in_agent_bus.rst),

             .haddr_i(SHA512_in_agent_bus.hadrr),
             .hwdata_i(SHA512_in_agent_bus.hwdata),
             .hsel_i(SHA512_in_agent_bus.hsel),
             .hwrite_i(SHA512_in_agent_bus.hwrite),
             .hready_i(SHA512_in_agent_bus.hready),
             .htrans_i(SHA512_in_agent_bus.htrans),
             .hsize_i(SHA512_in_agent_bus.hsize),

             .hresp_o(SHA512_out_agent_bus.hresp),
             .hreadyout_o(SHA512_out_agent_bus.hreadyout),
             .hrdata_o(SHA512_out_agent_bus.hrdata),
             .kv_read   (),
             .kv_write  (),
             .kv_rd_resp(),
             .kv_wr_resp(),
             .pv_read   (),
             .pv_write  (),
             .pv_rd_resp(),
             .pv_wr_resp(),
             .pcr_signing_hash(),
             .error_intr(),
             .notif_intr(),
             .debugUnlock_or_scan_mode_switch()
            );
  // pragma uvmf custom dut_instantiation end

  initial begin      // tbx vif_binding_block 
    import uvm_pkg::uvm_config_db;
    // The monitor_bfm and driver_bfm for each interface is placed into the uvm_config_db.
    // They are placed into the uvm_config_db using the string names defined in the parameters package.
    // The string names are passed to the agent configurations by test_top through the top level configuration.
    // They are retrieved by the agents configuration class for use by the agent.
    uvm_config_db #( virtual SHA512_in_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , SHA512_in_agent_BFM , SHA512_in_agent_mon_bfm ); 
    uvm_config_db #( virtual SHA512_out_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , SHA512_out_agent_BFM , SHA512_out_agent_mon_bfm ); 
    uvm_config_db #( virtual SHA512_in_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , SHA512_in_agent_BFM , SHA512_in_agent_drv_bfm  );
  end

endmodule

// pragma uvmf custom external begin
// pragma uvmf custom external end

