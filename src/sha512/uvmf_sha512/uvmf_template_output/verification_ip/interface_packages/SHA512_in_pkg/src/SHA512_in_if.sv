//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This interface contains the SHA512_in interface signals.
//      It is instantiated once per SHA512_in bus.  Bus Functional Models, 
//      BFM's named SHA512_in_driver_bfm, are used to drive signals on the bus.
//      BFM's named SHA512_in_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(SHA512_in_bus.sha512_rst), // Agent output 
// .dut_signal_port(SHA512_in_bus.hadrr), // Agent output 
// .dut_signal_port(SHA512_in_bus.hwdata), // Agent output 
// .dut_signal_port(SHA512_in_bus.hsel), // Agent output 
// .dut_signal_port(SHA512_in_bus.hwrite), // Agent output 
// .dut_signal_port(SHA512_in_bus.hready), // Agent output 
// .dut_signal_port(SHA512_in_bus.htrans), // Agent output 
// .dut_signal_port(SHA512_in_bus.hsize), // Agent output 
// .dut_signal_port(SHA512_in_bus.transaction_flag_in_monitor), // Agent output 
// .dut_signal_port(SHA512_in_bus.op), // Agent output 
// .dut_signal_port(SHA512_in_bus.test_case_sel), // Agent output 

import uvmf_base_pkg_hdl::*;
import SHA512_in_pkg_hdl::*;

interface  SHA512_in_if #(
  int AHB_DATA_WIDTH = 32,
  int AHB_ADDR_WIDTH = 32,
  bit BYPASS_HSEL = 0
  )


  (
  input tri clk, 
  input tri rst,
  inout tri  sha512_rst,
  inout tri [AHB_ADDR_WIDTH-1:0] hadrr,
  inout tri [AHB_DATA_WIDTH-1:0] hwdata,
  inout tri  hsel,
  inout tri  hwrite,
  inout tri  hready,
  inout tri [1:0] htrans,
  inout tri [2:0] hsize,
  inout tri  transaction_flag_in_monitor,
  inout tri [2:0] op,
  inout tri [7:0] test_case_sel
  );

modport monitor_port 
  (
  input clk,
  input rst,
  input sha512_rst,
  input hadrr,
  input hwdata,
  input hsel,
  input hwrite,
  input hready,
  input htrans,
  input hsize,
  input transaction_flag_in_monitor,
  input op,
  input test_case_sel
  );

modport initiator_port 
  (
  input clk,
  input rst,
  output sha512_rst,
  output hadrr,
  output hwdata,
  output hsel,
  output hwrite,
  output hready,
  output htrans,
  output hsize,
  output transaction_flag_in_monitor,
  output op,
  output test_case_sel
  );

modport responder_port 
  (
  input clk,
  input rst,  
  input sha512_rst,
  input hadrr,
  input hwdata,
  input hsel,
  input hwrite,
  input hready,
  input htrans,
  input hsize,
  input transaction_flag_in_monitor,
  input op,
  input test_case_sel
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

