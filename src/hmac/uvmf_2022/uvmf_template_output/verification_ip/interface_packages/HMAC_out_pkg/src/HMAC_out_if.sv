//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This interface contains the HMAC_out interface signals.
//      It is instantiated once per HMAC_out bus.  Bus Functional Models, 
//      BFM's named HMAC_out_driver_bfm, are used to drive signals on the bus.
//      BFM's named HMAC_out_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(HMAC_out_bus.hresp), // Agent input 
// .dut_signal_port(HMAC_out_bus.hreadyout), // Agent input 
// .dut_signal_port(HMAC_out_bus.hrdata), // Agent input 
// .dut_signal_port(HMAC_out_bus.transaction_flag_in_monitor), // Agent input 

import uvmf_base_pkg_hdl::*;
import HMAC_out_pkg_hdl::*;

interface  HMAC_out_if #(
  int AHB_DATA_WIDTH = 32,
  int AHB_ADDR_WIDTH = 32,
  int OUTPUT_TEXT_WIDTH = 384,
  bit BYPASS_HSEL = 0
  )


  (
  input tri clk, 
  input tri rst,
  inout tri  hresp,
  inout tri  hreadyout,
  inout tri [AHB_DATA_WIDTH-1:0] hrdata,
  inout tri  transaction_flag_in_monitor
  );

modport monitor_port 
  (
  input clk,
  input rst,
  input hresp,
  input hreadyout,
  input hrdata,
  input transaction_flag_in_monitor
  );

modport initiator_port 
  (
  input clk,
  input rst,
  input hresp,
  input hreadyout,
  input hrdata,
  input transaction_flag_in_monitor
  );

modport responder_port 
  (
  input clk,
  input rst,  
  output hresp,
  output hreadyout,
  output hrdata,
  output transaction_flag_in_monitor
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

