//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This interface contains the ECC_out interface signals.
//      It is instantiated once per ECC_out bus.  Bus Functional Models, 
//      BFM's named ECC_out_driver_bfm, are used to drive signals on the bus.
//      BFM's named ECC_out_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(ECC_out_bus.hresp), // Agent input 
// .dut_signal_port(ECC_out_bus.hreadyout), // Agent input 
// .dut_signal_port(ECC_out_bus.hrdata), // Agent input 
// .dut_signal_port(ECC_out_bus.transaction_flag_out_monitor), // Agent input 
// .dut_signal_port(ECC_out_bus.test), // Agent output 
// .dut_signal_port(ECC_out_bus.op), // Agent output 

import uvmf_base_pkg_hdl::*;
import ECC_out_pkg_hdl::*;

interface  ECC_out_if #(
  int AHB_ADDR_WIDTH = 32,
  int AHB_DATA_WIDTH = 32,
  int OUTPUT_TEXT_WIDTH = 384
  )


  (
  input tri clk, 
  input tri rst_n,
  inout tri  hresp,
  inout tri  hreadyout,
  inout tri [AHB_DATA_WIDTH-1:0] hrdata,
  inout tri  transaction_flag_out_monitor,
  inout tri [2:0] test,
  inout tri [2:0] op
  );

modport monitor_port 
  (
  input clk,
  input rst_n,
  input hresp,
  input hreadyout,
  input hrdata,
  input transaction_flag_out_monitor,
  input test,
  input op
  );

modport initiator_port 
  (
  input clk,
  input rst_n,
  input hresp,
  input hreadyout,
  input hrdata,
  input transaction_flag_out_monitor,
  output test,
  output op
  );

modport responder_port 
  (
  input clk,
  input rst_n,  
  output hresp,
  output hreadyout,
  output hrdata,
  output transaction_flag_out_monitor,
  input test,
  input op
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

