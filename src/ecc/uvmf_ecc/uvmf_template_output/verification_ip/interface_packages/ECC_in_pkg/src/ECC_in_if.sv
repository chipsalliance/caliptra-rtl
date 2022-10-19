//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This interface contains the ECC_in interface signals.
//      It is instantiated once per ECC_in bus.  Bus Functional Models, 
//      BFM's named ECC_in_driver_bfm, are used to drive signals on the bus.
//      BFM's named ECC_in_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(ECC_in_bus.ecc_rst_n), // Agent output 
// .dut_signal_port(ECC_in_bus.haddr), // Agent output 
// .dut_signal_port(ECC_in_bus.hwdata), // Agent output 
// .dut_signal_port(ECC_in_bus.hsel), // Agent output 
// .dut_signal_port(ECC_in_bus.hwrite), // Agent output 
// .dut_signal_port(ECC_in_bus.hready), // Agent output 
// .dut_signal_port(ECC_in_bus.htrans), // Agent output 
// .dut_signal_port(ECC_in_bus.hsize), // Agent output 
// .dut_signal_port(ECC_in_bus.hrdata), // Agent input 
// .dut_signal_port(ECC_in_bus.hreadyout), // Agent input 
// .dut_signal_port(ECC_in_bus.transaction_flag_out_monitor), // Agent output 
// .dut_signal_port(ECC_in_bus.test), // Agent output 
// .dut_signal_port(ECC_in_bus.op), // Agent output 
// .dut_signal_port(ECC_in_bus.test_case_sel), // Agent output 

import uvmf_base_pkg_hdl::*;
import ECC_in_pkg_hdl::*;

interface  ECC_in_if #(
  int AHB_ADDR_WIDTH = 32,
  int AHB_DATA_WIDTH = 32
  )


  (
  input tri clk, 
  input tri rst_n,
  inout tri  ecc_rst_n,
  inout tri [AHB_ADDR_WIDTH-1:0] haddr,
  inout tri [AHB_DATA_WIDTH-1:0] hwdata,
  inout tri  hsel,
  inout tri  hwrite,
  inout tri  hready,
  inout tri [1:0] htrans,
  inout tri [2:0] hsize,
  inout tri [AHB_DATA_WIDTH-1:0] hrdata,
  inout tri  hreadyout,
  inout tri  transaction_flag_out_monitor,
  inout tri [2:0] test,
  inout tri [1:0] op,
  inout tri [7:0] test_case_sel
  );

modport monitor_port 
  (
  input clk,
  input rst_n,
  input ecc_rst_n,
  input haddr,
  input hwdata,
  input hsel,
  input hwrite,
  input hready,
  input htrans,
  input hsize,
  input hrdata,
  input hreadyout,
  input transaction_flag_out_monitor,
  input test,
  input op,
  input test_case_sel
  );

modport initiator_port 
  (
  input clk,
  input rst_n,
  output ecc_rst_n,
  output haddr,
  output hwdata,
  output hsel,
  output hwrite,
  output hready,
  output htrans,
  output hsize,
  input hrdata,
  input hreadyout,
  output transaction_flag_out_monitor,
  output test,
  output op,
  output test_case_sel
  );

modport responder_port 
  (
  input clk,
  input rst_n,  
  input ecc_rst_n,
  input haddr,
  input hwdata,
  input hsel,
  input hwrite,
  input hready,
  input htrans,
  input hsize,
  output hrdata,
  output hreadyout,
  input transaction_flag_out_monitor,
  input test,
  input op,
  input test_case_sel
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

