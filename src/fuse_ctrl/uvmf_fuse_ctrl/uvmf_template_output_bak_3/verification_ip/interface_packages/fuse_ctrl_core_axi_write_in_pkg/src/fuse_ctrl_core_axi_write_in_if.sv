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
// DESCRIPTION: This interface contains the fuse_ctrl_core_axi_write_in interface signals.
//      It is instantiated once per fuse_ctrl_core_axi_write_in bus.  Bus Functional Models, 
//      BFM's named fuse_ctrl_core_axi_write_in_driver_bfm, are used to drive signals on the bus.
//      BFM's named fuse_ctrl_core_axi_write_in_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(fuse_ctrl_core_axi_write_in_bus.awaddr), // Agent output 
// .dut_signal_port(fuse_ctrl_core_axi_write_in_bus.awburst), // Agent output 
// .dut_signal_port(fuse_ctrl_core_axi_write_in_bus.awsize), // Agent output 
// .dut_signal_port(fuse_ctrl_core_axi_write_in_bus.awlen), // Agent output 
// .dut_signal_port(fuse_ctrl_core_axi_write_in_bus.awuser), // Agent output 
// .dut_signal_port(fuse_ctrl_core_axi_write_in_bus.awid), // Agent output 
// .dut_signal_port(fuse_ctrl_core_axi_write_in_bus.awlock), // Agent output 
// .dut_signal_port(fuse_ctrl_core_axi_write_in_bus.awvalid), // Agent output 
// .dut_signal_port(fuse_ctrl_core_axi_write_in_bus.wdata), // Agent output 
// .dut_signal_port(fuse_ctrl_core_axi_write_in_bus.wstrb), // Agent output 
// .dut_signal_port(fuse_ctrl_core_axi_write_in_bus.wvalid), // Agent output 
// .dut_signal_port(fuse_ctrl_core_axi_write_in_bus.wlast), // Agent output 
// .dut_signal_port(fuse_ctrl_core_axi_write_in_bus.bready), // Agent output 

import uvmf_base_pkg_hdl::*;
import fuse_ctrl_core_axi_write_in_pkg_hdl::*;

interface  fuse_ctrl_core_axi_write_in_if #(
  int AW = 32,
  int DW = 32,
  int IW = 3,
  int UW = 32
  )


  (
  input tri clk_i, 
  input tri rst_ni,
  inout tri [AW-1:0] awaddr,
  inout tri [$bits(axi_pkg::axi_burst_e)-1:0] awburst,
  inout tri [2:0] awsize,
  inout tri [7:0] awlen,
  inout tri [UW-1:0] awuser,
  inout tri [UW-1:0] awid,
  inout tri  awlock,
  inout tri  awvalid,
  inout tri [DW-1:0] wdata,
  inout tri [DW/8-1:0] wstrb,
  inout tri  wvalid,
  inout tri  wlast,
  inout tri  bready
  );

modport monitor_port 
  (
  input clk_i,
  input rst_ni,
  input awaddr,
  input awburst,
  input awsize,
  input awlen,
  input awuser,
  input awid,
  input awlock,
  input awvalid,
  input wdata,
  input wstrb,
  input wvalid,
  input wlast,
  input bready
  );

modport initiator_port 
  (
  input clk_i,
  input rst_ni,
  output awaddr,
  output awburst,
  output awsize,
  output awlen,
  output awuser,
  output awid,
  output awlock,
  output awvalid,
  output wdata,
  output wstrb,
  output wvalid,
  output wlast,
  output bready
  );

modport responder_port 
  (
  input clk_i,
  input rst_ni,  
  input awaddr,
  input awburst,
  input awsize,
  input awlen,
  input awuser,
  input awid,
  input awlock,
  input awvalid,
  input wdata,
  input wstrb,
  input wvalid,
  input wlast,
  input bready
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

