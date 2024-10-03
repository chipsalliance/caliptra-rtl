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
// DESCRIPTION: This interface contains the fuse_ctrl_prim_axi_read_in interface signals.
//      It is instantiated once per fuse_ctrl_prim_axi_read_in bus.  Bus Functional Models, 
//      BFM's named fuse_ctrl_prim_axi_read_in_driver_bfm, are used to drive signals on the bus.
//      BFM's named fuse_ctrl_prim_axi_read_in_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(fuse_ctrl_prim_axi_read_in_bus.araddr), // Agent output 
// .dut_signal_port(fuse_ctrl_prim_axi_read_in_bus.arburst), // Agent output 
// .dut_signal_port(fuse_ctrl_prim_axi_read_in_bus.arsize), // Agent output 
// .dut_signal_port(fuse_ctrl_prim_axi_read_in_bus.arlen), // Agent output 
// .dut_signal_port(fuse_ctrl_prim_axi_read_in_bus.aruser), // Agent output 
// .dut_signal_port(fuse_ctrl_prim_axi_read_in_bus.arid), // Agent output 
// .dut_signal_port(fuse_ctrl_prim_axi_read_in_bus.arlock), // Agent output 
// .dut_signal_port(fuse_ctrl_prim_axi_read_in_bus.arvalid), // Agent output 
// .dut_signal_port(fuse_ctrl_prim_axi_read_in_bus.rready), // Agent output 

import uvmf_base_pkg_hdl::*;
import fuse_ctrl_prim_axi_read_in_pkg_hdl::*;

interface  fuse_ctrl_prim_axi_read_in_if #(
  int AW = 32,
  int DW = 32,
  int IW = 3,
  int UW = 32
  )


  (
  input tri clk_i, 
  input tri rst_ni,
  inout tri [AW-1:0] araddr,
  inout tri [$bits(axi_pkg::axi_burst_e)-1:0] arburst,
  inout tri [2:0] arsize,
  inout tri [7:0] arlen,
  inout tri [UW-1:0] aruser,
  inout tri [IW-1:0] arid,
  inout tri  arlock,
  inout tri  arvalid,
  inout tri  rready
  );

modport monitor_port 
  (
  input clk_i,
  input rst_ni,
  input araddr,
  input arburst,
  input arsize,
  input arlen,
  input aruser,
  input arid,
  input arlock,
  input arvalid,
  input rready
  );

modport initiator_port 
  (
  input clk_i,
  input rst_ni,
  output araddr,
  output arburst,
  output arsize,
  output arlen,
  output aruser,
  output arid,
  output arlock,
  output arvalid,
  output rready
  );

modport responder_port 
  (
  input clk_i,
  input rst_ni,  
  input araddr,
  input arburst,
  input arsize,
  input arlen,
  input aruser,
  input arid,
  input arlock,
  input arvalid,
  input rready
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

