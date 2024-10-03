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
// DESCRIPTION: This interface contains the fuse_ctrl_core_axi_write_out interface signals.
//      It is instantiated once per fuse_ctrl_core_axi_write_out bus.  Bus Functional Models, 
//      BFM's named fuse_ctrl_core_axi_write_out_driver_bfm, are used to drive signals on the bus.
//      BFM's named fuse_ctrl_core_axi_write_out_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(fuse_ctrl_core_axi_write_out_bus.awready), // Agent input 
// .dut_signal_port(fuse_ctrl_core_axi_write_out_bus.wready), // Agent input 
// .dut_signal_port(fuse_ctrl_core_axi_write_out_bus.bresp), // Agent input 
// .dut_signal_port(fuse_ctrl_core_axi_write_out_bus.bid), // Agent input 
// .dut_signal_port(fuse_ctrl_core_axi_write_out_bus.bvalid), // Agent input 

import uvmf_base_pkg_hdl::*;
import fuse_ctrl_core_axi_write_out_pkg_hdl::*;

interface  fuse_ctrl_core_axi_write_out_if #(
  int AW = 32,
  int DW = 32,
  int IW = 3,
  int UW = 32
  )


  (
  input tri clk_i, 
  input tri rst_ni,
  inout tri  awready,
  inout tri  wready,
  inout tri [$bits(axi_pkg::axi_burst_e)-1:0] bresp,
  inout tri  bid,
  inout tri  bvalid
  );

modport monitor_port 
  (
  input clk_i,
  input rst_ni,
  input awready,
  input wready,
  input bresp,
  input bid,
  input bvalid
  );

modport initiator_port 
  (
  input clk_i,
  input rst_ni,
  input awready,
  input wready,
  input bresp,
  input bid,
  input bvalid
  );

modport responder_port 
  (
  input clk_i,
  input rst_ni,  
  output awready,
  output wready,
  output bresp,
  output bid,
  output bvalid
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

