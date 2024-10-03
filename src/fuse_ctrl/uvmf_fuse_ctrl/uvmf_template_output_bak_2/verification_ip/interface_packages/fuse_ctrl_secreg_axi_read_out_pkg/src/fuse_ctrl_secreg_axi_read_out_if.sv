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
// DESCRIPTION: This interface contains the fuse_ctrl_secreg_axi_read_out interface signals.
//      It is instantiated once per fuse_ctrl_secreg_axi_read_out bus.  Bus Functional Models, 
//      BFM's named fuse_ctrl_secreg_axi_read_out_driver_bfm, are used to drive signals on the bus.
//      BFM's named fuse_ctrl_secreg_axi_read_out_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(fuse_ctrl_secreg_axi_read_out_bus.arready), // Agent input 
// .dut_signal_port(fuse_ctrl_secreg_axi_read_out_bus.rdata), // Agent input 
// .dut_signal_port(fuse_ctrl_secreg_axi_read_out_bus.rresp), // Agent input 
// .dut_signal_port(fuse_ctrl_secreg_axi_read_out_bus.rid), // Agent input 
// .dut_signal_port(fuse_ctrl_secreg_axi_read_out_bus.rlast), // Agent input 
// .dut_signal_port(fuse_ctrl_secreg_axi_read_out_bus.rvalid), // Agent input 

import uvmf_base_pkg_hdl::*;
import fuse_ctrl_secreg_axi_read_out_pkg_hdl::*;

interface  fuse_ctrl_secreg_axi_read_out_if #(
  int AW = 32,
  int DW = 32,
  int IW = 3,
  int UW = 32
  )


  (
  input tri clk_i, 
  input tri rst_ni,
  inout tri  arready,
  inout tri [DW-1:0] rdata,
  inout tri  rresp,
  inout tri  rid,
  inout tri  rlast,
  inout tri  rvalid
  );

modport monitor_port 
  (
  input clk_i,
  input rst_ni,
  input arready,
  input rdata,
  input rresp,
  input rid,
  input rlast,
  input rvalid
  );

modport initiator_port 
  (
  input clk_i,
  input rst_ni,
  input arready,
  input rdata,
  input rresp,
  input rid,
  input rlast,
  input rvalid
  );

modport responder_port 
  (
  input clk_i,
  input rst_ni,  
  output arready,
  output rdata,
  output rresp,
  output rid,
  output rlast,
  output rvalid
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

