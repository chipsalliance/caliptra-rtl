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
// DESCRIPTION: This interface contains the pv_rst interface signals.
//      It is instantiated once per pv_rst bus.  Bus Functional Models, 
//      BFM's named pv_rst_driver_bfm, are used to drive signals on the bus.
//      BFM's named pv_rst_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(pv_rst_bus.cptra_pwrgood), // Agent output 
// .dut_signal_port(pv_rst_bus.rst_b), // Agent output 

import uvmf_base_pkg_hdl::*;
import pv_rst_pkg_hdl::*;

interface  pv_rst_if 

  (
  input tri clk, 
  input tri dummy,
  inout tri  cptra_pwrgood,
  inout tri  rst_b
  );

modport monitor_port 
  (
  input clk,
  input dummy,
  input cptra_pwrgood,
  input rst_b
  );

modport initiator_port 
  (
  input clk,
  input dummy,
  output cptra_pwrgood,
  output rst_b
  );

modport responder_port 
  (
  input clk,
  input dummy,  
  input cptra_pwrgood,
  input rst_b
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

