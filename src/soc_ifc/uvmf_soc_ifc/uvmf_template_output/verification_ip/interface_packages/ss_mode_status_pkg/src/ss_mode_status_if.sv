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
// DESCRIPTION: This interface contains the ss_mode_status interface signals.
//      It is instantiated once per ss_mode_status bus.  Bus Functional Models, 
//      BFM's named ss_mode_status_driver_bfm, are used to drive signals on the bus.
//      BFM's named ss_mode_status_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(ss_mode_status_bus.cptra_ss_debug_intent), // Agent output 
// .dut_signal_port(ss_mode_status_bus.ss_dbg_manuf_enable), // Agent output 
// .dut_signal_port(ss_mode_status_bus.ss_soc_dbg_unlock_level), // Agent output 
// .dut_signal_port(ss_mode_status_bus.ss_generic_fw_exec_ctrl), // Agent output 

import uvmf_base_pkg_hdl::*;
import ss_mode_status_pkg_hdl::*;

interface  ss_mode_status_if 

  (
  input tri clk, 
  input tri dummy,
  inout tri  cptra_ss_debug_intent,
  inout tri  ss_dbg_manuf_enable,
  inout tri [63:0] ss_soc_dbg_unlock_level,
  inout tri [127:0] ss_generic_fw_exec_ctrl
  );

modport monitor_port 
  (
  input clk,
  input dummy,
  input cptra_ss_debug_intent,
  input ss_dbg_manuf_enable,
  input ss_soc_dbg_unlock_level,
  input ss_generic_fw_exec_ctrl
  );

modport initiator_port 
  (
  input clk,
  input dummy,
  output cptra_ss_debug_intent,
  output ss_dbg_manuf_enable,
  output ss_soc_dbg_unlock_level,
  output ss_generic_fw_exec_ctrl
  );

modport responder_port 
  (
  input clk,
  input dummy,  
  input cptra_ss_debug_intent,
  input ss_dbg_manuf_enable,
  input ss_soc_dbg_unlock_level,
  input ss_generic_fw_exec_ctrl
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

