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
// DESCRIPTION: This interface contains the fuse_ctrl_in_if interface signals.
//      It is instantiated once per fuse_ctrl_in_if bus.  Bus Functional Models, 
//      BFM's named fuse_ctrl_in_if_driver_bfm, are used to drive signals on the bus.
//      BFM's named fuse_ctrl_in_if_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(fuse_ctrl_in_if_bus.edn_i), // Agent output 
// .dut_signal_port(fuse_ctrl_in_if_bus.alert_rx_i), // Agent output 
// .dut_signal_port(fuse_ctrl_in_if_bus.obs_ctrl_i), // Agent output 
// .dut_signal_port(fuse_ctrl_in_if_bus.otp_ast_pwr_seq_h_i), // Agent output 
// .dut_signal_port(fuse_ctrl_in_if_bus.otp_ext_voltage_h_io), // Agent output 
// .dut_signal_port(fuse_ctrl_in_if_bus.scan_en_i), // Agent output 
// .dut_signal_port(fuse_ctrl_in_if_bus.scan_rst_ni), // Agent output 
// .dut_signal_port(fuse_ctrl_in_if_bus.scanmode_i), // Agent output 

import uvmf_base_pkg_hdl::*;
import fuse_ctrl_in_if_pkg_hdl::*;

interface  fuse_ctrl_in_if_if #(
  int AlertSyncOn = 3,
  lfsr_seed_t RndConstLfrSeed = RndConstLfsrSeedDefault,
  lsfr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault,
  string MemInitFile = 
  )


  (
  input tri clk_i, 
  input tri rst_ni,
  inout tri [$bits(edn_pkg::edn_req_t)-1:0] edn_i,
  inout tri [NumAlerts * $bits(caliptra_prim_alert_pkg::alert_rx_t)-1:0] alert_rx_i,
  inout tri [$bits(ast_pkg::ast_obs_ctrl_t)-1:0] obs_ctrl_i,
  inout tri [$bits(otp_ast_req_t)-1:0] otp_ast_pwr_seq_h_i,
  inout tri  otp_ext_voltage_h_io,
  inout tri  scan_en_i,
  inout tri  scan_rst_ni,
  inout tri  scanmode_i
  );

modport monitor_port 
  (
  input clk_i,
  input rst_ni,
  input edn_i,
  input alert_rx_i,
  input obs_ctrl_i,
  input otp_ast_pwr_seq_h_i,
  input otp_ext_voltage_h_io,
  input scan_en_i,
  input scan_rst_ni,
  input scanmode_i
  );

modport initiator_port 
  (
  input clk_i,
  input rst_ni,
  output edn_i,
  output alert_rx_i,
  output obs_ctrl_i,
  output otp_ast_pwr_seq_h_i,
  output otp_ext_voltage_h_io,
  output scan_en_i,
  output scan_rst_ni,
  output scanmode_i
  );

modport responder_port 
  (
  input clk_i,
  input rst_ni,  
  input edn_i,
  input alert_rx_i,
  input obs_ctrl_i,
  input otp_ast_pwr_seq_h_i,
  input otp_ext_voltage_h_io,
  input scan_en_i,
  input scan_rst_ni,
  input scanmode_i
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

