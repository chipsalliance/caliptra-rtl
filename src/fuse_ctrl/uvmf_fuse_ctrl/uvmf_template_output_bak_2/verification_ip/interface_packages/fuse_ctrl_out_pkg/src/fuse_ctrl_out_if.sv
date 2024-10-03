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
// DESCRIPTION: This interface contains the fuse_ctrl_out interface signals.
//      It is instantiated once per fuse_ctrl_out bus.  Bus Functional Models, 
//      BFM's named fuse_ctrl_out_driver_bfm, are used to drive signals on the bus.
//      BFM's named fuse_ctrl_out_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(fuse_ctrl_out_bus.edn_o), // Agent input 
// .dut_signal_port(fuse_ctrl_out_bus.intr_otp_operation_done_o), // Agent input 
// .dut_signal_port(fuse_ctrl_out_bus.intr_otp_error_o), // Agent input 
// .dut_signal_port(fuse_ctrl_out_bus.alert_tx_o), // Agent input 
// .dut_signal_port(fuse_ctrl_out_bus.otp_obs_o), // Agent input 
// .dut_signal_port(fuse_ctrl_out_bus.otp_ast_pwr_seq_o), // Agent input 
// .dut_signal_port(fuse_ctrl_out_bus.pwr_otp_o), // Agent input 
// .dut_signal_port(fuse_ctrl_out_bus.otp_broadcast_o), // Agent input 
// .dut_signal_port(fuse_ctrl_out_bus.otp_ext_voltage_h_io), // Agent inout 
// .dut_signal_port(fuse_ctrl_out_bus.cio_test_o), // Agent input 
// .dut_signal_port(fuse_ctrl_out_bus.cio_test_en_o), // Agent input 

import uvmf_base_pkg_hdl::*;
import fuse_ctrl_out_pkg_hdl::*;

interface  fuse_ctrl_out_if #(
  int AlertSyncOn = 3,
  lfsr_seed_t RndConstLfrSeed = RndConstLfsrSeedDefault,
  lsfr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault,
  string MemInitFile = 
  )


  (
  input tri clk_i, 
  input tri rst_ni,
  inout tri [$bits(edn_pkg::edn_req_t)-1:0] edn_o,
  inout tri  intr_otp_operation_done_o,
  inout tri  intr_otp_error_o,
  inout tri [NumAlerts * $bits(caliptra_prim_alert_pkg::alert_tx_t)-1:0] alert_tx_o,
  inout tri [7:0] otp_obs_o,
  inout tri [$bits(caliptra_otp_ctrl_pkg::otp_ast_req_t)-1:0] otp_ast_pwr_seq_o,
  inout tri [$bits(pwrmgr_pkg::pwr_otp_rsp_t)-1:0] pwr_otp_o,
  inout tri [$bits(otp_broadcast_t)-1:0] otp_broadcast_o,
  inout tri  otp_ext_voltage_h_io,
  inout tri [OtpTestVectWidth-1:0] cio_test_o,
  inout tri [OtpTestVectWidth-1:0] cio_test_en_o
  );

modport monitor_port 
  (
  input clk_i,
  input rst_ni,
  input edn_o,
  input intr_otp_operation_done_o,
  input intr_otp_error_o,
  input alert_tx_o,
  input otp_obs_o,
  input otp_ast_pwr_seq_o,
  input pwr_otp_o,
  input otp_broadcast_o,
  input otp_ext_voltage_h_io,
  input cio_test_o,
  input cio_test_en_o
  );

modport initiator_port 
  (
  input clk_i,
  input rst_ni,
  input edn_o,
  input intr_otp_operation_done_o,
  input intr_otp_error_o,
  input alert_tx_o,
  input otp_obs_o,
  input otp_ast_pwr_seq_o,
  input pwr_otp_o,
  input otp_broadcast_o,
  inout otp_ext_voltage_h_io,
  input cio_test_o,
  input cio_test_en_o
  );

modport responder_port 
  (
  input clk_i,
  input rst_ni,  
  output edn_o,
  output intr_otp_operation_done_o,
  output intr_otp_error_o,
  output alert_tx_o,
  output otp_obs_o,
  output otp_ast_pwr_seq_o,
  output pwr_otp_o,
  output otp_broadcast_o,
  inout otp_ext_voltage_h_io,
  output cio_test_o,
  output cio_test_en_o
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

