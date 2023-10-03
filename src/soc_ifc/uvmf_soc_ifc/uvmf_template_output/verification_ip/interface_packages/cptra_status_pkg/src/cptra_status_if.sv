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
// DESCRIPTION: This interface contains the cptra_status interface signals.
//      It is instantiated once per cptra_status bus.  Bus Functional Models, 
//      BFM's named cptra_status_driver_bfm, are used to drive signals on the bus.
//      BFM's named cptra_status_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(cptra_status_bus.cptra_noncore_rst_b), // Agent output 
// .dut_signal_port(cptra_status_bus.cptra_uc_rst_b), // Agent output 
// .dut_signal_port(cptra_status_bus.fw_update_rst_window), // Agent output 
// .dut_signal_port(cptra_status_bus.cptra_obf_key_reg), // Agent output 
// .dut_signal_port(cptra_status_bus.obf_field_entropy), // Agent output 
// .dut_signal_port(cptra_status_bus.obf_uds_seed), // Agent output 
// .dut_signal_port(cptra_status_bus.soc_ifc_error_intr), // Agent output 
// .dut_signal_port(cptra_status_bus.soc_ifc_notif_intr), // Agent output 
// .dut_signal_port(cptra_status_bus.sha_error_intr), // Agent output 
// .dut_signal_port(cptra_status_bus.sha_notif_intr), // Agent output 
// .dut_signal_port(cptra_status_bus.timer_intr), // Agent output 
// .dut_signal_port(cptra_status_bus.nmi_vector), // Agent output 
// .dut_signal_port(cptra_status_bus.nmi_intr), // Agent output 
// .dut_signal_port(cptra_status_bus.iccm_lock), // Agent output 

import uvmf_base_pkg_hdl::*;
import cptra_status_pkg_hdl::*;

interface  cptra_status_if 

  (
  input tri clk, 
  input tri dummy,
  inout tri  cptra_noncore_rst_b,
  inout tri  cptra_uc_rst_b,
  inout tri  fw_update_rst_window,
  inout tri [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key_reg,
  inout tri [`CLP_OBF_FE_DWORDS-1:0][31:0] obf_field_entropy,
  inout tri [`CLP_OBF_UDS_DWORDS-1:0][31:0] obf_uds_seed,
  inout tri  soc_ifc_error_intr,
  inout tri  soc_ifc_notif_intr,
  inout tri  sha_error_intr,
  inout tri  sha_notif_intr,
  inout tri  timer_intr,
  inout tri [31:0] nmi_vector,
  inout tri  nmi_intr,
  inout tri  iccm_lock
  );

modport monitor_port 
  (
  input clk,
  input dummy,
  input cptra_noncore_rst_b,
  input cptra_uc_rst_b,
  input fw_update_rst_window,
  input cptra_obf_key_reg,
  input obf_field_entropy,
  input obf_uds_seed,
  input soc_ifc_error_intr,
  input soc_ifc_notif_intr,
  input sha_error_intr,
  input sha_notif_intr,
  input timer_intr,
  input nmi_vector,
  input nmi_intr,
  input iccm_lock
  );

modport initiator_port 
  (
  input clk,
  input dummy,
  output cptra_noncore_rst_b,
  output cptra_uc_rst_b,
  output fw_update_rst_window,
  output cptra_obf_key_reg,
  output obf_field_entropy,
  output obf_uds_seed,
  output soc_ifc_error_intr,
  output soc_ifc_notif_intr,
  output sha_error_intr,
  output sha_notif_intr,
  output timer_intr,
  output nmi_vector,
  output nmi_intr,
  output iccm_lock
  );

modport responder_port 
  (
  input clk,
  input dummy,  
  input cptra_noncore_rst_b,
  input cptra_uc_rst_b,
  input fw_update_rst_window,
  input cptra_obf_key_reg,
  input obf_field_entropy,
  input obf_uds_seed,
  input soc_ifc_error_intr,
  input soc_ifc_notif_intr,
  input sha_error_intr,
  input sha_notif_intr,
  input timer_intr,
  input nmi_vector,
  input nmi_intr,
  input iccm_lock
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

