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
// DESCRIPTION: This interface contains the soc_ifc_status interface signals.
//      It is instantiated once per soc_ifc_status bus.  Bus Functional Models, 
//      BFM's named soc_ifc_status_driver_bfm, are used to drive signals on the bus.
//      BFM's named soc_ifc_status_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(soc_ifc_status_bus.cptra_noncore_rst_b), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.cptra_uc_rst_b), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.ready_for_fuses), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.ready_for_fw_push), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.ready_for_runtime), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.mailbox_data_avail), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.mailbox_flow_done), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.generic_output_wires), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.cptra_obf_key_reg), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.obf_field_entropy), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.obf_uds_seed), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.soc_ifc_error_intr), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.soc_ifc_notif_intr), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.sha_error_intr), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.sha_notif_intr), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.iccm_lock), // Agent output 

import uvmf_base_pkg_hdl::*;
import soc_ifc_status_pkg_hdl::*;

interface  soc_ifc_status_if 

  (
  input tri clk, 
  input tri dummy,
  inout tri  cptra_noncore_rst_b,
  inout tri  cptra_uc_rst_b,
  inout tri  ready_for_fuses,
  inout tri  ready_for_fw_push,
  inout tri  ready_for_runtime,
  inout tri  mailbox_data_avail,
  inout tri  mailbox_flow_done,
  inout tri [63:0] generic_output_wires,
  inout tri [7:0][31:0] cptra_obf_key_reg,
  inout tri [31:0][31:0] obf_field_entropy,
  inout tri [11:0][31:0] obf_uds_seed,
  inout tri  soc_ifc_error_intr,
  inout tri  soc_ifc_notif_intr,
  inout tri  sha_error_intr,
  inout tri  sha_notif_intr,
  inout tri  iccm_lock
  );

modport monitor_port 
  (
  input clk,
  input dummy,
  input cptra_noncore_rst_b,
  input cptra_uc_rst_b,
  input ready_for_fuses,
  input ready_for_fw_push,
  input ready_for_runtime,
  input mailbox_data_avail,
  input mailbox_flow_done,
  input generic_output_wires,
  input cptra_obf_key_reg,
  input obf_field_entropy,
  input obf_uds_seed,
  input soc_ifc_error_intr,
  input soc_ifc_notif_intr,
  input sha_error_intr,
  input sha_notif_intr,
  input iccm_lock
  );

modport initiator_port 
  (
  input clk,
  input dummy,
  output cptra_noncore_rst_b,
  output cptra_uc_rst_b,
  output ready_for_fuses,
  output ready_for_fw_push,
  output ready_for_runtime,
  output mailbox_data_avail,
  output mailbox_flow_done,
  output generic_output_wires,
  output cptra_obf_key_reg,
  output obf_field_entropy,
  output obf_uds_seed,
  output soc_ifc_error_intr,
  output soc_ifc_notif_intr,
  output sha_error_intr,
  output sha_notif_intr,
  output iccm_lock
  );

modport responder_port 
  (
  input clk,
  input dummy,  
  input cptra_noncore_rst_b,
  input cptra_uc_rst_b,
  input ready_for_fuses,
  input ready_for_fw_push,
  input ready_for_runtime,
  input mailbox_data_avail,
  input mailbox_flow_done,
  input generic_output_wires,
  input cptra_obf_key_reg,
  input obf_field_entropy,
  input obf_uds_seed,
  input soc_ifc_error_intr,
  input soc_ifc_notif_intr,
  input sha_error_intr,
  input sha_notif_intr,
  input iccm_lock
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

