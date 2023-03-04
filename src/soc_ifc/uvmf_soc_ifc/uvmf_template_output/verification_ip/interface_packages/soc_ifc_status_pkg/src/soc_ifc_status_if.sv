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
// .dut_signal_port(soc_ifc_status_bus.ready_for_fuses), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.ready_for_fw_push), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.ready_for_runtime), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.mailbox_data_avail), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.mailbox_flow_done), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.cptra_error_fatal), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.cptra_error_non_fatal), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.trng_req), // Agent output 
// .dut_signal_port(soc_ifc_status_bus.generic_output_wires), // Agent output 

import uvmf_base_pkg_hdl::*;
import soc_ifc_status_pkg_hdl::*;

interface  soc_ifc_status_if 

  (
  input tri clk, 
  input tri dummy,
  inout tri  ready_for_fuses,
  inout tri  ready_for_fw_push,
  inout tri  ready_for_runtime,
  inout tri  mailbox_data_avail,
  inout tri  mailbox_flow_done,
  inout tri  cptra_error_fatal,
  inout tri  cptra_error_non_fatal,
  inout tri  trng_req,
  inout tri [63:0] generic_output_wires
  );

modport monitor_port 
  (
  input clk,
  input dummy,
  input ready_for_fuses,
  input ready_for_fw_push,
  input ready_for_runtime,
  input mailbox_data_avail,
  input mailbox_flow_done,
  input cptra_error_fatal,
  input cptra_error_non_fatal,
  input trng_req,
  input generic_output_wires
  );

modport initiator_port 
  (
  input clk,
  input dummy,
  output ready_for_fuses,
  output ready_for_fw_push,
  output ready_for_runtime,
  output mailbox_data_avail,
  output mailbox_flow_done,
  output cptra_error_fatal,
  output cptra_error_non_fatal,
  output trng_req,
  output generic_output_wires
  );

modport responder_port 
  (
  input clk,
  input dummy,  
  input ready_for_fuses,
  input ready_for_fw_push,
  input ready_for_runtime,
  input mailbox_data_avail,
  input mailbox_flow_done,
  input cptra_error_fatal,
  input cptra_error_non_fatal,
  input trng_req,
  input generic_output_wires
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

