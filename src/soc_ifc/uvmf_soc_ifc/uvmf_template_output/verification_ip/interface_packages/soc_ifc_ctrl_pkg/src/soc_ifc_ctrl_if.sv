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
// DESCRIPTION: This interface contains the soc_ifc_ctrl interface signals.
//      It is instantiated once per soc_ifc_ctrl bus.  Bus Functional Models, 
//      BFM's named soc_ifc_ctrl_driver_bfm, are used to drive signals on the bus.
//      BFM's named soc_ifc_ctrl_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(soc_ifc_ctrl_bus.cptra_pwrgood), // Agent output 
// .dut_signal_port(soc_ifc_ctrl_bus.cptra_rst_b), // Agent output 
// .dut_signal_port(soc_ifc_ctrl_bus.cptra_obf_key), // Agent output 
// .dut_signal_port(soc_ifc_ctrl_bus.cptra_obf_field_entropy_vld), // Agent output 
// .dut_signal_port(soc_ifc_ctrl_bus.cptra_obf_field_entropy), // Agent output 
// .dut_signal_port(soc_ifc_ctrl_bus.cptra_obf_uds_seed_vld), // Agent output 
// .dut_signal_port(soc_ifc_ctrl_bus.cptra_obf_uds_seed), // Agent output 
// .dut_signal_port(soc_ifc_ctrl_bus.security_state), // Agent output 
// .dut_signal_port(soc_ifc_ctrl_bus.BootFSM_BrkPoint), // Agent output 
// .dut_signal_port(soc_ifc_ctrl_bus.generic_input_wires), // Agent output 
// .dut_signal_port(soc_ifc_ctrl_bus.recovery_data_avail), // Agent output 
// .dut_signal_port(soc_ifc_ctrl_bus.recovery_image_activated), // Agent output 

import uvmf_base_pkg_hdl::*;
import soc_ifc_ctrl_pkg_hdl::*;

interface  soc_ifc_ctrl_if 

  (
  input tri clk, 
  input tri dummy,
  inout tri  cptra_pwrgood,
  inout tri  cptra_rst_b,
  inout tri [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key,
  inout tri  cptra_obf_field_entropy_vld,
  inout tri [`CLP_OBF_FE_DWORDS-1:0][31:0] cptra_obf_field_entropy,
  inout tri  cptra_obf_uds_seed_vld,
  inout tri [`CLP_OBF_UDS_DWORDS-1:0][31:0] cptra_obf_uds_seed,
  inout tri [2:0] security_state,
  inout tri  BootFSM_BrkPoint,
  inout tri [63:0] generic_input_wires,
  inout tri  recovery_data_avail,
  inout tri  recovery_image_activated
  );

modport monitor_port 
  (
  input clk,
  input dummy,
  input cptra_pwrgood,
  input cptra_rst_b,
  input cptra_obf_key,
  input cptra_obf_field_entropy_vld,
  input cptra_obf_field_entropy,
  input cptra_obf_uds_seed_vld,
  input cptra_obf_uds_seed,
  input security_state,
  input BootFSM_BrkPoint,
  input generic_input_wires,
  input recovery_data_avail,
  input recovery_image_activated
  );

modport initiator_port 
  (
  input clk,
  input dummy,
  output cptra_pwrgood,
  output cptra_rst_b,
  output cptra_obf_key,
  output cptra_obf_field_entropy_vld,
  output cptra_obf_field_entropy,
  output cptra_obf_uds_seed_vld,
  output cptra_obf_uds_seed,
  output security_state,
  output BootFSM_BrkPoint,
  output generic_input_wires,
  output recovery_data_avail,
  output recovery_image_activated
  );

modport responder_port 
  (
  input clk,
  input dummy,  
  input cptra_pwrgood,
  input cptra_rst_b,
  input cptra_obf_key,
  input cptra_obf_field_entropy_vld,
  input cptra_obf_field_entropy,
  input cptra_obf_uds_seed_vld,
  input cptra_obf_uds_seed,
  input security_state,
  input BootFSM_BrkPoint,
  input generic_input_wires,
  input recovery_data_avail,
  input recovery_image_activated
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

