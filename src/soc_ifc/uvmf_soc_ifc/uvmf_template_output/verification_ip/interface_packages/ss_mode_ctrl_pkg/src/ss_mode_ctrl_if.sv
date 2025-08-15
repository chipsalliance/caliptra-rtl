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
// DESCRIPTION: This interface contains the ss_mode_ctrl interface signals.
//      It is instantiated once per ss_mode_ctrl bus.  Bus Functional Models, 
//      BFM's named ss_mode_ctrl_driver_bfm, are used to drive signals on the bus.
//      BFM's named ss_mode_ctrl_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_caliptra_base_addr), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_mci_base_addr), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_recovery_ifc_base_addr), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_otp_fc_base_addr), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_uds_seed_base_addr), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_key_release_base_addr), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_key_release_key_size), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_num_of_prod_debug_unlock_auth_pk_hashes), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_strap_generic_0), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_strap_generic_1), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_strap_generic_2), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_strap_generic_3), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.strap_ss_caliptra_dma_axi_user), // Agent output 
// .dut_signal_port(ss_mode_ctrl_bus.ss_debug_intent), // Agent output 

import uvmf_base_pkg_hdl::*;
import ss_mode_ctrl_pkg_hdl::*;

interface  ss_mode_ctrl_if 

  (
  input tri clk, 
  input tri dummy,
  inout tri [63:0] strap_ss_caliptra_base_addr,
  inout tri [63:0] strap_ss_mci_base_addr,
  inout tri [63:0] strap_ss_recovery_ifc_base_addr,
  inout tri [63:0] strap_ss_external_staging_area_base_addr,
  inout tri [63:0] strap_ss_otp_fc_base_addr,
  inout tri [63:0] strap_ss_uds_seed_base_addr,
  inout tri [63:0] strap_ss_key_release_base_addr,
  inout tri [15:0] strap_ss_key_release_key_size,
  inout tri [31:0] strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset,
  inout tri [31:0] strap_ss_num_of_prod_debug_unlock_auth_pk_hashes,
  inout tri [31:0] strap_ss_strap_generic_0,
  inout tri [31:0] strap_ss_strap_generic_1,
  inout tri [31:0] strap_ss_strap_generic_2,
  inout tri [31:0] strap_ss_strap_generic_3,
  inout tri [31:0] strap_ss_caliptra_dma_axi_user,
  inout tri  ss_debug_intent
  );

modport monitor_port 
  (
  input clk,
  input dummy,
  input strap_ss_caliptra_base_addr,
  input strap_ss_mci_base_addr,
  input strap_ss_recovery_ifc_base_addr,
  input strap_ss_external_staging_area_base_addr,
  input strap_ss_otp_fc_base_addr,
  input strap_ss_uds_seed_base_addr,
  input strap_ss_key_release_base_addr,
  input strap_ss_key_release_key_size,
  input strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset,
  input strap_ss_num_of_prod_debug_unlock_auth_pk_hashes,
  input strap_ss_strap_generic_0,
  input strap_ss_strap_generic_1,
  input strap_ss_strap_generic_2,
  input strap_ss_strap_generic_3,
  input strap_ss_caliptra_dma_axi_user,
  input ss_debug_intent
  );

modport initiator_port 
  (
  input clk,
  input dummy,
  output strap_ss_caliptra_base_addr,
  output strap_ss_mci_base_addr,
  output strap_ss_recovery_ifc_base_addr,
  output strap_ss_external_staging_area_base_addr,
  output strap_ss_otp_fc_base_addr,
  output strap_ss_uds_seed_base_addr,
  output strap_ss_key_release_base_addr,
  output strap_ss_key_release_key_size,
  output strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset,
  output strap_ss_num_of_prod_debug_unlock_auth_pk_hashes,
  output strap_ss_strap_generic_0,
  output strap_ss_strap_generic_1,
  output strap_ss_strap_generic_2,
  output strap_ss_strap_generic_3,
  output strap_ss_caliptra_dma_axi_user,
  output ss_debug_intent
  );

modport responder_port 
  (
  input clk,
  input dummy,  
  input strap_ss_caliptra_base_addr,
  input strap_ss_mci_base_addr,
  input strap_ss_recovery_ifc_base_addr,
  input strap_ss_external_staging_area_base_addr,
  input strap_ss_otp_fc_base_addr,
  input strap_ss_uds_seed_base_addr,
  input strap_ss_key_release_base_addr,
  input strap_ss_key_release_key_size,
  input strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset,
  input strap_ss_num_of_prod_debug_unlock_auth_pk_hashes,
  input strap_ss_strap_generic_0,
  input strap_ss_strap_generic_1,
  input strap_ss_strap_generic_2,
  input strap_ss_strap_generic_3,
  input strap_ss_caliptra_dma_axi_user,
  input ss_debug_intent
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

