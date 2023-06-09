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
// DESCRIPTION: This interface contains the cptra_ctrl interface signals.
//      It is instantiated once per cptra_ctrl bus.  Bus Functional Models, 
//      BFM's named cptra_ctrl_driver_bfm, are used to drive signals on the bus.
//      BFM's named cptra_ctrl_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(cptra_ctrl_bus.clear_obf_secrets), // Agent output 
// .dut_signal_port(cptra_ctrl_bus.iccm_axs_blocked), // Agent output 
// .dut_signal_port(cptra_ctrl_bus.rv_ecc_sts), // Agent output 

import uvmf_base_pkg_hdl::*;
import cptra_ctrl_pkg_hdl::*;

interface  cptra_ctrl_if 

  (
  input tri clk, 
  input tri dummy,
  inout tri  clear_obf_secrets,
  inout tri  iccm_axs_blocked,
  inout tri [3:0] rv_ecc_sts
  );

modport monitor_port 
  (
  input clk,
  input dummy,
  input clear_obf_secrets,
  input iccm_axs_blocked,
  input rv_ecc_sts
  );

modport initiator_port 
  (
  input clk,
  input dummy,
  output clear_obf_secrets,
  output iccm_axs_blocked,
  output rv_ecc_sts
  );

modport responder_port 
  (
  input clk,
  input dummy,  
  input clear_obf_secrets,
  input iccm_axs_blocked,
  input rv_ecc_sts
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

