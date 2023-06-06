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
// DESCRIPTION: This interface contains the kv_write interface signals.
//      It is instantiated once per kv_write bus.  Bus Functional Models, 
//      BFM's named kv_write_driver_bfm, are used to drive signals on the bus.
//      BFM's named kv_write_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(kv_write_bus.kv_write), // Agent output 
// .dut_signal_port(kv_write_bus.kv_wr_resp), // Agent input 

import uvmf_base_pkg_hdl::*;
import kv_write_pkg_hdl::*;
import kv_reg_pkg::*;

interface  kv_write_if #(
  string KV_WRITE_REQUESTOR = "HMAC"
  )


  (
  input tri clk, 
  input tri dummy,
  inout tri [$bits(kv_defines_pkg::kv_write_t)-1:0] kv_write,
  inout tri [$bits(kv_defines_pkg::kv_wr_resp_t)-1:0] kv_wr_resp
  );

modport monitor_port 
  (
  input clk,
  input dummy,
  input kv_write,
  input kv_wr_resp
  );

modport initiator_port 
  (
  input clk,
  input dummy,
  output kv_write,
  input kv_wr_resp
  );

modport responder_port 
  (
  input clk,
  input dummy,  
  input kv_write,
  output kv_wr_resp
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

