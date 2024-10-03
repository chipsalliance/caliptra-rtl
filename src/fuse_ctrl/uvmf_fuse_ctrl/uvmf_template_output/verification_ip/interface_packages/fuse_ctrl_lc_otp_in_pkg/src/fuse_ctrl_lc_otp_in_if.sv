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
// DESCRIPTION: This interface contains the fuse_ctrl_lc_otp_in interface signals.
//      It is instantiated once per fuse_ctrl_lc_otp_in bus.  Bus Functional Models, 
//      BFM's named fuse_ctrl_lc_otp_in_driver_bfm, are used to drive signals on the bus.
//      BFM's named fuse_ctrl_lc_otp_in_monitor_bfm are used to monitor signals on the 
//      bus. This interface signal bundle is passed in the port list of
//      the BFM in order to give the BFM access to the signals in this
//      interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// This template can be used to connect a DUT to these signals
//
// .dut_signal_port(fuse_ctrl_lc_otp_in_bus.lc_otp_vendor_test_i), // Agent output 
// .dut_signal_port(fuse_ctrl_lc_otp_in_bus.lc_otp_program_i), // Agent output 
// .dut_signal_port(fuse_ctrl_lc_otp_in_bus.lc_dft_en_i), // Agent output 
// .dut_signal_port(fuse_ctrl_lc_otp_in_bus.lc_escalate_en_i), // Agent output 
// .dut_signal_port(fuse_ctrl_lc_otp_in_bus.lc_check_byp_en_i), // Agent output 

import uvmf_base_pkg_hdl::*;
import fuse_ctrl_lc_otp_in_pkg_hdl::*;

interface  fuse_ctrl_lc_otp_in_if 

  (
  input tri clk_i, 
  input tri rst_ni,
  inout tri [$bits(lc_otp_vendor_test_req_t)-1:0] lc_otp_vendor_test_i,
  inout tri [$bits(lc_otp_program_req_t)-1:0] lc_otp_program_i,
  inout tri [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] lc_dft_en_i,
  inout tri [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] lc_escalate_en_i,
  inout tri [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] lc_check_byp_en_i
  );

modport monitor_port 
  (
  input clk_i,
  input rst_ni,
  input lc_otp_vendor_test_i,
  input lc_otp_program_i,
  input lc_dft_en_i,
  input lc_escalate_en_i,
  input lc_check_byp_en_i
  );

modport initiator_port 
  (
  input clk_i,
  input rst_ni,
  output lc_otp_vendor_test_i,
  output lc_otp_program_i,
  output lc_dft_en_i,
  output lc_escalate_en_i,
  output lc_check_byp_en_i
  );

modport responder_port 
  (
  input clk_i,
  input rst_ni,  
  input lc_otp_vendor_test_i,
  input lc_otp_program_i,
  input lc_dft_en_i,
  input lc_escalate_en_i,
  input lc_check_byp_en_i
  );
  

// pragma uvmf custom interface_item_additional begin
// pragma uvmf custom interface_item_additional end

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

