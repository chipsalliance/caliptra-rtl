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
import soc_ifc_pkg::*;
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: This interface performs the mbox_sram signal monitoring.
//      It is accessed by the uvm mbox_sram monitor through a virtual
//      interface handle in the mbox_sram configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type mbox_sram_if.
//
//     Input signals from the mbox_sram_if are assigned to an internal input
//     signal with a _i suffix.  The _i signal should be used for sampling.
//
//     The input signal connections are as follows:
//       bus.signal -> signal_i
//
//      Interface functions and tasks used by UVM components:
//             monitor(inout TRANS_T txn);
//                   This task receives the transaction, txn, from the
//                   UVM monitor and then populates variables in txn
//                   from values observed on bus activity.  This task
//                   blocks until an operation on the mbox_sram bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import mbox_sram_pkg_hdl::*;
`include "src/mbox_sram_macros.svh"


interface mbox_sram_monitor_bfm
  ( mbox_sram_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute mbox_sram_monitor_bfm partition_interface_xif

`ifndef XRTL
// This code is to aid in debugging parameter mismatches between the BFM and its corresponding agent.
// Enable this debug by setting UVM_VERBOSITY to UVM_DEBUG
// Setting UVM_VERBOSITY to UVM_DEBUG causes all BFM's and all agents to display their parameter settings.
// All of the messages from this feature have a UVM messaging id value of "CFG"
// The transcript or run.log can be parsed to ensure BFM parameter settings match its corresponding agents parameter settings.
import uvm_pkg::*;
`include "uvm_macros.svh"
initial begin : bfm_vs_agent_parameter_debug
  `uvm_info("CFG",
      $psprintf("The BFM at '%m' has the following parameters: ", ),
      UVM_DEBUG)
end
`endif


  // Structure used to pass transaction data from monitor BFM to monitor class in agent.
`mbox_sram_MONITOR_STRUCT
  mbox_sram_monitor_s mbox_sram_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `mbox_sram_CONFIGURATION_STRUCT


  // Config value to determine if this is an initiator or a responder
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.
  // These are set using the configure function which is called during the UVM connect_phase
  bit [1:0] inject_ecc_error ;
  bit auto_clear_ecc_error_injection ;

  tri clk_i;
  tri dummy_i;
  tri mbox_sram_req_t  mbox_sram_req_i;
  tri mbox_sram_resp_t mbox_sram_resp_i;
  assign clk_i = bus.clk;
  assign dummy_i = bus.dummy;
  assign mbox_sram_req_i = bus.mbox_sram_req;
  assign mbox_sram_resp_i = bus.mbox_sram_resp;

  // Proxy handle to UVM monitor
  mbox_sram_pkg::mbox_sram_monitor  proxy;
  // pragma tbx oneway proxy.notify_transaction

  // pragma uvmf custom interface_item_additional begin
  function bit [1:0] rvecc_decode  ( input [31:0]  din, input [6:0]   ecc_in);
    bit [6:0]  ecc_check;

    // Generate the ecc bits
    ecc_check[0] = ecc_in[0]^din[0]^din[1]^din[3]^din[4]^din[6]^din[8]^din[10]^din[11]^din[13]^din[15]^din[17]^din[19]^din[21]^din[23]^din[25]^din[26]^din[28]^din[30];
    ecc_check[1] = ecc_in[1]^din[0]^din[2]^din[3]^din[5]^din[6]^din[9]^din[10]^din[12]^din[13]^din[16]^din[17]^din[20]^din[21]^din[24]^din[25]^din[27]^din[28]^din[31];
    ecc_check[2] = ecc_in[2]^din[1]^din[2]^din[3]^din[7]^din[8]^din[9]^din[10]^din[14]^din[15]^din[16]^din[17]^din[22]^din[23]^din[24]^din[25]^din[29]^din[30]^din[31];
    ecc_check[3] = ecc_in[3]^din[4]^din[5]^din[6]^din[7]^din[8]^din[9]^din[10]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25];
    ecc_check[4] = ecc_in[4]^din[11]^din[12]^din[13]^din[14]^din[15]^din[16]^din[17]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25];
    ecc_check[5] = ecc_in[5]^din[26]^din[27]^din[28]^din[29]^din[30]^din[31];

    // This is the parity bit
    ecc_check[6] = ((^din[31:0])^(^ecc_in[6:0]));

    rvecc_decode[0] = (ecc_check[6:0] != 0) &  ecc_check[6]; // Single-bit error
    rvecc_decode[1] = (ecc_check[6:0] != 0) & ~ecc_check[6]; // Double-bit error

  endfunction: rvecc_decode
  // pragma uvmf custom interface_item_additional end

  //******************************************************************
  task wait_for_reset();// pragma tbx xtf
//    @(posedge clk_i) ;
//    do_wait_for_reset();
  endtask

  // ****************************************************************************
  task do_wait_for_reset();
  // pragma uvmf custom reset_condition begin
    wait ( dummy_i === 1 ) ;
    @(posedge clk_i) ;
  // pragma uvmf custom reset_condition end
  endtask

  // pragma uvmf custom wait_for_num_clocks begin
  //****************************************************************************                         
  // Inject pragmas's here to throw a warning on regeneration.
  // Task must have automatic lifetime so that it can be concurrently invoked
  // by multiple entities with a different wait value.
  task automatic wait_for_num_clocks(input int unsigned count); // pragma tbx xtf
    if (count == 0) `uvm_fatal("CFG", "wait_for_num_clocks called with count of 0 - this will lead to a hang");
    @(posedge clk_i);
    repeat (count-1) @(posedge clk_i);
  endtask
  // pragma uvmf custom wait_for_num_clocks end                                                                

  //******************************************************************
  event go;
  function void start_monitoring();// pragma tbx xtf
    -> go;
  endfunction

  // ****************************************************************************
  initial begin
    @go;
    forever begin
      @(posedge clk_i);
      do_monitor( mbox_sram_monitor_struct );


      proxy.notify_transaction( mbox_sram_monitor_struct );

    end
  end

  //******************************************************************
  // The configure() function is used to pass agent configuration
  // variables to the monitor BFM.  It is called by the monitor within
  // the agent at the beginning of the simulation.  It may be called
  // during the simulation if agent configuration variables are updated
  // and the monitor BFM needs to be aware of the new configuration
  // variables.
  //
    function void configure(mbox_sram_configuration_s mbox_sram_configuration_arg); // pragma tbx xtf
    initiator_responder = mbox_sram_configuration_arg.initiator_responder;
    inject_ecc_error = mbox_sram_configuration_arg.inject_ecc_error;
    auto_clear_ecc_error_injection = mbox_sram_configuration_arg.auto_clear_ecc_error_injection;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction


  // ****************************************************************************

  task do_monitor(output mbox_sram_monitor_s mbox_sram_monitor_struct);
    //
    // Available struct members:
    //     //    mbox_sram_monitor_struct.is_read
    //     //    mbox_sram_monitor_struct.address
    //     //    mbox_sram_monitor_struct.data
    //     //    mbox_sram_monitor_struct.data_ecc
    //     //    mbox_sram_monitor_struct.ecc_single_bit_error
    //     //    mbox_sram_monitor_struct.ecc_double_bit_error
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal === 1'b1) @(posedge clk_i);
    //
    //    How to assign a struct member, named xyz, from a signal.
    //    All available input signals listed.
    //      mbox_sram_monitor_struct.xyz = mbox_sram_req_i;  //    [$bits(mbox_sram_req_t)-1:0]
    //      mbox_sram_monitor_struct.xyz = mbox_sram_resp_i;  //    [$bits(mbox_sram_resp_t)-1:0]
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code
    // below are examples of how to capture signal values and assign them to
    // structure members.  All available input signals are listed.  The 'while'
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe
    // the next transfer. One clock cycle is consumed between calls to do_monitor.
    while (mbox_sram_req_i.cs !== 1'b1) @(posedge clk_i);
    mbox_sram_monitor_struct.is_read              = ~mbox_sram_req_i.we;
    mbox_sram_monitor_struct.address              =  mbox_sram_req_i.addr;
    mbox_sram_monitor_struct.data                 =  mbox_sram_req_i.wdata.data;
    mbox_sram_monitor_struct.data_ecc             =  mbox_sram_req_i.wdata.ecc;
    // For writes, the monitored transaction signals the _intent_ to inject an ECC error
    // at the responder sequence
    mbox_sram_monitor_struct.ecc_single_bit_error =  proxy.configuration.inject_ecc_error[0];
    mbox_sram_monitor_struct.ecc_double_bit_error =  proxy.configuration.inject_ecc_error[1];
    // If a write is detected, return immediately (that's the whole transaction)
    if (mbox_sram_req_i.we) return;
    // If a read, continue another clock cycle to capture return data
    @(posedge clk_i);
    mbox_sram_monitor_struct.data     = mbox_sram_resp_i.rdata.data;
    mbox_sram_monitor_struct.data_ecc = mbox_sram_resp_i.rdata.ecc;
    // For reads, the monitored transaction signals the calculation of actual ECC errors
    // observed on the data returned from the responder sequence
    {mbox_sram_monitor_struct.ecc_double_bit_error,
     mbox_sram_monitor_struct.ecc_single_bit_error} = rvecc_decode(mbox_sram_monitor_struct.data, mbox_sram_monitor_struct.data_ecc);
    // pragma uvmf custom do_monitor end
  endtask


endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

