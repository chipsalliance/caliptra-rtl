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
// DESCRIPTION: This interface performs the cptra_ctrl signal monitoring.
//      It is accessed by the uvm cptra_ctrl monitor through a virtual
//      interface handle in the cptra_ctrl configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type cptra_ctrl_if.
//
//     Input signals from the cptra_ctrl_if are assigned to an internal input
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
//                   blocks until an operation on the cptra_ctrl bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import cptra_ctrl_pkg_hdl::*;
`include "src/cptra_ctrl_macros.svh"


interface cptra_ctrl_monitor_bfm
  ( cptra_ctrl_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute cptra_ctrl_monitor_bfm partition_interface_xif

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
`cptra_ctrl_MONITOR_STRUCT
  cptra_ctrl_monitor_s cptra_ctrl_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `cptra_ctrl_CONFIGURATION_STRUCT


  // Config value to determine if this is an initiator or a responder
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri dummy_i;
  tri  clear_obf_secrets_i;
  tri  iccm_axs_blocked_i;
  tri [3:0] rv_ecc_sts_i;
  assign clk_i = bus.clk;
  assign dummy_i = bus.dummy;
  assign clear_obf_secrets_i = bus.clear_obf_secrets;
  assign iccm_axs_blocked_i = bus.iccm_axs_blocked;
  assign rv_ecc_sts_i = bus.rv_ecc_sts;

  // Proxy handle to UVM monitor
  cptra_ctrl_pkg::cptra_ctrl_monitor  proxy;
  // pragma tbx oneway proxy.notify_transaction                 

  // pragma uvmf custom interface_item_additional begin
  logic clear_obf_secrets_r;
  logic iccm_axs_blocked_r;
  function bit any_signal_changed();
      return |(clear_obf_secrets_i   ^  clear_obf_secrets_r  ) ||
             |(iccm_axs_blocked_i    ^  iccm_axs_blocked_r   ) ||
             |(rv_ecc_sts_i          /* pulse no reg-stage */);
  endfunction
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

  //******************************************************************

  task wait_for_num_clocks(input int unsigned count); // pragma tbx xtf
    @(posedge clk_i);

    repeat (count-1) @(posedge clk_i);
  endtask

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
      do_monitor( cptra_ctrl_monitor_struct );


      proxy.notify_transaction( cptra_ctrl_monitor_struct );

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
    function void configure(cptra_ctrl_configuration_s cptra_ctrl_configuration_arg); // pragma tbx xtf
    initiator_responder = cptra_ctrl_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction


  // ****************************************************************************

  task do_monitor(output cptra_ctrl_monitor_s cptra_ctrl_monitor_struct);
    //
    // Available struct members:
    //     //    cptra_ctrl_monitor_struct.assert_clear_secrets
    //     //    cptra_ctrl_monitor_struct.iccm_axs_blocked
    //     //    cptra_ctrl_monitor_struct.pulse_rv_ecc_error
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal === 1'b1) @(posedge clk_i);
    //
    //    How to assign a struct member, named xyz, from a signal.
    //    All available input signals listed.
    //      cptra_ctrl_monitor_struct.xyz = clear_obf_secrets_i;  //     
    //      cptra_ctrl_monitor_struct.xyz = iccm_axs_blocked_i;  //
    //      cptra_ctrl_monitor_struct.xyz = rv_ecc_sts_i;  //    [3:0]
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code
    // below are examples of how to capture signal values and assign them to
    // structure members.  All available input signals are listed.  The 'while'
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe
    // the next transfer. One clock cycle is consumed between calls to do_monitor.

    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the cptra_ctrl_monitor_struct.
    while (!any_signal_changed()) @(posedge clk_i);
    iccm_axs_blocked_r    = iccm_axs_blocked_i;
    clear_obf_secrets_r   = clear_obf_secrets_i;
    begin: build_return_struct
  // Variables within the cptra_ctrl_monitor_struct:
         cptra_ctrl_monitor_struct.iccm_axs_blocked     = iccm_axs_blocked_i;
         cptra_ctrl_monitor_struct.assert_clear_secrets = clear_obf_secrets_i;
         cptra_ctrl_monitor_struct.pulse_rv_ecc_error   = rv_ecc_sts_i;
    end
    // pragma uvmf custom do_monitor end
  endtask


endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

