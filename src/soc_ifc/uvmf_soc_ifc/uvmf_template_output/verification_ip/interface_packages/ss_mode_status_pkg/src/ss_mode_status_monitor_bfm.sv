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
// DESCRIPTION: This interface performs the ss_mode_status signal monitoring.
//      It is accessed by the uvm ss_mode_status monitor through a virtual
//      interface handle in the ss_mode_status configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type ss_mode_status_if.
//
//     Input signals from the ss_mode_status_if are assigned to an internal input
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
//                   blocks until an operation on the ss_mode_status bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import ss_mode_status_pkg_hdl::*;
`include "src/ss_mode_status_macros.svh"


interface ss_mode_status_monitor_bfm 
  ( ss_mode_status_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute ss_mode_status_monitor_bfm partition_interface_xif                                  

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
`ss_mode_status_MONITOR_STRUCT
  ss_mode_status_monitor_s ss_mode_status_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `ss_mode_status_CONFIGURATION_STRUCT
 

  // Config value to determine if this is an initiator or a responder
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri dummy_i;
  tri  cptra_ss_debug_intent_i;
  tri  ss_dbg_manuf_enable_i;
  tri [63:0] ss_soc_dbg_unlock_level_i;
  tri [127:0] ss_generic_fw_exec_ctrl_i;
  assign clk_i = bus.clk;
  assign dummy_i = bus.dummy;
  assign cptra_ss_debug_intent_i = bus.cptra_ss_debug_intent;
  assign ss_dbg_manuf_enable_i = bus.ss_dbg_manuf_enable;
  assign ss_soc_dbg_unlock_level_i = bus.ss_soc_dbg_unlock_level;
  assign ss_generic_fw_exec_ctrl_i = bus.ss_generic_fw_exec_ctrl;

  // Proxy handle to UVM monitor
  ss_mode_status_pkg::ss_mode_status_monitor  proxy;
  // pragma tbx oneway proxy.notify_transaction

  // pragma uvmf custom interface_item_additional begin
  reg cptra_ss_debug_intent_o = 'b0;
  reg ss_dbg_manuf_enable_o = 'b0;
  reg [63:0] ss_soc_dbg_unlock_level_o = 'b0;
  reg [127:0] ss_generic_fw_exec_ctrl_o = 'b0;
  function bit any_signal_changed();
      return |(cptra_ss_debug_intent_i   ^ cptra_ss_debug_intent_o  ) ||
             |(ss_dbg_manuf_enable_i     ^ ss_dbg_manuf_enable_o    ) ||
             |(ss_soc_dbg_unlock_level_i ^ ss_soc_dbg_unlock_level_o) ||
             |(ss_generic_fw_exec_ctrl_i ^ ss_generic_fw_exec_ctrl_o);
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
      do_monitor( ss_mode_status_monitor_struct );


      proxy.notify_transaction( ss_mode_status_monitor_struct );

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
    function void configure(ss_mode_status_configuration_s ss_mode_status_configuration_arg); // pragma tbx xtf
    initiator_responder = ss_mode_status_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction


  // ****************************************************************************

  task do_monitor(output ss_mode_status_monitor_s ss_mode_status_monitor_struct);
    //
    // Available struct members:
    //     //    ss_mode_status_monitor_struct.cptra_ss_debug_intent
    //     //    ss_mode_status_monitor_struct.ss_dbg_manuf_enable
    //     //    ss_mode_status_monitor_struct.ss_soc_dbg_unlock_level
    //     //    ss_mode_status_monitor_struct.ss_generic_fw_exec_ctrl
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal === 1'b1) @(posedge clk_i);
    //
    //    How to assign a struct member, named xyz, from a signal.
    //    All available input signals listed.
    //      ss_mode_status_monitor_struct.xyz = cptra_ss_debug_intent_i;  //
    //      ss_mode_status_monitor_struct.xyz = ss_dbg_manuf_enable_i;  //
    //      ss_mode_status_monitor_struct.xyz = ss_soc_dbg_unlock_level_i;  //    [63:0]
    //      ss_mode_status_monitor_struct.xyz = ss_generic_fw_exec_ctrl_i;  //    [127:0]
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code
    // below are examples of how to capture signal values and assign them to
    // structure members.  All available input signals are listed.  The 'while'
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe
    // the next transfer. One clock cycle is consumed between calls to do_monitor.

    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the ss_mode_status_monitor_struct.
    while (!any_signal_changed()) @(posedge clk_i);
    cptra_ss_debug_intent_o   <= cptra_ss_debug_intent_i;
    ss_dbg_manuf_enable_o     <= ss_dbg_manuf_enable_i;
    ss_soc_dbg_unlock_level_o <= ss_soc_dbg_unlock_level_i;
    ss_generic_fw_exec_ctrl_o <= ss_generic_fw_exec_ctrl_i;
    begin: build_return_struct
        ss_mode_status_monitor_struct.cptra_ss_debug_intent   = cptra_ss_debug_intent_i;
        ss_mode_status_monitor_struct.ss_dbg_manuf_enable     = ss_dbg_manuf_enable_i;
        ss_mode_status_monitor_struct.ss_soc_dbg_unlock_level = ss_soc_dbg_unlock_level_i;
        ss_mode_status_monitor_struct.ss_generic_fw_exec_ctrl = ss_generic_fw_exec_ctrl_i;
    end
    // pragma uvmf custom do_monitor end
  endtask


endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

