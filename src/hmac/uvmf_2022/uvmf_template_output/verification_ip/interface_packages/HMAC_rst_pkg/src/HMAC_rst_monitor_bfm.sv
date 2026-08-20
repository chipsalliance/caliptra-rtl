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
// DESCRIPTION: This interface performs the hmac_rst signal monitoring.
//      It is accessed by the uvm hmac_rst monitor through a virtual
//      interface handle in the hmac_rst configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type HMAC_rst_if.
//
//     Input signals from the HMAC_rst_if are assigned to an internal input
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
//                   blocks until an operation on the hmac_rst bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import HMAC_rst_pkg_hdl::*;
`include "src/HMAC_rst_macros.svh"


interface HMAC_rst_monitor_bfm 
  ( HMAC_rst_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute HMAC_rst_monitor_bfm partition_interface_xif                                  

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
`hmac_rst_MONITOR_STRUCT
  hmac_rst_monitor_s hmac_rst_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `hmac_rst_CONFIGURATION_STRUCT
 

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri dummy_i;
  tri  cptra_pwrgood_i;
  tri  rst_b_i;
  tri  debugUnlock_or_scan_mode_switch_i;
  assign clk_i = bus.clk;
  assign dummy_i = bus.dummy;
  assign cptra_pwrgood_i = bus.cptra_pwrgood;
  assign rst_b_i = bus.rst_b;
  assign debugUnlock_or_scan_mode_switch_i = bus.debugUnlock_or_scan_mode_switch;

  // Proxy handle to UVM monitor
  HMAC_rst_pkg::HMAC_rst_monitor  proxy;
  // pragma tbx oneway proxy.notify_transaction                 

  // pragma uvmf custom interface_item_additional begin
    // Shadow registers + edge-detector function. Matches the kv/pv
    // canonical pattern: the monitor only emits a transaction when one
    // of the rst-related signals actually CHANGES, instead of every
    // clock. Without this the monitor fires every 5 cycles (the stock
    // generator placeholder did `@(posedge clk_i)` x4 and returned),
    // making the predictor wipe state continuously.
    reg cptra_pwrgood_o                = 'b0;
    reg rst_b_o                        = 'b0;
    reg debugUnlock_or_scan_mode_switch_o = 'b0;

  function bit any_signal_changed();
    return  |(cptra_pwrgood_i ^ cptra_pwrgood_o) ||
            |(rst_b_i ^ rst_b_o) ||
            |(debugUnlock_or_scan_mode_switch_i ^ debugUnlock_or_scan_mode_switch_o);
  endfunction
  // pragma uvmf custom interface_item_additional end
  
  //******************************************************************                         
  task wait_for_reset();// pragma tbx xtf  
    @(posedge clk_i) ;                                                                    
    do_wait_for_reset();                                                                   
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
      do_monitor( hmac_rst_monitor_struct );
                                                                 
 
      proxy.notify_transaction( hmac_rst_monitor_struct );
 
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
    function void configure(hmac_rst_configuration_s hmac_rst_configuration_arg); // pragma tbx xtf  
    initiator_responder = hmac_rst_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction   


  // ****************************************************************************  
            
  task do_monitor(output hmac_rst_monitor_s hmac_rst_monitor_struct);
    //
    // Available struct members:
    //     //    hmac_rst_monitor_struct.set_pwrgood
    //     //    hmac_rst_monitor_struct.assert_rst
    //     //    hmac_rst_monitor_struct.assert_debug_scan
    //     //    hmac_rst_monitor_struct.wait_cycles
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal === 1'b1) @(posedge clk_i);
    //    
    //    How to assign a struct member, named xyz, from a signal.   
    //    All available input signals listed.
    //      hmac_rst_monitor_struct.xyz = cptra_pwrgood_i;  //     
    //      hmac_rst_monitor_struct.xyz = rst_b_i;  //     
    //      hmac_rst_monitor_struct.xyz = debugUnlock_or_scan_mode_switch_i;  //     
    // pragma uvmf custom do_monitor begin
    // Wait for any rst-related signal to change vs. its shadow copy
    // (kv/pv pattern -- see HMAC_rst_monitor_bfm.sv interface_item_additional
    // block for any_signal_changed() and shadow regs). Then snapshot the
    // current bus state and return. This causes the monitor to emit ONE
    // transaction per real event, not one every 5 clocks like the stock
    // generator placeholder did.
    while (!any_signal_changed()) @(posedge clk_i);

    cptra_pwrgood_o                <= cptra_pwrgood_i;
    rst_b_o                        <= rst_b_i;
    debugUnlock_or_scan_mode_switch_o <= debugUnlock_or_scan_mode_switch_i;

    hmac_rst_monitor_struct.set_pwrgood       = cptra_pwrgood_i;
    hmac_rst_monitor_struct.assert_rst        = !rst_b_i;
    hmac_rst_monitor_struct.assert_debug_scan = debugUnlock_or_scan_mode_switch_i;
    hmac_rst_monitor_struct.wait_cycles       = 0;
    // pragma uvmf custom do_monitor end
  endtask         
  
 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

