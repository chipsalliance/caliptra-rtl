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
// DESCRIPTION: This interface performs the kv_rst signal monitoring.
//      It is accessed by the uvm kv_rst monitor through a virtual
//      interface handle in the kv_rst configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type kv_rst_if.
//
//     Input signals from the kv_rst_if are assigned to an internal input
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
//                   blocks until an operation on the kv_rst bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import kv_rst_pkg_hdl::*;
`include "src/kv_rst_macros.svh"


interface kv_rst_monitor_bfm 
  ( kv_rst_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute kv_rst_monitor_bfm partition_interface_xif                                  

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
`kv_rst_MONITOR_STRUCT
  kv_rst_monitor_s kv_rst_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `kv_rst_CONFIGURATION_STRUCT
 

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri dummy_i;
  tri  cptra_pwrgood_i;
  tri  rst_b_i;
  tri  core_only_rst_b_i;
  tri  fw_update_rst_window_i;
  tri  debug_locked_i;
  tri  cptra_in_debug_scan_mode_i;
  assign clk_i = bus.clk;
  assign dummy_i = bus.dummy;
  assign cptra_pwrgood_i = bus.cptra_pwrgood;
  assign rst_b_i = bus.rst_b;
  assign core_only_rst_b_i = bus.core_only_rst_b;
  assign fw_update_rst_window_i = bus.fw_update_rst_window;
  assign debug_locked_i = bus.debug_locked;
  assign cptra_in_debug_scan_mode_i = bus.cptra_in_debug_scan_mode;

  // Proxy handle to UVM monitor
  kv_rst_pkg::kv_rst_monitor  proxy;
  // pragma tbx oneway proxy.notify_transaction                 

  // pragma uvmf custom interface_item_additional begin
    reg cptra_pwrgood_o = 'b0;
    reg rst_b_o = 'b0;
    reg core_only_rst_b_o = 'b0;
    reg fw_update_rst_window_o = 'b0;
    reg debug_locked_o = 'b0;
    reg cptra_in_debug_scan_mode_o = 'b0;

    function bit any_signal_changed();

      return  |(cptra_pwrgood_i ^ cptra_pwrgood_o) ||
              |(rst_b_i ^ rst_b_o) ||
              |(core_only_rst_b_i ^ core_only_rst_b_o) ||
              |(fw_update_rst_window_i ^ fw_update_rst_window_o) ||
              |(debug_locked_i ^ debug_locked_o) ||
              |(cptra_in_debug_scan_mode_i ^ cptra_in_debug_scan_mode_o);
  
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
      do_monitor( kv_rst_monitor_struct );
                                                                 
 
      proxy.notify_transaction( kv_rst_monitor_struct );
 
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
    function void configure(kv_rst_configuration_s kv_rst_configuration_arg); // pragma tbx xtf  
    initiator_responder = kv_rst_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction   


  // ****************************************************************************  
            
  task do_monitor(output kv_rst_monitor_s kv_rst_monitor_struct);
    //
    // Available struct members:
    //     //    kv_rst_monitor_struct.set_pwrgood
    //     //    kv_rst_monitor_struct.assert_rst
    //     //    kv_rst_monitor_struct.assert_core_rst
    //     //    kv_rst_monitor_struct.wait_cycles
    //     //    kv_rst_monitor_struct.debug_mode
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal === 1'b1) @(posedge clk_i);
    //    
    //    How to assign a struct member, named xyz, from a signal.   
    //    All available input signals listed.
    //      kv_rst_monitor_struct.xyz = cptra_pwrgood_i;  //     
    //      kv_rst_monitor_struct.xyz = rst_b_i;  //     
    //      kv_rst_monitor_struct.xyz = core_only_rst_b_i;  //     
    //      kv_rst_monitor_struct.xyz = debug_locked_i;  // 
    //      kv_rst_monitor_struct.xyz = cptra_in_debug_scan_mode_i;  // 
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code 
    // below are examples of how to capture signal values and assign them to 
    // structure members.  All available input signals are listed.  The 'while' 
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe 
    // the next transfer. One clock cycle is consumed between calls to do_monitor.
    while (!any_signal_changed()) @(posedge clk_i);

    cptra_pwrgood_o        <= cptra_pwrgood_i;
    rst_b_o                <= rst_b_i;
    core_only_rst_b_o      <= core_only_rst_b_i;
    fw_update_rst_window_o <= fw_update_rst_window_i;
    debug_locked_o         <= debug_locked_i;
    cptra_in_debug_scan_mode_o <= cptra_in_debug_scan_mode_i;

    kv_rst_monitor_struct.set_pwrgood = cptra_pwrgood_i;
    kv_rst_monitor_struct.assert_rst = !rst_b_i;
    kv_rst_monitor_struct.assert_core_rst = !core_only_rst_b_i;
    kv_rst_monitor_struct.wait_cycles = 0;
    kv_rst_monitor_struct.debug_mode = debug_locked_i;
    kv_rst_monitor_struct.scan_mode = cptra_in_debug_scan_mode_i & !debug_locked_i;
    // pragma uvmf custom do_monitor end
  endtask         
  
 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

