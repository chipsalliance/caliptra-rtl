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
// DESCRIPTION: This interface performs the kv_read signal monitoring.
//      It is accessed by the uvm kv_read monitor through a virtual
//      interface handle in the kv_read configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type kv_read_if.
//
//     Input signals from the kv_read_if are assigned to an internal input
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
//                   blocks until an operation on the kv_read bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import kv_read_pkg_hdl::*;
import kv_defines_pkg::*;
`include "src/kv_read_macros.svh"


interface kv_read_monitor_bfm #(
  string KV_READ_REQUESTOR = "HMAC_KEY"
  )

  ( kv_read_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute kv_read_monitor_bfm partition_interface_xif                                  

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
      $psprintf("The BFM at '%m' has the following parameters: KV_READ_REQUESTOR=%x ", KV_READ_REQUESTOR),
      UVM_DEBUG)
end
`endif


  // Structure used to pass transaction data from monitor BFM to monitor class in agent.
`kv_read_MONITOR_STRUCT
  kv_read_monitor_s kv_read_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `kv_read_CONFIGURATION_STRUCT
 

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri dummy_i;
  tri [$bits(kv_defines_pkg::kv_read_t)-1:0] kv_read_i;
  tri [$bits(kv_defines_pkg::kv_rd_resp_t)-1:0] kv_rd_resp_i;
  assign clk_i = bus.clk;
  assign dummy_i = bus.dummy;
  assign kv_read_i = bus.kv_read;
  assign kv_rd_resp_i = bus.kv_rd_resp;

  // Proxy handle to UVM monitor
  kv_read_pkg::kv_read_monitor #(
    .KV_READ_REQUESTOR(KV_READ_REQUESTOR)
    )
 proxy;
  // pragma tbx oneway proxy.notify_transaction                 

  // pragma uvmf custom interface_item_additional begin
 reg [KV_ENTRY_ADDR_W-1:0] read_entry_o = 'h0;
 reg [KV_ENTRY_SIZE_W-1:0] read_offset_o = 'h0;
 reg error_o = 'h0;
 reg last_o = 'h0;
 reg [KV_DATA_W-1:0] read_data_o = 'h0;
  function bit any_signal_changed();

    return  |(kv_read_i[8:4] ^ read_entry_o ) ||
            |(kv_read_i[3:0] ^ read_offset_o) ||
            |(kv_rd_resp_i[33] ^ error_o    ) ||
            |(kv_rd_resp_i[32] ^ last_o    ) ||
            |(kv_rd_resp_i[31:0] ^ read_data_o);

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
      do_monitor( kv_read_monitor_struct );
                                                                 
 
      proxy.notify_transaction( kv_read_monitor_struct );
 
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
    function void configure(kv_read_configuration_s kv_read_configuration_arg); // pragma tbx xtf  
    initiator_responder = kv_read_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction   


  // ****************************************************************************  
            
  task do_monitor(output kv_read_monitor_s kv_read_monitor_struct);
    //
    // Available struct members:
    //     //    kv_read_monitor_struct.read_entry
    //     //    kv_read_monitor_struct.read_offset
    //     //    kv_read_monitor_struct.error
    //     //    kv_read_monitor_struct.last
    //     //    kv_read_monitor_struct.read_data
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal === 1'b1) @(posedge clk_i);
    //    
    //    How to assign a struct member, named xyz, from a signal.   
    //    All available input signals listed.
    //      kv_read_monitor_struct.xyz = kv_read_i;  //    [$bits(kv_defines_pkg::kv_read_t)-1:0] 
    //      kv_read_monitor_struct.xyz = kv_rd_resp_i;  //    [$bits(kv_defines_pkg::kv_rd_resp_t)-1:0] 
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code 
    // below are examples of how to capture signal values and assign them to 
    // structure members.  All available input signals are listed.  The 'while' 
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe 
    // the next transfer. One clock cycle is consumed between calls to do_monitor.
    while (!any_signal_changed()) @(posedge clk_i);

    // read_entry_o <= kv_read_i[3:1];
    // read_offset_o <= kv_read_i[7:4];
    read_entry_o <= kv_read_i[8:4];
    read_offset_o <= kv_read_i[3:0];
    
    error_o <= kv_rd_resp_i[33];
    last_o <= kv_rd_resp_i[32];
    read_data_o <= kv_rd_resp_i[31:0];

    
    // kv_read_monitor_struct.read_entry   = kv_read_i[3:1];
    // kv_read_monitor_struct.read_offset  = kv_read_i[7:4];
    kv_read_monitor_struct.read_entry   = kv_read_i[8:4];
    kv_read_monitor_struct.read_offset  = kv_read_i[3:0];

    kv_read_monitor_struct.error        = kv_rd_resp_i[33];
    kv_read_monitor_struct.last        = kv_rd_resp_i[32];
    kv_read_monitor_struct.read_data    = kv_rd_resp_i[31:0];

    // pragma uvmf custom do_monitor end
  endtask         
  
 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

