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
// DESCRIPTION: This interface performs the kv_write signal monitoring.
//      It is accessed by the uvm kv_write monitor through a virtual
//      interface handle in the kv_write configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type kv_write_if.
//
//     Input signals from the kv_write_if are assigned to an internal input
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
//                   blocks until an operation on the kv_write bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import kv_write_pkg_hdl::*;
`include "src/kv_write_macros.svh"


interface kv_write_monitor_bfm #(
  string KV_WRITE_REQUESTOR = "HMAC"
  )

  ( kv_write_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute kv_write_monitor_bfm partition_interface_xif                                  

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
      $psprintf("The BFM at '%m' has the following parameters: KV_WRITE_REQUESTOR=%x ", KV_WRITE_REQUESTOR),
      UVM_DEBUG)
end
`endif


  // Structure used to pass transaction data from monitor BFM to monitor class in agent.
`kv_write_MONITOR_STRUCT
  kv_write_monitor_s kv_write_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `kv_write_CONFIGURATION_STRUCT
 

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri dummy_i;
  tri [$bits(kv_defines_pkg::kv_write_t)-1:0] kv_write_i;
  tri [$bits(kv_defines_pkg::kv_wr_resp_t)-1:0] kv_wr_resp_i;
    reg write_en_i          ;
    reg [KV_ENTRY_ADDR_W-1:0] write_entry_i ;
    reg [KV_ENTRY_SIZE_W-1:0] write_offset_i;
    reg [KV_DATA_W-1:0] write_data_i ;
    reg [KV_NUM_READ-1:0] write_dest_valid_i ;
    reg error_i;
  assign clk_i = bus.clk;
  assign dummy_i = bus.dummy;
  assign kv_write_i = bus.kv_write;
  assign kv_wr_resp_i = bus.kv_wr_resp;
  assign write_en_i          = kv_write_i[46]; //[0];
  assign write_entry_i       = kv_write_i[45:41]; //[4:2];
  assign write_offset_i      = kv_write_i[40:37]; //[8:5];
  assign write_data_i        = kv_write_i[36:5]; //[40:9];
  assign write_dest_valid_i  = kv_write_i[4:0]; //[46:41];
  assign error_i             = kv_wr_resp_i[0];

  // Proxy handle to UVM monitor
  kv_write_pkg::kv_write_monitor #(
    .KV_WRITE_REQUESTOR(KV_WRITE_REQUESTOR)
    )
 proxy;
  // pragma tbx oneway proxy.notify_transaction                 

  // pragma uvmf custom interface_item_additional begin
 reg write_en_o               = 'h0; 
 reg [KV_ENTRY_ADDR_W-1:0] write_entry_o      = 'h0; 
 reg [KV_ENTRY_SIZE_W-1:0] write_offset_o     = 'h0; 
 reg [KV_DATA_W-1:0] write_data_o      = 'h0; 
 reg [KV_NUM_READ-1:0] write_dest_valid_o = 'h0; 
 reg error_o = 'h0;

  function any_signal_changed();

    return |(write_en_i ^ write_en_o) ||
           |(write_entry_i ^ write_entry_o) ||
           |(write_offset_i ^ write_offset_o) ||
           |(write_data_i ^ write_data_o) ||
           |(write_dest_valid_i ^ write_dest_valid_o) ||
           |(error_i ^ error_o);

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
      //@(posedge clk_i);  
      do_monitor( kv_write_monitor_struct );
                                                                 
 
      proxy.notify_transaction( kv_write_monitor_struct );
 
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
    function void configure(kv_write_configuration_s kv_write_configuration_arg); // pragma tbx xtf  
    initiator_responder = kv_write_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction   


  // ****************************************************************************  
            
  task do_monitor(output kv_write_monitor_s kv_write_monitor_struct);
    //
    // Available struct members:
    //     //    kv_write_monitor_struct.write_en
    //     //    kv_write_monitor_struct.write_entry
    //     //    kv_write_monitor_struct.write_offset
    //     //    kv_write_monitor_struct.write_data
    //     //    kv_write_monitor_struct.write_dest_valid
    //     //    kv_write_monitor_struct.error
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal === 1'b1) @(posedge clk_i);
    //    
    //    How to assign a struct member, named xyz, from a signal.   
    //    All available input signals listed.
    //      kv_write_monitor_struct.xyz = kv_write_i;  //    [$bits(kv_defines_pkg::kv_write_t)-1:0] 
    //      kv_write_monitor_struct.xyz = kv_wr_resp_i;  //    [$bits(kv_defines_pkg::kv_wr_resp_t)-1:0] 
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code 
    // below are examples of how to capture signal values and assign them to 
    // structure members.  All available input signals are listed.  The 'while' 
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe 
    // the next transfer. One clock cycle is consumed between calls to do_monitor.

    while(!any_signal_changed()) @(posedge clk_i);
    write_en_o          <= write_en_i; //kv_write_i[0];
    write_entry_o       <= write_entry_i; //kv_write_i[4:2];
    write_offset_o      <= write_offset_i; //kv_write_i[8:5];
    write_data_o        <= write_data_i; //kv_write_i[40:9];
    write_dest_valid_o  <= write_dest_valid_i; //kv_write_i[46:41];
    error_o             <= error_i;

    @(posedge clk_i); //Delay write txn to monitor by 1 clk to mimic design
    //(regs are updated in the next clk and reg model should follow the same)
    kv_write_monitor_struct.write_en          = write_en_o; //kv_write_i[0];
    kv_write_monitor_struct.write_entry       = write_entry_o; //kv_write_i[4:2];
    kv_write_monitor_struct.write_offset      = write_offset_o; //kv_write_i[8:5];
    kv_write_monitor_struct.write_data        = write_data_o; //kv_write_i[40:9];
    kv_write_monitor_struct.write_dest_valid  = write_dest_valid_o; //kv_write_i[46:41];
    kv_write_monitor_struct.error             = error_o;


    // pragma uvmf custom do_monitor end
  endtask         
  
 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

