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
// DESCRIPTION: This interface performs the soc_ifc_ctrl signal monitoring.
//      It is accessed by the uvm soc_ifc_ctrl monitor through a virtual
//      interface handle in the soc_ifc_ctrl configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type soc_ifc_ctrl_if.
//
//     Input signals from the soc_ifc_ctrl_if are assigned to an internal input
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
//                   blocks until an operation on the soc_ifc_ctrl bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import soc_ifc_ctrl_pkg_hdl::*;
`include "src/soc_ifc_ctrl_macros.svh"


interface soc_ifc_ctrl_monitor_bfm
  ( soc_ifc_ctrl_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute soc_ifc_ctrl_monitor_bfm partition_interface_xif

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
`soc_ifc_ctrl_MONITOR_STRUCT
  soc_ifc_ctrl_monitor_s soc_ifc_ctrl_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `soc_ifc_ctrl_CONFIGURATION_STRUCT
 

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri dummy_i;
  tri  cptra_pwrgood_i;
  tri  cptra_rst_b_i;
  tri [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key_i;
  tri [2:0] security_state_i;
  tri  BootFSM_BrkPoint_i;
  tri [63:0] generic_input_wires_i;
  assign clk_i = bus.clk;
  assign dummy_i = bus.dummy;
  assign cptra_pwrgood_i = bus.cptra_pwrgood;
  assign cptra_rst_b_i = bus.cptra_rst_b;
  assign cptra_obf_key_i = bus.cptra_obf_key;
  assign security_state_i = bus.security_state;
  assign BootFSM_BrkPoint_i = bus.BootFSM_BrkPoint;
  assign generic_input_wires_i = bus.generic_input_wires;

  // Proxy handle to UVM monitor
  soc_ifc_ctrl_pkg::soc_ifc_ctrl_monitor  proxy;
  // pragma tbx oneway proxy.notify_transaction                 

  // pragma uvmf custom interface_item_additional begin
  logic  cptra_pwrgood_r = 1'bx;
  logic  cptra_rst_b_r = 1'bx;
  logic [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key_r;
  logic [63:0] generic_input_wires_r;
  security_state_t security_state_r;
  logic BootFSM_BrkPoint_r;
  // Returns 1 on first transaction that sets any value to cptra_pwrgood_i or cptra_rst_b_i
  // Also returns 1 anytime any other signal transitions, outside of a reset
  function bit any_signal_changed();
      if (cptra_pwrgood_r !== 1'b1)
          return (cptra_pwrgood_i !== cptra_pwrgood_r);
      else if (cptra_rst_b_r !== 1'b1)
          return (cptra_rst_b_i !== cptra_rst_b_r);
      else
          return |(cptra_pwrgood_i       ^  cptra_pwrgood_r      ) ||
                 |(cptra_rst_b_i         ^  cptra_rst_b_r        ) ||
                 |(cptra_obf_key_i       ^  cptra_obf_key_r      ) ||
                 |(security_state_i      ^  security_state_r     ) ||
                 |(BootFSM_BrkPoint_i    ^  BootFSM_BrkPoint_r   ) ||
                 |(generic_input_wires_i ^  generic_input_wires_r);
  endfunction
  
  //******************************************************************                         
  task wait_for_reset_assertion(output string kind);
    bit soft_rst, hard_rst;
    soft_rst = 1'b0;
    hard_rst = 1'b0;
    @(posedge clk_i) ;
    fork
        begin
        do_wait_for_hard_reset_assertion();
        hard_rst = 1'b1;
        end
        begin
        do_wait_for_soft_reset_assertion();
        soft_rst = 1'b1;
        hard_rst = !cptra_pwrgood_i;
        end
    join_any
    disable fork;
    if (hard_rst) kind = "HARD";
    else          kind = "SOFT";
  endtask                                                                                   

  // ****************************************************************************              
  task do_wait_for_soft_reset_assertion(); 
    // Catch the edge of any transition to 0 (assertion)
    wait ( (cptra_rst_b_r !== 1'b0) && (cptra_rst_b_i === 1'b0) ) ;                                                              
    @(posedge clk_i) ;                                                                    
  endtask    

  // ****************************************************************************              
  task do_wait_for_hard_reset_assertion(); 
    // Catch the edge of any transition to 0 (assertion)
    wait ( (cptra_pwrgood_r !== 1'b0) && (cptra_pwrgood_i === 1'b0) ) ;                                                              
    @(posedge clk_i) ;                                                                    
  endtask    

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
      do_monitor( soc_ifc_ctrl_monitor_struct );
                                                                 
 
      proxy.notify_transaction( soc_ifc_ctrl_monitor_struct );
 
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
    function void configure(soc_ifc_ctrl_configuration_s soc_ifc_ctrl_configuration_arg); // pragma tbx xtf  
    initiator_responder = soc_ifc_ctrl_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction   


  // ****************************************************************************  
            
  task do_monitor(output soc_ifc_ctrl_monitor_s soc_ifc_ctrl_monitor_struct);
    //
    // Available struct members:
    //     //    soc_ifc_ctrl_monitor_struct.cptra_obf_key_rand
    //     //    soc_ifc_ctrl_monitor_struct.set_pwrgood
    //     //    soc_ifc_ctrl_monitor_struct.assert_rst
    //     //    soc_ifc_ctrl_monitor_struct.wait_cycles
    //     //    soc_ifc_ctrl_monitor_struct.security_state
    //     //    soc_ifc_ctrl_monitor_struct.set_bootfsm_breakpoint
    //     //    soc_ifc_ctrl_monitor_struct.generic_input_val
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal === 1'b1) @(posedge clk_i);
    //    
    //    How to assign a struct member, named xyz, from a signal.   
    //    All available input signals listed.
    //      soc_ifc_ctrl_monitor_struct.xyz = cptra_pwrgood_i;  //     
    //      soc_ifc_ctrl_monitor_struct.xyz = cptra_rst_b_i;  //     
    //      soc_ifc_ctrl_monitor_struct.xyz = cptra_obf_key_i;  //    [`CLP_OBF_KEY_DWORDS-1:0][31:0] 
    //      soc_ifc_ctrl_monitor_struct.xyz = security_state_i;  //    [2:0] 
    //      soc_ifc_ctrl_monitor_struct.xyz = BootFSM_BrkPoint_i;  //     
    //      soc_ifc_ctrl_monitor_struct.xyz = generic_input_wires_i;  //    [63:0] 
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code 
    // below are examples of how to capture signal values and assign them to 
    // structure members.  All available input signals are listed.  The 'while' 
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe 
    // the next transfer. One clock cycle is consumed between calls to do_monitor.

    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the soc_ifc_ctrl_monitor_struct.
    while (!any_signal_changed()) @(posedge clk_i);
    cptra_pwrgood_r       = cptra_pwrgood_i;
    cptra_rst_b_r         = cptra_rst_b_i;
    cptra_obf_key_r       = cptra_obf_key_i;
    security_state_r      = security_state_i;
    BootFSM_BrkPoint_r    = BootFSM_BrkPoint_i;
    generic_input_wires_r = generic_input_wires_i;
    begin: build_return_struct
         // Variables within the soc_ifc_ctrl_monitor_struct:
         soc_ifc_ctrl_monitor_struct.set_pwrgood            = cptra_pwrgood_i;
         soc_ifc_ctrl_monitor_struct.assert_rst             = !cptra_rst_b_i;
         soc_ifc_ctrl_monitor_struct.cptra_obf_key_rand     = cptra_obf_key_i;
         soc_ifc_ctrl_monitor_struct.security_state         = security_state_i;
         soc_ifc_ctrl_monitor_struct.set_bootfsm_breakpoint = BootFSM_BrkPoint_i;
         soc_ifc_ctrl_monitor_struct.generic_input_val      = generic_input_wires_i;
         soc_ifc_ctrl_monitor_struct.wait_cycles            = 0;
    end
    // pragma uvmf custom do_monitor end
  endtask         
  
 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

