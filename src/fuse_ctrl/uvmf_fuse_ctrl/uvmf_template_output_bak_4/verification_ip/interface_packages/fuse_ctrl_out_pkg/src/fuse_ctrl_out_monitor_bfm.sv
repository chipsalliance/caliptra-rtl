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
// DESCRIPTION: This interface performs the fuse_ctrl_out signal monitoring.
//      It is accessed by the uvm fuse_ctrl_out monitor through a virtual
//      interface handle in the fuse_ctrl_out configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type fuse_ctrl_out_if.
//
//     Input signals from the fuse_ctrl_out_if are assigned to an internal input
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
//                   blocks until an operation on the fuse_ctrl_out bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import fuse_ctrl_out_pkg_hdl::*;
`include "src/fuse_ctrl_out_macros.svh"


interface fuse_ctrl_out_monitor_bfm #(
  int AlertSyncOn = 3,
  lfsr_seed_t RndConstLfrSeed = RndConstLfsrSeedDefault,
  lsfr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault,
  string MemInitFile = 
  )

  ( fuse_ctrl_out_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute fuse_ctrl_out_monitor_bfm partition_interface_xif                                  

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
      $psprintf("The BFM at '%m' has the following parameters: AlertSyncOn=%x RndConstLfrSeed=%x RndCnstLfsrPerm=%x MemInitFile=%x ", AlertSyncOn,RndConstLfrSeed,RndCnstLfsrPerm,MemInitFile),
      UVM_DEBUG)
end
`endif


  // Structure used to pass transaction data from monitor BFM to monitor class in agent.
`fuse_ctrl_out_MONITOR_STRUCT
  fuse_ctrl_out_monitor_s fuse_ctrl_out_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `fuse_ctrl_out_CONFIGURATION_STRUCT
 

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i_i;
  tri rst_ni_i;
  tri [$bits(edn_pkg::edn_req_t)-1:0] edn_o_i;
  tri  intr_otp_operation_done_o_i;
  tri  intr_otp_error_o_i;
  tri [NumAlerts * $bits(caliptra_prim_alert_pkg::alert_tx_t)-1:0] alert_tx_o_i;
  tri [7:0] otp_obs_o_i;
  tri [$bits(caliptra_otp_ctrl_pkg::otp_ast_req_t)-1:0] otp_ast_pwr_seq_o_i;
  tri [$bits(otp_broadcast_t)-1:0] otp_broadcast_o_i;
  tri [OtpTestVectWidth-1:0] cio_test_o_i;
  tri [OtpTestVectWidth-1:0] cio_test_en_o_i;
  assign clk_i_i = bus.clk_i;
  assign rst_ni_i = bus.rst_ni;
  assign edn_o_i = bus.edn_o;
  assign intr_otp_operation_done_o_i = bus.intr_otp_operation_done_o;
  assign intr_otp_error_o_i = bus.intr_otp_error_o;
  assign alert_tx_o_i = bus.alert_tx_o;
  assign otp_obs_o_i = bus.otp_obs_o;
  assign otp_ast_pwr_seq_o_i = bus.otp_ast_pwr_seq_o;
  assign otp_broadcast_o_i = bus.otp_broadcast_o;
  assign cio_test_o_i = bus.cio_test_o;
  assign cio_test_en_o_i = bus.cio_test_en_o;

  // Proxy handle to UVM monitor
  fuse_ctrl_out_pkg::fuse_ctrl_out_monitor #(
    .AlertSyncOn(AlertSyncOn),
    .RndConstLfrSeed(RndConstLfrSeed),
    .RndCnstLfsrPerm(RndCnstLfsrPerm),
    .MemInitFile(MemInitFile)
    )
 proxy;
  // pragma tbx oneway proxy.notify_transaction                 

  // pragma uvmf custom interface_item_additional begin
  // pragma uvmf custom interface_item_additional end
  
  //******************************************************************                         
  task wait_for_reset();// pragma tbx xtf  
    @(posedge clk_i_i) ;                                                                    
    do_wait_for_reset();                                                                   
  endtask                                                                                   

  // ****************************************************************************              
  task do_wait_for_reset(); 
  // pragma uvmf custom reset_condition begin
    wait ( rst_ni_i === 1 ) ;                                                              
    @(posedge clk_i_i) ;                                                                    
  // pragma uvmf custom reset_condition end                                                                
  endtask    

  //******************************************************************                         
 
  task wait_for_num_clocks(input int unsigned count); // pragma tbx xtf 
    @(posedge clk_i_i);  
                                                                   
    repeat (count-1) @(posedge clk_i_i);                                                    
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
      @(posedge clk_i_i);  
      do_monitor( fuse_ctrl_out_monitor_struct );
                                                                 
 
      proxy.notify_transaction( fuse_ctrl_out_monitor_struct );
 
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
    function void configure(fuse_ctrl_out_configuration_s fuse_ctrl_out_configuration_arg); // pragma tbx xtf  
    initiator_responder = fuse_ctrl_out_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction   


  // ****************************************************************************  
            
  task do_monitor(output fuse_ctrl_out_monitor_s fuse_ctrl_out_monitor_struct);
    //
    // Available struct members:
    //     //    fuse_ctrl_out_monitor_struct.pwr_otp_o
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal === 1'b1) @(posedge clk_i_i);
    //    
    //    How to assign a struct member, named xyz, from a signal.   
    //    All available input signals listed.
    //      fuse_ctrl_out_monitor_struct.xyz = edn_o_i;  //    [$bits(edn_pkg::edn_req_t)-1:0] 
    //      fuse_ctrl_out_monitor_struct.xyz = intr_otp_operation_done_o_i;  //     
    //      fuse_ctrl_out_monitor_struct.xyz = intr_otp_error_o_i;  //     
    //      fuse_ctrl_out_monitor_struct.xyz = alert_tx_o_i;  //    [NumAlerts * $bits(caliptra_prim_alert_pkg::alert_tx_t)-1:0] 
    //      fuse_ctrl_out_monitor_struct.xyz = otp_obs_o_i;  //    [7:0] 
    //      fuse_ctrl_out_monitor_struct.xyz = otp_ast_pwr_seq_o_i;  //    [$bits(caliptra_otp_ctrl_pkg::otp_ast_req_t)-1:0] 
    //      fuse_ctrl_out_monitor_struct.xyz = otp_broadcast_o_i;  //    [$bits(otp_broadcast_t)-1:0] 
    //      fuse_ctrl_out_monitor_struct.xyz = cio_test_o_i;  //    [OtpTestVectWidth-1:0] 
    //      fuse_ctrl_out_monitor_struct.xyz = cio_test_en_o_i;  //    [OtpTestVectWidth-1:0] 
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code 
    // below are examples of how to capture signal values and assign them to 
    // structure members.  All available input signals are listed.  The 'while' 
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe 
    // the next transfer. One clock cycle is consumed between calls to do_monitor.
    @(posedge clk_i_i);
    @(posedge clk_i_i);
    @(posedge clk_i_i);
    @(posedge clk_i_i);
    // pragma uvmf custom do_monitor end
  endtask         
  
 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

