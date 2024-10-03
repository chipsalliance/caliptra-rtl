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
// DESCRIPTION: 
//    This interface performs the fuse_ctrl_in_if signal driving.  It is
//     accessed by the uvm fuse_ctrl_in_if driver through a virtual interface
//     handle in the fuse_ctrl_in_if configuration.  It drives the singals passed
//     in through the port connection named bus of type fuse_ctrl_in_if_if.
//
//     Input signals from the fuse_ctrl_in_if_if are assigned to an internal input
//     signal with a _i suffix.  The _i signal should be used for sampling.
//
//     The input signal connections are as follows:
//       bus.signal -> signal_i 
//
//     This bfm drives signals with a _o suffix.  These signals
//     are driven onto signals within fuse_ctrl_in_if_if based on INITIATOR/RESPONDER and/or
//     ARBITRATION/GRANT status.  
//
//     The output signal connections are as follows:
//        signal_o -> bus.signal
//
//                                                                                           
//      Interface functions and tasks used by UVM components:
//
//             configure:
//                   This function gets configuration attributes from the
//                   UVM driver to set any required BFM configuration
//                   variables such as 'initiator_responder'.                                       
//                                                                                           
//             initiate_and_get_response:
//                   This task is used to perform signaling activity for initiating
//                   a protocol transfer.  The task initiates the transfer, using
//                   input data from the initiator struct.  Then the task captures
//                   response data, placing the data into the response struct.
//                   The response struct is returned to the driver class.
//
//             respond_and_wait_for_next_transfer:
//                   This task is used to complete a current transfer as a responder
//                   and then wait for the initiator to start the next transfer.
//                   The task uses data in the responder struct to drive protocol
//                   signals to complete the transfer.  The task then waits for 
//                   the next transfer.  Once the next transfer begins, data from
//                   the initiator is placed into the initiator struct and sent
//                   to the responder sequence for processing to determine 
//                   what data to respond with.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import fuse_ctrl_in_if_pkg_hdl::*;
`include "src/fuse_ctrl_in_if_macros.svh"

interface fuse_ctrl_in_if_driver_bfm #(
  int AlertSyncOn = 3,
  lfsr_seed_t RndConstLfrSeed = RndConstLfsrSeedDefault,
  lsfr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault,
  string MemInitFile = 
  )

  (fuse_ctrl_in_if_if bus);
  // The following pragma and additional ones in-lined further below are for running this BFM on Veloce
  // pragma attribute fuse_ctrl_in_if_driver_bfm partition_interface_xif

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

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i_i;
  tri rst_ni_i;

  // Signal list (all signals are capable of being inputs and outputs for the sake
  // of supporting both INITIATOR and RESPONDER mode operation. Expectation is that 
  // directionality in the config file was from the point-of-view of the INITIATOR

  // INITIATOR mode input signals

  // INITIATOR mode output signals
  tri [$bits(edn_pkg::edn_req_t)-1:0] edn_i_i;
  reg [$bits(edn_pkg::edn_req_t)-1:0] edn_i_o = 'bz;
  tri [NumAlerts * $bits(caliptra_prim_alert_pkg::alert_rx_t)-1:0] alert_rx_i_i;
  reg [NumAlerts * $bits(caliptra_prim_alert_pkg::alert_rx_t)-1:0] alert_rx_i_o = 'bz;
  tri [$bits(ast_pkg::ast_obs_ctrl_t)-1:0] obs_ctrl_i_i;
  reg [$bits(ast_pkg::ast_obs_ctrl_t)-1:0] obs_ctrl_i_o = 'bz;
  tri [$bits(otp_ast_req_t)-1:0] otp_ast_pwr_seq_h_i_i;
  reg [$bits(otp_ast_req_t)-1:0] otp_ast_pwr_seq_h_i_o = 'bz;
  tri  otp_ext_voltage_h_io_i;
  reg  otp_ext_voltage_h_io_o = 'bz;
  tri  scan_en_i_i;
  reg  scan_en_i_o = 'bz;
  tri  scan_rst_ni_i;
  reg  scan_rst_ni_o = 'bz;
  tri  scanmode_i_i;
  reg  scanmode_i_o = 'bz;

  // Bi-directional signals
  

  assign clk_i_i = bus.clk_i;
  assign rst_ni_i = bus.rst_ni;

  // These are signals marked as 'input' by the config file, but the signals will be
  // driven by this BFM if put into RESPONDER mode (flipping all signal directions around)


  // These are signals marked as 'output' by the config file, but the outputs will
  // not be driven by this BFM unless placed in INITIATOR mode.
  assign bus.edn_i = (initiator_responder == INITIATOR) ? edn_i_o : 'bz;
  assign edn_i_i = bus.edn_i;
  assign bus.alert_rx_i = (initiator_responder == INITIATOR) ? alert_rx_i_o : 'bz;
  assign alert_rx_i_i = bus.alert_rx_i;
  assign bus.obs_ctrl_i = (initiator_responder == INITIATOR) ? obs_ctrl_i_o : 'bz;
  assign obs_ctrl_i_i = bus.obs_ctrl_i;
  assign bus.otp_ast_pwr_seq_h_i = (initiator_responder == INITIATOR) ? otp_ast_pwr_seq_h_i_o : 'bz;
  assign otp_ast_pwr_seq_h_i_i = bus.otp_ast_pwr_seq_h_i;
  assign bus.otp_ext_voltage_h_io = (initiator_responder == INITIATOR) ? otp_ext_voltage_h_io_o : 'bz;
  assign otp_ext_voltage_h_io_i = bus.otp_ext_voltage_h_io;
  assign bus.scan_en_i = (initiator_responder == INITIATOR) ? scan_en_i_o : 'bz;
  assign scan_en_i_i = bus.scan_en_i;
  assign bus.scan_rst_ni = (initiator_responder == INITIATOR) ? scan_rst_ni_o : 'bz;
  assign scan_rst_ni_i = bus.scan_rst_ni;
  assign bus.scanmode_i = (initiator_responder == INITIATOR) ? scanmode_i_o : 'bz;
  assign scanmode_i_i = bus.scanmode_i;

  // Proxy handle to UVM driver
  fuse_ctrl_in_if_pkg::fuse_ctrl_in_if_driver #(
    .AlertSyncOn(AlertSyncOn),
    .RndConstLfrSeed(RndConstLfrSeed),
    .RndCnstLfsrPerm(RndCnstLfsrPerm),
    .MemInitFile(MemInitFile)
    )
  proxy;
  // pragma tbx oneway proxy.my_function_name_in_uvm_driver                 

  // ****************************************************************************
  // **************************************************************************** 
  // Macros that define structs located in fuse_ctrl_in_if_macros.svh
  // ****************************************************************************
  // Struct for passing configuration data from fuse_ctrl_in_if_driver to this BFM
  // ****************************************************************************
  `fuse_ctrl_in_if_CONFIGURATION_STRUCT
  // ****************************************************************************
  // Structs for INITIATOR and RESPONDER data flow
  //*******************************************************************
  // Initiator macro used by fuse_ctrl_in_if_driver and fuse_ctrl_in_if_driver_bfm
  // to communicate initiator driven data to fuse_ctrl_in_if_driver_bfm.           
  `fuse_ctrl_in_if_INITIATOR_STRUCT
    fuse_ctrl_in_if_initiator_s initiator_struct;
  // Responder macro used by fuse_ctrl_in_if_driver and fuse_ctrl_in_if_driver_bfm
  // to communicate Responder driven data to fuse_ctrl_in_if_driver_bfm.
  `fuse_ctrl_in_if_RESPONDER_STRUCT
    fuse_ctrl_in_if_responder_s responder_struct;

  // ****************************************************************************
// pragma uvmf custom reset_condition_and_response begin
  // Always block used to return signals to reset value upon assertion of reset
  always @( negedge rst_ni_i )
     begin
       // RESPONDER mode output signals
       // INITIATOR mode output signals
       edn_i_o <= 'bz;
       alert_rx_i_o <= 'bz;
       obs_ctrl_i_o <= 'bz;
       otp_ast_pwr_seq_h_i_o <= 'bz;
       otp_ext_voltage_h_io_o <= 'bz;
       scan_en_i_o <= 'bz;
       scan_rst_ni_o <= 'bz;
       scanmode_i_o <= 'bz;
       // Bi-directional signals
 
     end    
// pragma uvmf custom reset_condition_and_response end

  // pragma uvmf custom interface_item_additional begin
  // pragma uvmf custom interface_item_additional end

  //******************************************************************
  // The configure() function is used to pass agent configuration
  // variables to the driver BFM.  It is called by the driver within
  // the agent at the beginning of the simulation.  It may be called 
  // during the simulation if agent configuration variables are updated
  // and the driver BFM needs to be aware of the new configuration 
  // variables.
  //

  function void configure(fuse_ctrl_in_if_configuration_s fuse_ctrl_in_if_configuration_arg); // pragma tbx xtf  
    initiator_responder = fuse_ctrl_in_if_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction                                                                             

// pragma uvmf custom initiate_and_get_response begin
// ****************************************************************************
// UVMF_CHANGE_ME
// This task is used by an initator.  The task first initiates a transfer then
// waits for the responder to complete the transfer.
    task initiate_and_get_response( 
       // This argument passes transaction variables used by an initiator
       // to perform the initial part of a protocol transfer.  The values
       // come from a sequence item created in a sequence.
       input fuse_ctrl_in_if_initiator_s fuse_ctrl_in_if_initiator_struct, 
       // This argument is used to send data received from the responder
       // back to the sequence item.  The sequence item is returned to the sequence.
       output fuse_ctrl_in_if_responder_s fuse_ctrl_in_if_responder_struct 
       );// pragma tbx xtf  
       // 
       // Members within the fuse_ctrl_in_if_initiator_struct:
       //   caliptra_prim_alert_pkg::alert_rx_t set_alert_rx_i ;
       // Members within the fuse_ctrl_in_if_responder_struct:
       //   caliptra_prim_alert_pkg::alert_rx_t set_alert_rx_i ;
       initiator_struct = fuse_ctrl_in_if_initiator_struct;
       //
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available initiator input and inout signals listed.
       //    Initiator input signals
       //    Initiator inout signals
       //    How to assign a signal from an initiator struct member named xyz.   
       //    All available initiator output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Initiator output signals
       //      edn_i_o <= fuse_ctrl_in_if_initiator_struct.xyz;  //    [$bits(edn_pkg::edn_req_t)-1:0] 
       //      alert_rx_i_o <= fuse_ctrl_in_if_initiator_struct.xyz;  //    [NumAlerts * $bits(caliptra_prim_alert_pkg::alert_rx_t)-1:0] 
       //      obs_ctrl_i_o <= fuse_ctrl_in_if_initiator_struct.xyz;  //    [$bits(ast_pkg::ast_obs_ctrl_t)-1:0] 
       //      otp_ast_pwr_seq_h_i_o <= fuse_ctrl_in_if_initiator_struct.xyz;  //    [$bits(otp_ast_req_t)-1:0] 
       //      otp_ext_voltage_h_io_o <= fuse_ctrl_in_if_initiator_struct.xyz;  //     
       //      scan_en_i_o <= fuse_ctrl_in_if_initiator_struct.xyz;  //     
       //      scan_rst_ni_o <= fuse_ctrl_in_if_initiator_struct.xyz;  //     
       //      scanmode_i_o <= fuse_ctrl_in_if_initiator_struct.xyz;  //     
       //    Initiator inout signals
    // Initiate a transfer using the data received.
    @(posedge clk_i_i);
    @(posedge clk_i_i);
    // Wait for the responder to complete the transfer then place the responder data into 
    // fuse_ctrl_in_if_responder_struct.
    @(posedge clk_i_i);
    @(posedge clk_i_i);
    responder_struct = fuse_ctrl_in_if_responder_struct;
  endtask        
// pragma uvmf custom initiate_and_get_response end

// pragma uvmf custom respond_and_wait_for_next_transfer begin
// ****************************************************************************
// The first_transfer variable is used to prevent completing a transfer in the 
// first call to this task.  For the first call to this task, there is not
// current transfer to complete.
bit first_transfer=1;

// UVMF_CHANGE_ME
// This task is used by a responder.  The task first completes the current 
// transfer in progress then waits for the initiator to start the next transfer.
  task respond_and_wait_for_next_transfer( 
       // This argument is used to send data received from the initiator
       // back to the sequence item.  The sequence determines how to respond.
       output fuse_ctrl_in_if_initiator_s fuse_ctrl_in_if_initiator_struct, 
       // This argument passes transaction variables used by a responder
       // to complete a protocol transfer.  The values come from a sequence item.       
       input fuse_ctrl_in_if_responder_s fuse_ctrl_in_if_responder_struct 
       );// pragma tbx xtf   
  // Variables within the fuse_ctrl_in_if_initiator_struct:
  //   caliptra_prim_alert_pkg::alert_rx_t set_alert_rx_i ;
  // Variables within the fuse_ctrl_in_if_responder_struct:
  //   caliptra_prim_alert_pkg::alert_rx_t set_alert_rx_i ;
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available responder input and inout signals listed.
       //    Responder input signals
       //      fuse_ctrl_in_if_responder_struct.xyz = edn_i_i;  //    [$bits(edn_pkg::edn_req_t)-1:0] 
       //      fuse_ctrl_in_if_responder_struct.xyz = alert_rx_i_i;  //    [NumAlerts * $bits(caliptra_prim_alert_pkg::alert_rx_t)-1:0] 
       //      fuse_ctrl_in_if_responder_struct.xyz = obs_ctrl_i_i;  //    [$bits(ast_pkg::ast_obs_ctrl_t)-1:0] 
       //      fuse_ctrl_in_if_responder_struct.xyz = otp_ast_pwr_seq_h_i_i;  //    [$bits(otp_ast_req_t)-1:0] 
       //      fuse_ctrl_in_if_responder_struct.xyz = otp_ext_voltage_h_io_i;  //     
       //      fuse_ctrl_in_if_responder_struct.xyz = scan_en_i_i;  //     
       //      fuse_ctrl_in_if_responder_struct.xyz = scan_rst_ni_i;  //     
       //      fuse_ctrl_in_if_responder_struct.xyz = scanmode_i_i;  //     
       //    Responder inout signals
       //    How to assign a signal, named xyz, from an initiator struct member.   
       //    All available responder output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Responder output signals
       //    Responder inout signals
    
  @(posedge clk_i_i);
  if (!first_transfer) begin
    // Perform transfer response here.   
    // Reply using data recieved in the fuse_ctrl_in_if_responder_struct.
    @(posedge clk_i_i);
    // Reply using data recieved in the transaction handle.
    @(posedge clk_i_i);
  end
    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the fuse_ctrl_in_if_initiator_struct.
    @(posedge clk_i_i);
    @(posedge clk_i_i);
    first_transfer = 0;
  endtask
// pragma uvmf custom respond_and_wait_for_next_transfer end

 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

