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
//    This interface performs the fuse_ctrl_prim_axi_write_in signal driving.  It is
//     accessed by the uvm fuse_ctrl_prim_axi_write_in driver through a virtual interface
//     handle in the fuse_ctrl_prim_axi_write_in configuration.  It drives the singals passed
//     in through the port connection named bus of type fuse_ctrl_prim_axi_write_in_if.
//
//     Input signals from the fuse_ctrl_prim_axi_write_in_if are assigned to an internal input
//     signal with a _i suffix.  The _i signal should be used for sampling.
//
//     The input signal connections are as follows:
//       bus.signal -> signal_i 
//
//     This bfm drives signals with a _o suffix.  These signals
//     are driven onto signals within fuse_ctrl_prim_axi_write_in_if based on INITIATOR/RESPONDER and/or
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
import fuse_ctrl_prim_axi_write_in_pkg_hdl::*;
`include "src/fuse_ctrl_prim_axi_write_in_macros.svh"

interface fuse_ctrl_prim_axi_write_in_driver_bfm #(
  int AW = 32,
  int DW = 32,
  int IW = 3,
  int UW = 32
  )

  (fuse_ctrl_prim_axi_write_in_if bus);
  // The following pragma and additional ones in-lined further below are for running this BFM on Veloce
  // pragma attribute fuse_ctrl_prim_axi_write_in_driver_bfm partition_interface_xif

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
      $psprintf("The BFM at '%m' has the following parameters: AW=%x DW=%x IW=%x UW=%x ", AW,DW,IW,UW),
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
  tri [AW-1:0] awaddr_i;
  reg [AW-1:0] awaddr_o = 'bz;
  tri [$bits(axi_pkg::axi_burst_e)-1:0] awburst_i;
  reg [$bits(axi_pkg::axi_burst_e)-1:0] awburst_o = 'bz;
  tri [2:0] awsize_i;
  reg [2:0] awsize_o = 'bz;
  tri [7:0] awlen_i;
  reg [7:0] awlen_o = 'bz;
  tri [UW-1:0] awuser_i;
  reg [UW-1:0] awuser_o = 'bz;
  tri [UW-1:0] awid_i;
  reg [UW-1:0] awid_o = 'bz;
  tri  awlock_i;
  reg  awlock_o = 'bz;
  tri  awvalid_i;
  reg  awvalid_o = 'bz;
  tri [DW-1:0] wdata_i;
  reg [DW-1:0] wdata_o = 'bz;
  tri [DW/8-1:0] wstrb_i;
  reg [DW/8-1:0] wstrb_o = 'bz;
  tri  wvalid_i;
  reg  wvalid_o = 'bz;
  tri  wlast_i;
  reg  wlast_o = 'bz;
  tri  bready_i;
  reg  bready_o = 'bz;

  // Bi-directional signals
  

  assign clk_i_i = bus.clk_i;
  assign rst_ni_i = bus.rst_ni;

  // These are signals marked as 'input' by the config file, but the signals will be
  // driven by this BFM if put into RESPONDER mode (flipping all signal directions around)


  // These are signals marked as 'output' by the config file, but the outputs will
  // not be driven by this BFM unless placed in INITIATOR mode.
  assign bus.awaddr = (initiator_responder == INITIATOR) ? awaddr_o : 'bz;
  assign awaddr_i = bus.awaddr;
  assign bus.awburst = (initiator_responder == INITIATOR) ? awburst_o : 'bz;
  assign awburst_i = bus.awburst;
  assign bus.awsize = (initiator_responder == INITIATOR) ? awsize_o : 'bz;
  assign awsize_i = bus.awsize;
  assign bus.awlen = (initiator_responder == INITIATOR) ? awlen_o : 'bz;
  assign awlen_i = bus.awlen;
  assign bus.awuser = (initiator_responder == INITIATOR) ? awuser_o : 'bz;
  assign awuser_i = bus.awuser;
  assign bus.awid = (initiator_responder == INITIATOR) ? awid_o : 'bz;
  assign awid_i = bus.awid;
  assign bus.awlock = (initiator_responder == INITIATOR) ? awlock_o : 'bz;
  assign awlock_i = bus.awlock;
  assign bus.awvalid = (initiator_responder == INITIATOR) ? awvalid_o : 'bz;
  assign awvalid_i = bus.awvalid;
  assign bus.wdata = (initiator_responder == INITIATOR) ? wdata_o : 'bz;
  assign wdata_i = bus.wdata;
  assign bus.wstrb = (initiator_responder == INITIATOR) ? wstrb_o : 'bz;
  assign wstrb_i = bus.wstrb;
  assign bus.wvalid = (initiator_responder == INITIATOR) ? wvalid_o : 'bz;
  assign wvalid_i = bus.wvalid;
  assign bus.wlast = (initiator_responder == INITIATOR) ? wlast_o : 'bz;
  assign wlast_i = bus.wlast;
  assign bus.bready = (initiator_responder == INITIATOR) ? bready_o : 'bz;
  assign bready_i = bus.bready;

  // Proxy handle to UVM driver
  fuse_ctrl_prim_axi_write_in_pkg::fuse_ctrl_prim_axi_write_in_driver #(
    .AW(AW),
    .DW(DW),
    .IW(IW),
    .UW(UW)
    )
  proxy;
  // pragma tbx oneway proxy.my_function_name_in_uvm_driver                 

  // ****************************************************************************
  // **************************************************************************** 
  // Macros that define structs located in fuse_ctrl_prim_axi_write_in_macros.svh
  // ****************************************************************************
  // Struct for passing configuration data from fuse_ctrl_prim_axi_write_in_driver to this BFM
  // ****************************************************************************
  `fuse_ctrl_prim_axi_write_in_CONFIGURATION_STRUCT
  // ****************************************************************************
  // Structs for INITIATOR and RESPONDER data flow
  //*******************************************************************
  // Initiator macro used by fuse_ctrl_prim_axi_write_in_driver and fuse_ctrl_prim_axi_write_in_driver_bfm
  // to communicate initiator driven data to fuse_ctrl_prim_axi_write_in_driver_bfm.           
  `fuse_ctrl_prim_axi_write_in_INITIATOR_STRUCT
    fuse_ctrl_prim_axi_write_in_initiator_s initiator_struct;
  // Responder macro used by fuse_ctrl_prim_axi_write_in_driver and fuse_ctrl_prim_axi_write_in_driver_bfm
  // to communicate Responder driven data to fuse_ctrl_prim_axi_write_in_driver_bfm.
  `fuse_ctrl_prim_axi_write_in_RESPONDER_STRUCT
    fuse_ctrl_prim_axi_write_in_responder_s responder_struct;

  // ****************************************************************************
// pragma uvmf custom reset_condition_and_response begin
  // Always block used to return signals to reset value upon assertion of reset
  always @( negedge rst_ni_i )
     begin
       // RESPONDER mode output signals
       // INITIATOR mode output signals
       awaddr_o <= 'bz;
       awburst_o <= 'bz;
       awsize_o <= 'bz;
       awlen_o <= 'bz;
       awuser_o <= 'bz;
       awid_o <= 'bz;
       awlock_o <= 'bz;
       awvalid_o <= 'bz;
       wdata_o <= 'bz;
       wstrb_o <= 'bz;
       wvalid_o <= 'bz;
       wlast_o <= 'bz;
       bready_o <= 'bz;
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

  function void configure(fuse_ctrl_prim_axi_write_in_configuration_s fuse_ctrl_prim_axi_write_in_configuration_arg); // pragma tbx xtf  
    initiator_responder = fuse_ctrl_prim_axi_write_in_configuration_arg.initiator_responder;
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
       input fuse_ctrl_prim_axi_write_in_initiator_s fuse_ctrl_prim_axi_write_in_initiator_struct, 
       // This argument is used to send data received from the responder
       // back to the sequence item.  The sequence item is returned to the sequence.
       output fuse_ctrl_prim_axi_write_in_responder_s fuse_ctrl_prim_axi_write_in_responder_struct 
       );// pragma tbx xtf  
       // 
       // Members within the fuse_ctrl_prim_axi_write_in_initiator_struct:
       //   logic [AW-1:0] prim_awaddr ;
       //   logic prim_awvalid ;
       //   logic [$bits(axi_pkg::axi_burst_e)] prim_awburst ;
       //   logic [2:0] prim_awsize ;
       //   logic [7:0] prim_awlen ;
       //   logic [UW-1:0] prim_awuser ;
       //   logic [IW-1:0] prim_awid ;
       //   logic prim_awlock ;
       //   logic [DW-1:0] prim_wdata ;
       //   logic [DW/8 - 1:0] prim_wstrb ;
       //   logic prim_wvalid ;
       //   logic prim_wlast ;
       //   logic prim_bready ;
       // Members within the fuse_ctrl_prim_axi_write_in_responder_struct:
       //   logic [AW-1:0] prim_awaddr ;
       //   logic prim_awvalid ;
       //   logic [$bits(axi_pkg::axi_burst_e)] prim_awburst ;
       //   logic [2:0] prim_awsize ;
       //   logic [7:0] prim_awlen ;
       //   logic [UW-1:0] prim_awuser ;
       //   logic [IW-1:0] prim_awid ;
       //   logic prim_awlock ;
       //   logic [DW-1:0] prim_wdata ;
       //   logic [DW/8 - 1:0] prim_wstrb ;
       //   logic prim_wvalid ;
       //   logic prim_wlast ;
       //   logic prim_bready ;
       initiator_struct = fuse_ctrl_prim_axi_write_in_initiator_struct;
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
       //      awaddr_o <= fuse_ctrl_prim_axi_write_in_initiator_struct.xyz;  //    [AW-1:0] 
       //      awburst_o <= fuse_ctrl_prim_axi_write_in_initiator_struct.xyz;  //    [$bits(axi_pkg::axi_burst_e)-1:0] 
       //      awsize_o <= fuse_ctrl_prim_axi_write_in_initiator_struct.xyz;  //    [2:0] 
       //      awlen_o <= fuse_ctrl_prim_axi_write_in_initiator_struct.xyz;  //    [7:0] 
       //      awuser_o <= fuse_ctrl_prim_axi_write_in_initiator_struct.xyz;  //    [UW-1:0] 
       //      awid_o <= fuse_ctrl_prim_axi_write_in_initiator_struct.xyz;  //    [UW-1:0] 
       //      awlock_o <= fuse_ctrl_prim_axi_write_in_initiator_struct.xyz;  //     
       //      awvalid_o <= fuse_ctrl_prim_axi_write_in_initiator_struct.xyz;  //     
       //      wdata_o <= fuse_ctrl_prim_axi_write_in_initiator_struct.xyz;  //    [DW-1:0] 
       //      wstrb_o <= fuse_ctrl_prim_axi_write_in_initiator_struct.xyz;  //    [DW/8-1:0] 
       //      wvalid_o <= fuse_ctrl_prim_axi_write_in_initiator_struct.xyz;  //     
       //      wlast_o <= fuse_ctrl_prim_axi_write_in_initiator_struct.xyz;  //     
       //      bready_o <= fuse_ctrl_prim_axi_write_in_initiator_struct.xyz;  //     
       //    Initiator inout signals
    // Initiate a transfer using the data received.
    @(posedge clk_i_i);
    @(posedge clk_i_i);
    // Wait for the responder to complete the transfer then place the responder data into 
    // fuse_ctrl_prim_axi_write_in_responder_struct.
    @(posedge clk_i_i);
    @(posedge clk_i_i);
    responder_struct = fuse_ctrl_prim_axi_write_in_responder_struct;
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
       output fuse_ctrl_prim_axi_write_in_initiator_s fuse_ctrl_prim_axi_write_in_initiator_struct, 
       // This argument passes transaction variables used by a responder
       // to complete a protocol transfer.  The values come from a sequence item.       
       input fuse_ctrl_prim_axi_write_in_responder_s fuse_ctrl_prim_axi_write_in_responder_struct 
       );// pragma tbx xtf   
  // Variables within the fuse_ctrl_prim_axi_write_in_initiator_struct:
  //   logic [AW-1:0] prim_awaddr ;
  //   logic prim_awvalid ;
  //   logic [$bits(axi_pkg::axi_burst_e)] prim_awburst ;
  //   logic [2:0] prim_awsize ;
  //   logic [7:0] prim_awlen ;
  //   logic [UW-1:0] prim_awuser ;
  //   logic [IW-1:0] prim_awid ;
  //   logic prim_awlock ;
  //   logic [DW-1:0] prim_wdata ;
  //   logic [DW/8 - 1:0] prim_wstrb ;
  //   logic prim_wvalid ;
  //   logic prim_wlast ;
  //   logic prim_bready ;
  // Variables within the fuse_ctrl_prim_axi_write_in_responder_struct:
  //   logic [AW-1:0] prim_awaddr ;
  //   logic prim_awvalid ;
  //   logic [$bits(axi_pkg::axi_burst_e)] prim_awburst ;
  //   logic [2:0] prim_awsize ;
  //   logic [7:0] prim_awlen ;
  //   logic [UW-1:0] prim_awuser ;
  //   logic [IW-1:0] prim_awid ;
  //   logic prim_awlock ;
  //   logic [DW-1:0] prim_wdata ;
  //   logic [DW/8 - 1:0] prim_wstrb ;
  //   logic prim_wvalid ;
  //   logic prim_wlast ;
  //   logic prim_bready ;
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available responder input and inout signals listed.
       //    Responder input signals
       //      fuse_ctrl_prim_axi_write_in_responder_struct.xyz = awaddr_i;  //    [AW-1:0] 
       //      fuse_ctrl_prim_axi_write_in_responder_struct.xyz = awburst_i;  //    [$bits(axi_pkg::axi_burst_e)-1:0] 
       //      fuse_ctrl_prim_axi_write_in_responder_struct.xyz = awsize_i;  //    [2:0] 
       //      fuse_ctrl_prim_axi_write_in_responder_struct.xyz = awlen_i;  //    [7:0] 
       //      fuse_ctrl_prim_axi_write_in_responder_struct.xyz = awuser_i;  //    [UW-1:0] 
       //      fuse_ctrl_prim_axi_write_in_responder_struct.xyz = awid_i;  //    [UW-1:0] 
       //      fuse_ctrl_prim_axi_write_in_responder_struct.xyz = awlock_i;  //     
       //      fuse_ctrl_prim_axi_write_in_responder_struct.xyz = awvalid_i;  //     
       //      fuse_ctrl_prim_axi_write_in_responder_struct.xyz = wdata_i;  //    [DW-1:0] 
       //      fuse_ctrl_prim_axi_write_in_responder_struct.xyz = wstrb_i;  //    [DW/8-1:0] 
       //      fuse_ctrl_prim_axi_write_in_responder_struct.xyz = wvalid_i;  //     
       //      fuse_ctrl_prim_axi_write_in_responder_struct.xyz = wlast_i;  //     
       //      fuse_ctrl_prim_axi_write_in_responder_struct.xyz = bready_i;  //     
       //    Responder inout signals
       //    How to assign a signal, named xyz, from an initiator struct member.   
       //    All available responder output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Responder output signals
       //    Responder inout signals
    
  @(posedge clk_i_i);
  if (!first_transfer) begin
    // Perform transfer response here.   
    // Reply using data recieved in the fuse_ctrl_prim_axi_write_in_responder_struct.
    @(posedge clk_i_i);
    // Reply using data recieved in the transaction handle.
    @(posedge clk_i_i);
  end
    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the fuse_ctrl_prim_axi_write_in_initiator_struct.
    @(posedge clk_i_i);
    @(posedge clk_i_i);
    first_transfer = 0;
  endtask
// pragma uvmf custom respond_and_wait_for_next_transfer end

 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

