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
//    This interface performs the fuse_ctrl_secreg_axi_read_in signal driving.  It is
//     accessed by the uvm fuse_ctrl_secreg_axi_read_in driver through a virtual interface
//     handle in the fuse_ctrl_secreg_axi_read_in configuration.  It drives the singals passed
//     in through the port connection named bus of type fuse_ctrl_secreg_axi_read_in_if.
//
//     Input signals from the fuse_ctrl_secreg_axi_read_in_if are assigned to an internal input
//     signal with a _i suffix.  The _i signal should be used for sampling.
//
//     The input signal connections are as follows:
//       bus.signal -> signal_i 
//
//     This bfm drives signals with a _o suffix.  These signals
//     are driven onto signals within fuse_ctrl_secreg_axi_read_in_if based on INITIATOR/RESPONDER and/or
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
import fuse_ctrl_secreg_axi_read_in_pkg_hdl::*;
`include "src/fuse_ctrl_secreg_axi_read_in_macros.svh"

interface fuse_ctrl_secreg_axi_read_in_driver_bfm #(
  int AW = 32,
  int DW = 32,
  int IW = 3,
  int UW = 32
  )

  (fuse_ctrl_secreg_axi_read_in_if bus);
  // The following pragma and additional ones in-lined further below are for running this BFM on Veloce
  // pragma attribute fuse_ctrl_secreg_axi_read_in_driver_bfm partition_interface_xif

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
  tri [AW-1:0] araddr_i;
  reg [AW-1:0] araddr_o = 'bz;
  tri [$bits(axi_pkg::axi_burst_e)-1:0] arburst_i;
  reg [$bits(axi_pkg::axi_burst_e)-1:0] arburst_o = 'bz;
  tri [2:0] arsize_i;
  reg [2:0] arsize_o = 'bz;
  tri [7:0] arlen_i;
  reg [7:0] arlen_o = 'bz;
  tri [UW-1:0] aruser_i;
  reg [UW-1:0] aruser_o = 'bz;
  tri [IW-1:0] arid_i;
  reg [IW-1:0] arid_o = 'bz;
  tri  arlock_i;
  reg  arlock_o = 'bz;
  tri  arvalid_i;
  reg  arvalid_o = 'bz;
  tri  rready_i;
  reg  rready_o = 'bz;

  // Bi-directional signals
  

  assign clk_i_i = bus.clk_i;
  assign rst_ni_i = bus.rst_ni;

  // These are signals marked as 'input' by the config file, but the signals will be
  // driven by this BFM if put into RESPONDER mode (flipping all signal directions around)


  // These are signals marked as 'output' by the config file, but the outputs will
  // not be driven by this BFM unless placed in INITIATOR mode.
  assign bus.araddr = (initiator_responder == INITIATOR) ? araddr_o : 'bz;
  assign araddr_i = bus.araddr;
  assign bus.arburst = (initiator_responder == INITIATOR) ? arburst_o : 'bz;
  assign arburst_i = bus.arburst;
  assign bus.arsize = (initiator_responder == INITIATOR) ? arsize_o : 'bz;
  assign arsize_i = bus.arsize;
  assign bus.arlen = (initiator_responder == INITIATOR) ? arlen_o : 'bz;
  assign arlen_i = bus.arlen;
  assign bus.aruser = (initiator_responder == INITIATOR) ? aruser_o : 'bz;
  assign aruser_i = bus.aruser;
  assign bus.arid = (initiator_responder == INITIATOR) ? arid_o : 'bz;
  assign arid_i = bus.arid;
  assign bus.arlock = (initiator_responder == INITIATOR) ? arlock_o : 'bz;
  assign arlock_i = bus.arlock;
  assign bus.arvalid = (initiator_responder == INITIATOR) ? arvalid_o : 'bz;
  assign arvalid_i = bus.arvalid;
  assign bus.rready = (initiator_responder == INITIATOR) ? rready_o : 'bz;
  assign rready_i = bus.rready;

  // Proxy handle to UVM driver
  fuse_ctrl_secreg_axi_read_in_pkg::fuse_ctrl_secreg_axi_read_in_driver #(
    .AW(AW),
    .DW(DW),
    .IW(IW),
    .UW(UW)
    )
  proxy;
  // pragma tbx oneway proxy.my_function_name_in_uvm_driver                 

  // ****************************************************************************
  // **************************************************************************** 
  // Macros that define structs located in fuse_ctrl_secreg_axi_read_in_macros.svh
  // ****************************************************************************
  // Struct for passing configuration data from fuse_ctrl_secreg_axi_read_in_driver to this BFM
  // ****************************************************************************
  `fuse_ctrl_secreg_axi_read_in_CONFIGURATION_STRUCT
  // ****************************************************************************
  // Structs for INITIATOR and RESPONDER data flow
  //*******************************************************************
  // Initiator macro used by fuse_ctrl_secreg_axi_read_in_driver and fuse_ctrl_secreg_axi_read_in_driver_bfm
  // to communicate initiator driven data to fuse_ctrl_secreg_axi_read_in_driver_bfm.           
  `fuse_ctrl_secreg_axi_read_in_INITIATOR_STRUCT
    fuse_ctrl_secreg_axi_read_in_initiator_s initiator_struct;
  // Responder macro used by fuse_ctrl_secreg_axi_read_in_driver and fuse_ctrl_secreg_axi_read_in_driver_bfm
  // to communicate Responder driven data to fuse_ctrl_secreg_axi_read_in_driver_bfm.
  `fuse_ctrl_secreg_axi_read_in_RESPONDER_STRUCT
    fuse_ctrl_secreg_axi_read_in_responder_s responder_struct;

  // ****************************************************************************
// pragma uvmf custom reset_condition_and_response begin
  // Always block used to return signals to reset value upon assertion of reset
  always @( negedge rst_ni_i )
     begin
       // RESPONDER mode output signals
       // INITIATOR mode output signals
       araddr_o <= 'bz;
       arburst_o <= 'bz;
       arsize_o <= 'bz;
       arlen_o <= 'bz;
       aruser_o <= 'bz;
       arid_o <= 'bz;
       arlock_o <= 'bz;
       arvalid_o <= 'bz;
       rready_o <= 'bz;
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

  function void configure(fuse_ctrl_secreg_axi_read_in_configuration_s fuse_ctrl_secreg_axi_read_in_configuration_arg); // pragma tbx xtf  
    initiator_responder = fuse_ctrl_secreg_axi_read_in_configuration_arg.initiator_responder;
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
       input fuse_ctrl_secreg_axi_read_in_initiator_s fuse_ctrl_secreg_axi_read_in_initiator_struct, 
       // This argument is used to send data received from the responder
       // back to the sequence item.  The sequence item is returned to the sequence.
       output fuse_ctrl_secreg_axi_read_in_responder_s fuse_ctrl_secreg_axi_read_in_responder_struct 
       );// pragma tbx xtf  
       // 
       // Members within the fuse_ctrl_secreg_axi_read_in_initiator_struct:
       //   logic [AW-1:0] secreg_araddr ;
       //   logic secreg_arvalid ;
       //   logic [$bits(axi_pkg::axi_burst_e)] secreg_arburst ;
       //   logic [2:0] secreg_arsize ;
       //   logic [7:0] secreg_arlen ;
       //   logic [UW-1:0] secreg_aruser ;
       //   logic [IW-1:0] secreg_arid ;
       //   logic secreg_arlock ;
       //   logic secreg_rready ;
       // Members within the fuse_ctrl_secreg_axi_read_in_responder_struct:
       //   logic [AW-1:0] secreg_araddr ;
       //   logic secreg_arvalid ;
       //   logic [$bits(axi_pkg::axi_burst_e)] secreg_arburst ;
       //   logic [2:0] secreg_arsize ;
       //   logic [7:0] secreg_arlen ;
       //   logic [UW-1:0] secreg_aruser ;
       //   logic [IW-1:0] secreg_arid ;
       //   logic secreg_arlock ;
       //   logic secreg_rready ;
       initiator_struct = fuse_ctrl_secreg_axi_read_in_initiator_struct;
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
       //      araddr_o <= fuse_ctrl_secreg_axi_read_in_initiator_struct.xyz;  //    [AW-1:0] 
       //      arburst_o <= fuse_ctrl_secreg_axi_read_in_initiator_struct.xyz;  //    [$bits(axi_pkg::axi_burst_e)-1:0] 
       //      arsize_o <= fuse_ctrl_secreg_axi_read_in_initiator_struct.xyz;  //    [2:0] 
       //      arlen_o <= fuse_ctrl_secreg_axi_read_in_initiator_struct.xyz;  //    [7:0] 
       //      aruser_o <= fuse_ctrl_secreg_axi_read_in_initiator_struct.xyz;  //    [UW-1:0] 
       //      arid_o <= fuse_ctrl_secreg_axi_read_in_initiator_struct.xyz;  //    [IW-1:0] 
       //      arlock_o <= fuse_ctrl_secreg_axi_read_in_initiator_struct.xyz;  //     
       //      arvalid_o <= fuse_ctrl_secreg_axi_read_in_initiator_struct.xyz;  //     
       //      rready_o <= fuse_ctrl_secreg_axi_read_in_initiator_struct.xyz;  //     
       //    Initiator inout signals
    // Initiate a transfer using the data received.
    @(posedge clk_i_i);
    @(posedge clk_i_i);
    // Wait for the responder to complete the transfer then place the responder data into 
    // fuse_ctrl_secreg_axi_read_in_responder_struct.
    @(posedge clk_i_i);
    @(posedge clk_i_i);
    responder_struct = fuse_ctrl_secreg_axi_read_in_responder_struct;
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
       output fuse_ctrl_secreg_axi_read_in_initiator_s fuse_ctrl_secreg_axi_read_in_initiator_struct, 
       // This argument passes transaction variables used by a responder
       // to complete a protocol transfer.  The values come from a sequence item.       
       input fuse_ctrl_secreg_axi_read_in_responder_s fuse_ctrl_secreg_axi_read_in_responder_struct 
       );// pragma tbx xtf   
  // Variables within the fuse_ctrl_secreg_axi_read_in_initiator_struct:
  //   logic [AW-1:0] secreg_araddr ;
  //   logic secreg_arvalid ;
  //   logic [$bits(axi_pkg::axi_burst_e)] secreg_arburst ;
  //   logic [2:0] secreg_arsize ;
  //   logic [7:0] secreg_arlen ;
  //   logic [UW-1:0] secreg_aruser ;
  //   logic [IW-1:0] secreg_arid ;
  //   logic secreg_arlock ;
  //   logic secreg_rready ;
  // Variables within the fuse_ctrl_secreg_axi_read_in_responder_struct:
  //   logic [AW-1:0] secreg_araddr ;
  //   logic secreg_arvalid ;
  //   logic [$bits(axi_pkg::axi_burst_e)] secreg_arburst ;
  //   logic [2:0] secreg_arsize ;
  //   logic [7:0] secreg_arlen ;
  //   logic [UW-1:0] secreg_aruser ;
  //   logic [IW-1:0] secreg_arid ;
  //   logic secreg_arlock ;
  //   logic secreg_rready ;
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available responder input and inout signals listed.
       //    Responder input signals
       //      fuse_ctrl_secreg_axi_read_in_responder_struct.xyz = araddr_i;  //    [AW-1:0] 
       //      fuse_ctrl_secreg_axi_read_in_responder_struct.xyz = arburst_i;  //    [$bits(axi_pkg::axi_burst_e)-1:0] 
       //      fuse_ctrl_secreg_axi_read_in_responder_struct.xyz = arsize_i;  //    [2:0] 
       //      fuse_ctrl_secreg_axi_read_in_responder_struct.xyz = arlen_i;  //    [7:0] 
       //      fuse_ctrl_secreg_axi_read_in_responder_struct.xyz = aruser_i;  //    [UW-1:0] 
       //      fuse_ctrl_secreg_axi_read_in_responder_struct.xyz = arid_i;  //    [IW-1:0] 
       //      fuse_ctrl_secreg_axi_read_in_responder_struct.xyz = arlock_i;  //     
       //      fuse_ctrl_secreg_axi_read_in_responder_struct.xyz = arvalid_i;  //     
       //      fuse_ctrl_secreg_axi_read_in_responder_struct.xyz = rready_i;  //     
       //    Responder inout signals
       //    How to assign a signal, named xyz, from an initiator struct member.   
       //    All available responder output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Responder output signals
       //    Responder inout signals
    
  @(posedge clk_i_i);
  if (!first_transfer) begin
    // Perform transfer response here.   
    // Reply using data recieved in the fuse_ctrl_secreg_axi_read_in_responder_struct.
    @(posedge clk_i_i);
    // Reply using data recieved in the transaction handle.
    @(posedge clk_i_i);
  end
    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the fuse_ctrl_secreg_axi_read_in_initiator_struct.
    @(posedge clk_i_i);
    @(posedge clk_i_i);
    first_transfer = 0;
  endtask
// pragma uvmf custom respond_and_wait_for_next_transfer end

 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

