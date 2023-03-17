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
//    This interface performs the pv_write signal driving.  It is
//     accessed by the uvm pv_write driver through a virtual interface
//     handle in the pv_write configuration.  It drives the singals passed
//     in through the port connection named bus of type pv_write_if.
//
//     Input signals from the pv_write_if are assigned to an internal input
//     signal with a _i suffix.  The _i signal should be used for sampling.
//
//     The input signal connections are as follows:
//       bus.signal -> signal_i 
//
//     This bfm drives signals with a _o suffix.  These signals
//     are driven onto signals within pv_write_if based on INITIATOR/RESPONDER and/or
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
import pv_write_pkg_hdl::*;
`include "src/pv_write_macros.svh"

interface pv_write_driver_bfm #(
  string PV_WRITE_REQUESTOR = "SHA512"
  )

  (pv_write_if bus);
  // The following pragma and additional ones in-lined further below are for running this BFM on Veloce
  // pragma attribute pv_write_driver_bfm partition_interface_xif

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
      $psprintf("The BFM at '%m' has the following parameters: PV_WRITE_REQUESTOR=%x ", PV_WRITE_REQUESTOR),
      UVM_DEBUG)
end
`endif

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri dummy_i;

  // Signal list (all signals are capable of being inputs and outputs for the sake
  // of supporting both INITIATOR and RESPONDER mode operation. Expectation is that 
  // directionality in the config file was from the point-of-view of the INITIATOR

  // INITIATOR mode input signals
  tri [$bits(pv_defines_pkg::pv_wr_resp_t)-1:0] pv_wr_resp_i;
  reg [$bits(pv_defines_pkg::pv_wr_resp_t)-1:0] pv_wr_resp_o = 'b0;

  // INITIATOR mode output signals
  tri [$bits(pv_defines_pkg::pv_write_t)-1:0] pv_write_i;
  reg [$bits(pv_defines_pkg::pv_write_t)-1:0] pv_write_o = 'b0;

  // Bi-directional signals
  

  assign clk_i = bus.clk;
  assign dummy_i = bus.dummy;

  // These are signals marked as 'input' by the config file, but the signals will be
  // driven by this BFM if put into RESPONDER mode (flipping all signal directions around)
  assign pv_wr_resp_i = bus.pv_wr_resp;
  assign bus.pv_wr_resp = (initiator_responder == RESPONDER) ? pv_wr_resp_o : 'bz;


  // These are signals marked as 'output' by the config file, but the outputs will
  // not be driven by this BFM unless placed in INITIATOR mode.
  assign bus.pv_write = (initiator_responder == INITIATOR) ? pv_write_o : 'bz;
  assign pv_write_i = bus.pv_write;

  // Proxy handle to UVM driver
  pv_write_pkg::pv_write_driver #(
    .PV_WRITE_REQUESTOR(PV_WRITE_REQUESTOR)
    )
  proxy;
  // pragma tbx oneway proxy.my_function_name_in_uvm_driver                 

  // ****************************************************************************
  // **************************************************************************** 
  // Macros that define structs located in pv_write_macros.svh
  // ****************************************************************************
  // Struct for passing configuration data from pv_write_driver to this BFM
  // ****************************************************************************
  `pv_write_CONFIGURATION_STRUCT
  // ****************************************************************************
  // Structs for INITIATOR and RESPONDER data flow
  //*******************************************************************
  // Initiator macro used by pv_write_driver and pv_write_driver_bfm
  // to communicate initiator driven data to pv_write_driver_bfm.           
  `pv_write_INITIATOR_STRUCT
    pv_write_initiator_s initiator_struct;
  // Responder macro used by pv_write_driver and pv_write_driver_bfm
  // to communicate Responder driven data to pv_write_driver_bfm.
  `pv_write_RESPONDER_STRUCT
    pv_write_responder_s responder_struct;

  // ****************************************************************************
// pragma uvmf custom reset_condition_and_response begin
  // Always block used to return signals to reset value upon assertion of reset
  always @( negedge dummy_i )
     begin
       // RESPONDER mode output signals
       pv_wr_resp_o <= 'bz;
       // INITIATOR mode output signals
       pv_write_o <= 'bz;
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

  function void configure(pv_write_configuration_s pv_write_configuration_arg); // pragma tbx xtf  
    initiator_responder = pv_write_configuration_arg.initiator_responder;
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
       input pv_write_initiator_s pv_write_initiator_struct, 
       // This argument is used to send data received from the responder
       // back to the sequence item.  The sequence item is returned to the sequence.
       output pv_write_responder_s pv_write_responder_struct 
       );// pragma tbx xtf  
       // 
       // Members within the pv_write_initiator_struct:
       //   logic write_en ;
       //   logic   [PV_ENTRY_ADDR_W-1:0] write_entry ;
       //   logic   [PV_ENTRY_SIZE_WIDTH-1:0] write_offset ;
       //   logic   [PV_DATA_W-1:0] write_data ;
       //   logic error ;
       // Members within the pv_write_responder_struct:
       //   logic write_en ;
       //   logic   [PV_ENTRY_ADDR_W-1:0] write_entry ;
       //   logic   [PV_ENTRY_SIZE_WIDTH-1:0] write_offset ;
       //   logic   [PV_DATA_W-1:0] write_data ;
       //   logic error ;
       initiator_struct = pv_write_initiator_struct;
       //
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available initiator input and inout signals listed.
       //    Initiator input signals
       //      pv_write_responder_struct.xyz = pv_wr_resp_i;  //    [$bits(pv_defines_pkg::pv_wr_resp_t)-1:0] 
       //    Initiator inout signals
       //    How to assign a signal from an initiator struct member named xyz.   
       //    All available initiator output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Initiator output signals
       //      pv_write_o <= pv_write_initiator_struct.xyz;  //    [$bits(pv_defines_pkg::pv_write_t)-1:0] 
       //    Initiator inout signals
    // Initiate a transfer using the data received.
    pv_write_o <= {
        initiator_struct.write_en,
        initiator_struct.write_entry,
        initiator_struct.write_offset,
        initiator_struct.write_data
    };

    @(posedge clk_i);
    pv_write_o[41] <= 1'b0; //Set write_en to 0 after txn is complete
    // Wait for the responder to complete the transfer then place the responder data into 
    // pv_write_responder_struct.
    pv_write_responder_struct.write_en          = pv_write_i[41];
    pv_write_responder_struct.write_entry       = pv_write_i[40:36];
    pv_write_responder_struct.write_offset      = pv_write_i[35:32];
    pv_write_responder_struct.write_data        = pv_write_i[31:0];
    
    responder_struct = pv_write_responder_struct;
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
       output pv_write_initiator_s pv_write_initiator_struct, 
       // This argument passes transaction variables used by a responder
       // to complete a protocol transfer.  The values come from a sequence item.       
       input pv_write_responder_s pv_write_responder_struct 
       );// pragma tbx xtf   
  // Variables within the pv_write_initiator_struct:
  //   logic write_en ;
  //   logic   [PV_ENTRY_ADDR_W-1:0] write_entry ;
  //   logic   [PV_ENTRY_SIZE_WIDTH-1:0] write_offset ;
  //   logic   [PV_DATA_W-1:0] write_data ;
  //   logic error ;
  // Variables within the pv_write_responder_struct:
  //   logic write_en ;
  //   logic   [PV_ENTRY_ADDR_W-1:0] write_entry ;
  //   logic   [PV_ENTRY_SIZE_WIDTH-1:0] write_offset ;
  //   logic   [PV_DATA_W-1:0] write_data ;
  //   logic error ;
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available responder input and inout signals listed.
       //    Responder input signals
       //      pv_write_responder_struct.xyz = pv_write_i;  //    [$bits(pv_defines_pkg::pv_write_t)-1:0] 
       //    Responder inout signals
       //    How to assign a signal, named xyz, from an initiator struct member.   
       //    All available responder output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Responder output signals
       //      pv_wr_resp_o <= pv_write_initiator_struct.xyz;  //    [$bits(pv_defines_pkg::pv_wr_resp_t)-1:0] 
       //    Responder inout signals
    
  @(posedge clk_i);
  if (!first_transfer) begin
    // Perform transfer response here.   
    // Reply using data recieved in the pv_write_responder_struct.
    @(posedge clk_i);
    // Reply using data recieved in the transaction handle.
    @(posedge clk_i);
  end
    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the pv_write_initiator_struct.
    @(posedge clk_i);
    @(posedge clk_i);
    first_transfer = 0;
  endtask
// pragma uvmf custom respond_and_wait_for_next_transfer end

 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

