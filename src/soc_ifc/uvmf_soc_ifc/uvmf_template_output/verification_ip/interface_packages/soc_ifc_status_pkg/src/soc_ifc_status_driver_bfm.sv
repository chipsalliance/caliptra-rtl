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
//    This interface performs the soc_ifc_status signal driving.  It is
//     accessed by the uvm soc_ifc_status driver through a virtual interface
//     handle in the soc_ifc_status configuration.  It drives the singals passed
//     in through the port connection named bus of type soc_ifc_status_if.
//
//     Input signals from the soc_ifc_status_if are assigned to an internal input
//     signal with a _i suffix.  The _i signal should be used for sampling.
//
//     The input signal connections are as follows:
//       bus.signal -> signal_i 
//
//     This bfm drives signals with a _o suffix.  These signals
//     are driven onto signals within soc_ifc_status_if based on INITIATOR/RESPONDER and/or
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
import soc_ifc_status_pkg_hdl::*;
`include "src/soc_ifc_status_macros.svh"

interface soc_ifc_status_driver_bfm 
  (soc_ifc_status_if bus);
  // The following pragma and additional ones in-lined further below are for running this BFM on Veloce
  // pragma attribute soc_ifc_status_driver_bfm partition_interface_xif

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

  // INITIATOR mode output signals
  tri  ready_for_fuses_i;
  reg  ready_for_fuses_o = 'b0;
  tri  ready_for_fw_push_i;
  reg  ready_for_fw_push_o = 'b0;
  tri  ready_for_runtime_i;
  reg  ready_for_runtime_o = 'b0;
  tri  mailbox_data_avail_i;
  reg  mailbox_data_avail_o = 'b0;
  tri  mailbox_flow_done_i;
  reg  mailbox_flow_done_o = 'b0;
  tri  cptra_error_fatal_i;
  reg  cptra_error_fatal_o = 'bz;
  tri  cptra_error_non_fatal_i;
  reg  cptra_error_non_fatal_o = 'bz;
  tri  trng_req_i;
  reg  trng_req_o = 'bz;
  tri [63:0] generic_output_wires_i;
  reg [63:0] generic_output_wires_o = 'b0;

  // Bi-directional signals
  

  assign clk_i = bus.clk;
  assign dummy_i = bus.dummy;

  // These are signals marked as 'input' by the config file, but the signals will be
  // driven by this BFM if put into RESPONDER mode (flipping all signal directions around)


  // These are signals marked as 'output' by the config file, but the outputs will
  // not be driven by this BFM unless placed in INITIATOR mode.
  assign bus.ready_for_fuses = (initiator_responder == INITIATOR) ? ready_for_fuses_o : 'bz;
  assign ready_for_fuses_i = bus.ready_for_fuses;
  assign bus.ready_for_fw_push = (initiator_responder == INITIATOR) ? ready_for_fw_push_o : 'bz;
  assign ready_for_fw_push_i = bus.ready_for_fw_push;
  assign bus.ready_for_runtime = (initiator_responder == INITIATOR) ? ready_for_runtime_o : 'bz;
  assign ready_for_runtime_i = bus.ready_for_runtime;
  assign bus.mailbox_data_avail = (initiator_responder == INITIATOR) ? mailbox_data_avail_o : 'bz;
  assign mailbox_data_avail_i = bus.mailbox_data_avail;
  assign bus.mailbox_flow_done = (initiator_responder == INITIATOR) ? mailbox_flow_done_o : 'bz;
  assign mailbox_flow_done_i = bus.mailbox_flow_done;
  assign bus.cptra_error_fatal = (initiator_responder == INITIATOR) ? cptra_error_fatal_o : 'bz;
  assign cptra_error_fatal_i = bus.cptra_error_fatal;
  assign bus.cptra_error_non_fatal = (initiator_responder == INITIATOR) ? cptra_error_non_fatal_o : 'bz;
  assign cptra_error_non_fatal_i = bus.cptra_error_non_fatal;
  assign bus.trng_req = (initiator_responder == INITIATOR) ? trng_req_o : 'bz;
  assign trng_req_i = bus.trng_req;
  assign bus.generic_output_wires = (initiator_responder == INITIATOR) ? generic_output_wires_o : 'bz;
  assign generic_output_wires_i = bus.generic_output_wires;

  // Proxy handle to UVM driver
  soc_ifc_status_pkg::soc_ifc_status_driver   proxy;
  // pragma tbx oneway proxy.my_function_name_in_uvm_driver                 

  // ****************************************************************************
  // **************************************************************************** 
  // Macros that define structs located in soc_ifc_status_macros.svh
  // ****************************************************************************
  // Struct for passing configuration data from soc_ifc_status_driver to this BFM
  // ****************************************************************************
  `soc_ifc_status_CONFIGURATION_STRUCT
  // ****************************************************************************
  // Structs for INITIATOR and RESPONDER data flow
  //*******************************************************************
  // Initiator macro used by soc_ifc_status_driver and soc_ifc_status_driver_bfm
  // to communicate initiator driven data to soc_ifc_status_driver_bfm.           
  `soc_ifc_status_INITIATOR_STRUCT
    soc_ifc_status_initiator_s initiator_struct;
  // Responder macro used by soc_ifc_status_driver and soc_ifc_status_driver_bfm
  // to communicate Responder driven data to soc_ifc_status_driver_bfm.
  `soc_ifc_status_RESPONDER_STRUCT
    soc_ifc_status_responder_s responder_struct;

  // ****************************************************************************
// pragma uvmf custom reset_condition_and_response begin
  // Always block used to return signals to reset value upon assertion of reset
  always @( negedge dummy_i )
     begin
       // RESPONDER mode output signals
       // INITIATOR mode output signals
       ready_for_fuses_o <= 'b0;
       ready_for_fw_push_o <= 'b0;
       ready_for_runtime_o <= 'b0;
       mailbox_data_avail_o <= 'b0;
       mailbox_flow_done_o <= 'b0;
       cptra_error_fatal_o <= 1'b0;
       cptra_error_non_fatal_o <= 1'b0;
       trng_req_o <= 1'b0;
       generic_output_wires_o <= 'b0;
       // Bi-directional signals
 
     end    
// pragma uvmf custom reset_condition_and_response end

  // pragma uvmf custom interface_item_additional begin
  function bit any_signal_changed();
      return |(ready_for_fuses_i       ^  ready_for_fuses_o          ) ||
             |(ready_for_fw_push_i     ^  ready_for_fw_push_o        ) ||
             |(ready_for_runtime_i     ^  ready_for_runtime_o        ) ||
             |(mailbox_data_avail_i    ^  mailbox_data_avail_o       ) ||
             |(mailbox_flow_done_i     ^  mailbox_flow_done_o        ) ||
             |(cptra_error_fatal_i     & !cptra_error_fatal_o        ) ||
             |(cptra_error_non_fatal_i & !cptra_error_non_fatal_o    ) ||
             |(trng_req_i              ^  trng_req_o                 ) ||
             |(generic_output_wires_i  ^  generic_output_wires_o     );
  endfunction
  // pragma uvmf custom interface_item_additional end

  //******************************************************************
  // The configure() function is used to pass agent configuration
  // variables to the driver BFM.  It is called by the driver within
  // the agent at the beginning of the simulation.  It may be called 
  // during the simulation if agent configuration variables are updated
  // and the driver BFM needs to be aware of the new configuration 
  // variables.
  //

  function void configure(soc_ifc_status_configuration_s soc_ifc_status_configuration_arg); // pragma tbx xtf  
    initiator_responder = soc_ifc_status_configuration_arg.initiator_responder;
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
       input soc_ifc_status_initiator_s soc_ifc_status_initiator_struct, 
       // This argument is used to send data received from the responder
       // back to the sequence item.  The sequence item is returned to the sequence.
       output soc_ifc_status_responder_s soc_ifc_status_responder_struct 
       );// pragma tbx xtf  
       // 
       // Members within the soc_ifc_status_initiator_struct:
       //   bit ready_for_fuses ;
       //   bit ready_for_fw_push ;
       //   bit ready_for_runtime ;
       //   bit mailbox_data_avail ;
       //   bit mailbox_flow_done ;
       //   bit cptra_error_fatal_intr_pending ;
       //   bit cptra_error_non_fatal_intr_pending ;
       //   bit trng_req_pending ;
       //   bit [63:0] generic_output_val ;
       // Members within the soc_ifc_status_responder_struct:
       //   bit ready_for_fuses ;
       //   bit ready_for_fw_push ;
       //   bit ready_for_runtime ;
       //   bit mailbox_data_avail ;
       //   bit mailbox_flow_done ;
       //   bit cptra_error_fatal_intr_pending ;
       //   bit cptra_error_non_fatal_intr_pending ;
       //   bit trng_req_pending ;
       //   bit [63:0] generic_output_val ;
       initiator_struct = soc_ifc_status_initiator_struct;
       //
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available initiator input and inout signals listed.
       //    Initiator input signals
       //    Initiator inout signals
       //    How to assign a signal from an initiator struct member named xyz.   
       //    All available initiator output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Initiator output signals
       //      ready_for_fuses_o <= soc_ifc_status_initiator_struct.xyz;  //     
       //      ready_for_fw_push_o <= soc_ifc_status_initiator_struct.xyz;  //     
       //      ready_for_runtime_o <= soc_ifc_status_initiator_struct.xyz;  //     
       //      mailbox_data_avail_o <= soc_ifc_status_initiator_struct.xyz;  //     
       //      mailbox_flow_done_o <= soc_ifc_status_initiator_struct.xyz;  //     
       //      cptra_error_fatal_o <= soc_ifc_status_initiator_struct.xyz;  //     
       //      cptra_error_non_fatal_o <= soc_ifc_status_initiator_struct.xyz;  //     
       //      trng_req_o <= soc_ifc_status_initiator_struct.xyz;  //     
       //      generic_output_wires_o <= soc_ifc_status_initiator_struct.xyz;  //    [63:0] 
       //    Initiator inout signals
    // Initiate a transfer using the data received.
    @(posedge clk_i);
    @(posedge clk_i);
    // Wait for the responder to complete the transfer then place the responder data into 
    // soc_ifc_status_responder_struct.
    @(posedge clk_i);
    @(posedge clk_i);
    responder_struct = soc_ifc_status_responder_struct;
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
       output soc_ifc_status_initiator_s soc_ifc_status_initiator_struct, 
       // This argument passes transaction variables used by a responder
       // to complete a protocol transfer.  The values come from a sequence item.       
       input soc_ifc_status_responder_s soc_ifc_status_responder_struct 
       );// pragma tbx xtf   
  // Variables within the soc_ifc_status_initiator_struct:
  //   bit ready_for_fuses ;
  //   bit ready_for_fw_push ;
  //   bit ready_for_runtime ;
  //   bit mailbox_data_avail ;
  //   bit mailbox_flow_done ;
  //   bit cptra_error_fatal_intr_pending ;
  //   bit cptra_error_non_fatal_intr_pending ;
  //   bit trng_req_pending ;
  //   bit [63:0] generic_output_val ;
  // Variables within the soc_ifc_status_responder_struct:
  //   bit ready_for_fuses ;
  //   bit ready_for_fw_push ;
  //   bit ready_for_runtime ;
  //   bit mailbox_data_avail ;
  //   bit mailbox_flow_done ;
  //   bit cptra_error_fatal_intr_pending ;
  //   bit cptra_error_non_fatal_intr_pending ;
  //   bit trng_req_pending ;
  //   bit [63:0] generic_output_val ;
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available responder input and inout signals listed.
       //    Responder input signals
       //      soc_ifc_status_responder_struct.xyz = ready_for_fuses_i;  //     
       //      soc_ifc_status_responder_struct.xyz = ready_for_fw_push_i;  //     
       //      soc_ifc_status_responder_struct.xyz = ready_for_runtime_i;  //     
       //      soc_ifc_status_responder_struct.xyz = mailbox_data_avail_i;  //     
       //      soc_ifc_status_responder_struct.xyz = mailbox_flow_done_i;  //     
       //      soc_ifc_status_responder_struct.xyz = cptra_error_fatal_i;  //     
       //      soc_ifc_status_responder_struct.xyz = cptra_error_non_fatal_i;  //     
       //      soc_ifc_status_responder_struct.xyz = trng_req_i;  //     
       //      soc_ifc_status_responder_struct.xyz = generic_output_wires_i;  //    [63:0] 
       //    Responder inout signals
       //    How to assign a signal, named xyz, from an initiator struct member.   
       //    All available responder output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Responder output signals
       //    Responder inout signals
    
//  @(posedge clk_i);
//  if (!first_transfer) begin
//    // Perform transfer response here.   
//    // Reply using data received in the soc_ifc_status_responder_struct.
//    @(posedge clk_i);
//    // Reply using data received in the transaction handle.
//    @(posedge clk_i);
//  end
    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the soc_ifc_status_initiator_struct.
    do @(posedge clk_i); while (!any_signal_changed());
    ready_for_fuses_o              <= ready_for_fuses_i      ;
    ready_for_fw_push_o            <= ready_for_fw_push_i    ;
    ready_for_runtime_o            <= ready_for_runtime_i    ;
    mailbox_data_avail_o           <= mailbox_data_avail_i   ;
    mailbox_flow_done_o            <= mailbox_flow_done_i    ;
    cptra_error_fatal_o            <= mailbox_flow_done_i    ;
    cptra_error_non_fatal_o        <= cptra_error_non_fatal_i;
    trng_req_o                     <= trng_req_i             ;
    generic_output_wires_o         <= generic_output_wires_i ;
//    @(posedge clk_i);
    first_transfer = 0;
    begin: build_return_struct
  // Variables within the soc_ifc_status_initiator_struct:
         soc_ifc_status_initiator_struct.ready_for_fuses                    = ready_for_fuses_i;
         soc_ifc_status_initiator_struct.ready_for_fw_push                  = ready_for_fw_push_i;
         soc_ifc_status_initiator_struct.ready_for_runtime                  = ready_for_runtime_i;
         soc_ifc_status_initiator_struct.mailbox_data_avail                 = mailbox_data_avail_i;
         soc_ifc_status_initiator_struct.mailbox_flow_done                  = mailbox_flow_done_i;
         soc_ifc_status_responder_struct.cptra_error_fatal_intr_pending     = cptra_error_fatal_i;  //     
         soc_ifc_status_responder_struct.cptra_error_non_fatal_intr_pending = cptra_error_non_fatal_i;  //     
         soc_ifc_status_responder_struct.trng_req_pending                   = trng_req_i;  //     
         soc_ifc_status_initiator_struct.generic_output_val                 = generic_output_wires_i;
    end
  endtask
// pragma uvmf custom respond_and_wait_for_next_transfer end

 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

