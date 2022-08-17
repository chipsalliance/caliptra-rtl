//----------------------------------------------------------------------
// Created with uvmf_gen version 2021.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: 
//    This interface performs the HMAC_out signal driving.  It is
//     accessed by the uvm HMAC_out driver through a virtual interface
//     handle in the HMAC_out configuration.  It drives the singals passed
//     in through the port connection named bus of type HMAC_out_if.
//
//     Input signals from the HMAC_out_if are assigned to an internal input
//     signal with a _i suffix.  The _i signal should be used for sampling.
//
//     The input signal connections are as follows:
//       bus.signal -> signal_i 
//
//     This bfm drives signals with a _o suffix.  These signals
//     are driven onto signals within HMAC_out_if based on INITIATOR/RESPONDER and/or
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
import HMAC_out_pkg_hdl::*;
`include "src/HMAC_out_macros.svh"

interface HMAC_out_driver_bfm #(
  int AHB_DATA_WIDTH = 32,
  int AHB_ADDR_WIDTH = 32,
  int OUTPUT_TEXT_WIDTH = 1280,
  bit BYPASS_HSEL = 0
  )
  (HMAC_out_if bus);
  // The following pragma and additional ones in-lined further below are for running this BFM on Veloce
  // pragma attribute HMAC_out_driver_bfm partition_interface_xif

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
      $psprintf("The BFM at '%m' has the following parameters: AHB_DATA_WIDTH=%x AHB_ADDR_WIDTH=%x OUTPUT_TEXT_WIDTH=%x BYPASS_HSEL=%x ", AHB_DATA_WIDTH,AHB_ADDR_WIDTH,OUTPUT_TEXT_WIDTH,BYPASS_HSEL),
      UVM_DEBUG)
end
`endif

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri rst_i;

  // Signal list (all signals are capable of being inputs and outputs for the sake
  // of supporting both INITIATOR and RESPONDER mode operation. Expectation is that 
  // directionality in the config file was from the point-of-view of the INITIATOR

  // INITIATOR mode input signals
  tri  hresp_i;
  reg  hresp_o = 'bz;
  tri  hreadyout_i;
  reg  hreadyout_o = 'bz;
  tri [AHB_DATA_WIDTH-1:0] hrdata_i;
  reg [AHB_DATA_WIDTH-1:0] hrdata_o = 'bz;
  tri  transaction_flag_in_monitor_i;
  reg  transaction_flag_in_monitor_o = 'bz;

  // INITIATOR mode output signals

  // Bi-directional signals
  

  assign clk_i = bus.clk;
  assign rst_i = bus.rst;

  // These are signals marked as 'input' by the config file, but the signals will be
  // driven by this BFM if put into RESPONDER mode (flipping all signal directions around)
  assign hresp_i = bus.hresp;
  assign bus.hresp = (initiator_responder == RESPONDER) ? hresp_o : 'bz;
  assign hreadyout_i = bus.hreadyout;
  assign bus.hreadyout = (initiator_responder == RESPONDER) ? hreadyout_o : 'bz;
  assign hrdata_i = bus.hrdata;
  assign bus.hrdata = (initiator_responder == RESPONDER) ? hrdata_o : 'bz;
  assign transaction_flag_in_monitor_i = bus.transaction_flag_in_monitor;
  assign bus.transaction_flag_in_monitor = (initiator_responder == RESPONDER) ? transaction_flag_in_monitor_o : 'bz;


  // These are signals marked as 'output' by the config file, but the outputs will
  // not be driven by this BFM unless placed in INITIATOR mode.

  // Proxy handle to UVM driver
  HMAC_out_pkg::HMAC_out_driver #(
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
    .BYPASS_HSEL(BYPASS_HSEL)
    )  proxy;
  // pragma tbx oneway proxy.my_function_name_in_uvm_driver                 

  // ****************************************************************************
  // **************************************************************************** 
  // Macros that define structs located in HMAC_out_macros.svh
  // ****************************************************************************
  // Struct for passing configuration data from HMAC_out_driver to this BFM
  // ****************************************************************************
  `HMAC_out_CONFIGURATION_STRUCT
  // ****************************************************************************
  // Structs for INITIATOR and RESPONDER data flow
  //*******************************************************************
  // Initiator macro used by HMAC_out_driver and HMAC_out_driver_bfm
  // to communicate initiator driven data to HMAC_out_driver_bfm.           
  `HMAC_out_INITIATOR_STRUCT
    HMAC_out_initiator_s initiator_struct;
  // Responder macro used by HMAC_out_driver and HMAC_out_driver_bfm
  // to communicate Responder driven data to HMAC_out_driver_bfm.
  `HMAC_out_RESPONDER_STRUCT
    HMAC_out_responder_s responder_struct;

  // ****************************************************************************
// pragma uvmf custom reset_condition_and_response begin
  // Always block used to return signals to reset value upon assertion of reset
  always @( negedge rst_i )
     begin
       // RESPONDER mode output signals
       hresp_o <= 'bz;
       hreadyout_o <= 'bz;
       hrdata_o <= 'bz;
       transaction_flag_in_monitor_o <= 'bz;
       // INITIATOR mode output signals
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

  function void configure(HMAC_out_configuration_s HMAC_out_configuration_arg); // pragma tbx xtf  
    initiator_responder = HMAC_out_configuration_arg.initiator_responder;
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
       input HMAC_out_initiator_s HMAC_out_initiator_struct, 
       // This argument is used to send data received from the responder
       // back to the sequence item.  The sequence item is returned to the sequence.
       output HMAC_out_responder_s HMAC_out_responder_struct 
       );// pragma tbx xtf  
       // 
       // Members within the HMAC_out_initiator_struct:
       //   bit [OUTPUT_TEXT_WIDTH-1:0] result ;
       // Members within the HMAC_out_responder_struct:
       //   bit [OUTPUT_TEXT_WIDTH-1:0] result ;
       initiator_struct = HMAC_out_initiator_struct;
       //
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available input signals listed.
       //      HMAC_out_responder_struct.xyz = hresp_i;  //     
       //      HMAC_out_responder_struct.xyz = hreadyout_i;  //     
       //      HMAC_out_responder_struct.xyz = hrdata_i;  //    [AHB_DATA_WIDTH-1:0] 
       //      HMAC_out_responder_struct.xyz = transaction_flag_in_monitor_i;  //     
       //    How to assign a signal, named xyz, from an initiator struct member.   
       //    All available input signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //      hresp_o <= HMAC_out_initiator_struct.xyz;  //     
       //      hreadyout_o <= HMAC_out_initiator_struct.xyz;  //     
       //      hrdata_o <= HMAC_out_initiator_struct.xyz;  //    [AHB_DATA_WIDTH-1:0] 
       //      transaction_flag_in_monitor_o <= HMAC_out_initiator_struct.xyz;  //     
    // Initiate a transfer using the data received.
    @(posedge clk_i);
    @(posedge clk_i);
    // Wait for the responder to complete the transfer then place the responder data into 
    // HMAC_out_responder_struct.
    @(posedge clk_i);
    @(posedge clk_i);
    responder_struct = HMAC_out_responder_struct;
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
       output HMAC_out_initiator_s HMAC_out_initiator_struct, 
       // This argument passes transaction variables used by a responder
       // to complete a protocol transfer.  The values come from a sequence item.       
       input HMAC_out_responder_s HMAC_out_responder_struct 
       );// pragma tbx xtf   
  // Variables within the HMAC_out_initiator_struct:
  //   bit [OUTPUT_TEXT_WIDTH-1:0] result ;
  // Variables within the HMAC_out_responder_struct:
  //   bit [OUTPUT_TEXT_WIDTH-1:0] result ;
        
  @(posedge clk_i);
  if (!first_transfer) begin
    // Perform transfer response here.   
    // Reply using data recieved in the HMAC_out_responder_struct.
    @(posedge clk_i);
    // Reply using data recieved in the transaction handle.
    @(posedge clk_i);
  end
    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the HMAC_out_initiator_struct.
    @(posedge clk_i);
    @(posedge clk_i);
    first_transfer = 0;
  endtask
// pragma uvmf custom respond_and_wait_for_next_transfer end

 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

