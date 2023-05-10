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
//    This interface performs the cptra_status signal driving.  It is
//     accessed by the uvm cptra_status driver through a virtual interface
//     handle in the cptra_status configuration.  It drives the singals passed
//     in through the port connection named bus of type cptra_status_if.
//
//     Input signals from the cptra_status_if are assigned to an internal input
//     signal with a _i suffix.  The _i signal should be used for sampling.
//
//     The input signal connections are as follows:
//       bus.signal -> signal_i 
//
//     This bfm drives signals with a _o suffix.  These signals
//     are driven onto signals within cptra_status_if based on INITIATOR/RESPONDER and/or
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
import cptra_status_pkg_hdl::*;
`include "src/cptra_status_macros.svh"

interface cptra_status_driver_bfm 
  (cptra_status_if bus);
  // The following pragma and additional ones in-lined further below are for running this BFM on Veloce
  // pragma attribute cptra_status_driver_bfm partition_interface_xif

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
  tri  cptra_noncore_rst_b_i;
  reg  cptra_noncore_rst_b_o = 'b0;
  tri  cptra_uc_rst_b_i;
  reg  cptra_uc_rst_b_o = 'b0;
  tri [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key_reg_i;
  reg [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key_reg_o = 'bz;
  tri [`CLP_OBF_FE_DWORDS-1:0][31:0] obf_field_entropy_i;
  reg [`CLP_OBF_FE_DWORDS-1:0][31:0] obf_field_entropy_o = 'bz;
  tri [`CLP_OBF_UDS_DWORDS-1:0][31:0] obf_uds_seed_i;
  reg [`CLP_OBF_UDS_DWORDS-1:0][31:0] obf_uds_seed_o = 'bz;
  tri  soc_ifc_error_intr_i;
  reg  soc_ifc_error_intr_o = 'bz;
  tri  soc_ifc_notif_intr_i;
  reg  soc_ifc_notif_intr_o = 'bz;
  tri  sha_error_intr_i;
  reg  sha_error_intr_o = 'bz;
  tri  sha_notif_intr_i;
  reg  sha_notif_intr_o = 'bz;
  tri [31:0] nmi_vector_i;
  reg [31:0] nmi_vector_o = 'bz;
  tri  iccm_lock_i;
  reg  iccm_lock_o = 'bz;

  // Bi-directional signals
  

  assign clk_i = bus.clk;
  assign dummy_i = bus.dummy;

  // These are signals marked as 'input' by the config file, but the signals will be
  // driven by this BFM if put into RESPONDER mode (flipping all signal directions around)


  // These are signals marked as 'output' by the config file, but the outputs will
  // not be driven by this BFM unless placed in INITIATOR mode.
  assign bus.cptra_noncore_rst_b = (initiator_responder == INITIATOR) ? cptra_noncore_rst_b_o : 'bz;
  assign cptra_noncore_rst_b_i = bus.cptra_noncore_rst_b;
  assign bus.cptra_uc_rst_b = (initiator_responder == INITIATOR) ? cptra_uc_rst_b_o : 'bz;
  assign cptra_uc_rst_b_i = bus.cptra_uc_rst_b;
  assign bus.cptra_obf_key_reg = (initiator_responder == INITIATOR) ? cptra_obf_key_reg_o : 'bz;
  assign cptra_obf_key_reg_i = bus.cptra_obf_key_reg;
  assign bus.obf_field_entropy = (initiator_responder == INITIATOR) ? obf_field_entropy_o : 'bz;
  assign obf_field_entropy_i = bus.obf_field_entropy;
  assign bus.obf_uds_seed = (initiator_responder == INITIATOR) ? obf_uds_seed_o : 'bz;
  assign obf_uds_seed_i = bus.obf_uds_seed;
  assign bus.soc_ifc_error_intr = (initiator_responder == INITIATOR) ? soc_ifc_error_intr_o : 'bz;
  assign soc_ifc_error_intr_i = bus.soc_ifc_error_intr;
  assign bus.soc_ifc_notif_intr = (initiator_responder == INITIATOR) ? soc_ifc_notif_intr_o : 'bz;
  assign soc_ifc_notif_intr_i = bus.soc_ifc_notif_intr;
  assign bus.sha_error_intr = (initiator_responder == INITIATOR) ? sha_error_intr_o : 'bz;
  assign sha_error_intr_i = bus.sha_error_intr;
  assign bus.sha_notif_intr = (initiator_responder == INITIATOR) ? sha_notif_intr_o : 'bz;
  assign sha_notif_intr_i = bus.sha_notif_intr;
  assign bus.nmi_vector = (initiator_responder == INITIATOR) ? nmi_vector_o : 'bz;
  assign nmi_vector_i = bus.nmi_vector;
  assign bus.iccm_lock = (initiator_responder == INITIATOR) ? iccm_lock_o : 'bz;
  assign iccm_lock_i = bus.iccm_lock;

  // Proxy handle to UVM driver
  cptra_status_pkg::cptra_status_driver   proxy;
  // pragma tbx oneway proxy.my_function_name_in_uvm_driver                 

  // ****************************************************************************
  // **************************************************************************** 
  // Macros that define structs located in cptra_status_macros.svh
  // ****************************************************************************
  // Struct for passing configuration data from cptra_status_driver to this BFM
  // ****************************************************************************
  `cptra_status_CONFIGURATION_STRUCT
  // ****************************************************************************
  // Structs for INITIATOR and RESPONDER data flow
  //*******************************************************************
  // Initiator macro used by cptra_status_driver and cptra_status_driver_bfm
  // to communicate initiator driven data to cptra_status_driver_bfm.           
  `cptra_status_INITIATOR_STRUCT
    cptra_status_initiator_s initiator_struct;
  // Responder macro used by cptra_status_driver and cptra_status_driver_bfm
  // to communicate Responder driven data to cptra_status_driver_bfm.
  `cptra_status_RESPONDER_STRUCT
    cptra_status_responder_s responder_struct;

  // ****************************************************************************
// pragma uvmf custom reset_condition_and_response begin
  // Always block used to return signals to reset value upon assertion of reset
  always @( negedge dummy_i )
     begin
       // RESPONDER mode output signals
       // INITIATOR mode output signals
       cptra_noncore_rst_b_o <= 'b0;
       cptra_uc_rst_b_o <= 'b0;
       cptra_obf_key_reg_o <= 'bz;
       obf_field_entropy_o <= 'bz;
       obf_uds_seed_o <= 'bz;
       soc_ifc_error_intr_o <= 'bz;
       soc_ifc_notif_intr_o <= 'bz;
       sha_error_intr_o <= 'bz;
       sha_notif_intr_o <= 'bz;
       nmi_vector_o <= 'bz;
       iccm_lock_o <= 'bz;
       // Bi-directional signals
 
     end    
// pragma uvmf custom reset_condition_and_response end

  // pragma uvmf custom interface_item_additional begin
  function bit any_signal_changed();
      if (!cptra_noncore_rst_b_o)
          return cptra_noncore_rst_b_i ||
                 |(cptra_obf_key_reg_i    ^  cptra_obf_key_reg_o        ) || /* NOTE:             */
                 |(obf_field_entropy_i    ^  obf_field_entropy_o        ) || /*   These are reset */
                 |(obf_uds_seed_i         ^  obf_uds_seed_o             ) ;  /*   by pwrgood      */
      else
          return |(cptra_noncore_rst_b_i  ^  cptra_noncore_rst_b_o      ) ||
                 |(cptra_uc_rst_b_i       ^  cptra_uc_rst_b_o           ) ||
                 |(cptra_obf_key_reg_i    ^  cptra_obf_key_reg_o        ) ||
                 |(obf_field_entropy_i    ^  obf_field_entropy_o        ) ||
                 |(obf_uds_seed_i         ^  obf_uds_seed_o             ) ||
                 |(soc_ifc_error_intr_i   & !soc_ifc_error_intr_o       ) ||
                 |(soc_ifc_notif_intr_i   & !soc_ifc_notif_intr_o       ) ||
                 |(sha_error_intr_i       & !sha_error_intr_o           ) ||
                 |(sha_notif_intr_i       & !sha_notif_intr_o           ) ||
                 |(nmi_vector_i           ^  nmi_vector_o               ) ||
                 |(iccm_lock_i            ^  iccm_lock_o                );
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

  function void configure(cptra_status_configuration_s cptra_status_configuration_arg); // pragma tbx xtf  
    initiator_responder = cptra_status_configuration_arg.initiator_responder;
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
       input cptra_status_initiator_s cptra_status_initiator_struct, 
       // This argument is used to send data received from the responder
       // back to the sequence item.  The sequence item is returned to the sequence.
       output cptra_status_responder_s cptra_status_responder_struct 
       );// pragma tbx xtf  
       // 
       // Members within the cptra_status_initiator_struct:
       //   bit soc_ifc_err_intr_pending ;
       //   bit soc_ifc_notif_intr_pending ;
       //   bit sha_err_intr_pending ;
       //   bit sha_notif_intr_pending ;
       //   bit noncore_rst_asserted ;
       //   bit uc_rst_asserted ;
       //   bit [`CLP_OBF_KEY_DWORDS-1:0] [31:0] cptra_obf_key_reg ;
       //   bit [`CLP_OBF_FE_DWORDS-1:0] [31:0] obf_field_entropy ;
       //   bit [`CLP_OBF_UDS_DWORDS-1:0] [31:0] obf_uds_seed ;
       //   bit [31:0] nmi_vector ;
       //   bit iccm_locked ;
       // Members within the cptra_status_responder_struct:
       //   bit soc_ifc_err_intr_pending ;
       //   bit soc_ifc_notif_intr_pending ;
       //   bit sha_err_intr_pending ;
       //   bit sha_notif_intr_pending ;
       //   bit noncore_rst_asserted ;
       //   bit uc_rst_asserted ;
       //   bit [`CLP_OBF_KEY_DWORDS-1:0] [31:0] cptra_obf_key_reg ;
       //   bit [`CLP_OBF_FE_DWORDS-1:0] [31:0] obf_field_entropy ;
       //   bit [`CLP_OBF_UDS_DWORDS-1:0] [31:0] obf_uds_seed ;
       //   bit [31:0] nmi_vector ;
       //   bit iccm_locked ;
       initiator_struct = cptra_status_initiator_struct;
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
       //      cptra_noncore_rst_b_o <= cptra_status_initiator_struct.xyz;  //     
       //      cptra_uc_rst_b_o <= cptra_status_initiator_struct.xyz;  //
       //      cptra_obf_key_reg_o <= cptra_status_initiator_struct.xyz;  //    [`CLP_OBF_KEY_DWORDS-1:0][31:0] 
       //      obf_field_entropy_o <= cptra_status_initiator_struct.xyz;  //    [`CLP_OBF_FE_DWORDS-1:0][31:0] 
       //      obf_uds_seed_o <= cptra_status_initiator_struct.xyz;  //    [`CLP_OBF_UDS_DWORDS-1:0][31:0] 
       //      soc_ifc_error_intr_o <= cptra_status_initiator_struct.xyz;  //     
       //      soc_ifc_notif_intr_o <= cptra_status_initiator_struct.xyz;  //    
       //      sha_error_intr_o <= cptra_status_initiator_struct.xyz;  //     
       //      sha_notif_intr_o <= cptra_status_initiator_struct.xyz;  //     
       //      nmi_vector_o <= cptra_status_initiator_struct.xyz;  //    [31:0]
       //      iccm_lock_o <= cptra_status_initiator_struct.xyz;  //     
       //    Initiator inout signals
    // Initiate a transfer using the data received.
    @(posedge clk_i);
    @(posedge clk_i);
    // Wait for the responder to complete the transfer then place the responder data into 
    // cptra_status_responder_struct.
    @(posedge clk_i);
    @(posedge clk_i);
    responder_struct = cptra_status_responder_struct;
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
       output cptra_status_initiator_s cptra_status_initiator_struct, 
       // This argument passes transaction variables used by a responder
       // to complete a protocol transfer.  The values come from a sequence item.       
       input cptra_status_responder_s cptra_status_responder_struct 
       );// pragma tbx xtf   
  // Variables within the cptra_status_initiator_struct:
  //   bit soc_ifc_err_intr_pending ;
  //   bit soc_ifc_notif_intr_pending ;
  //   bit sha_err_intr_pending ;
  //   bit sha_notif_intr_pending ;
  //   bit noncore_rst_asserted ;
  //   bit uc_rst_asserted ;
  //   bit [`CLP_OBF_KEY_DWORDS-1:0] [31:0] cptra_obf_key_reg ;
  //   bit [`CLP_OBF_FE_DWORDS-1:0] [31:0] obf_field_entropy ;
  //   bit [`CLP_OBF_UDS_DWORDS-1:0] [31:0] obf_uds_seed ;
  //   bit [31:0] nmi_vector ;
  //   bit iccm_locked ;
  // Variables within the cptra_status_responder_struct:
  //   bit soc_ifc_err_intr_pending ;
  //   bit soc_ifc_notif_intr_pending ;
  //   bit sha_err_intr_pending ;
  //   bit sha_notif_intr_pending ;
  //   bit noncore_rst_asserted ;
  //   bit uc_rst_asserted ;
  //   bit [`CLP_OBF_KEY_DWORDS-1:0] [31:0] cptra_obf_key_reg ;
  //   bit [`CLP_OBF_FE_DWORDS-1:0] [31:0] obf_field_entropy ;
  //   bit [`CLP_OBF_UDS_DWORDS-1:0] [31:0] obf_uds_seed ;
  //   bit [31:0] nmi_vector ;
  //   bit iccm_locked ;
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available responder input and inout signals listed.
       //    Responder input signals
       //      cptra_status_responder_struct.xyz = cptra_noncore_rst_b_i;  //     
       //      cptra_status_responder_struct.xyz = cptra_uc_rst_b_i;  //     
       //      cptra_status_responder_struct.xyz = cptra_obf_key_reg_i;  //    [`CLP_OBF_KEY_DWORDS-1:0][31:0] 
       //      cptra_status_responder_struct.xyz = obf_field_entropy_i;  //    [`CLP_OBF_FE_DWORDS-1:0][31:0] 
       //      cptra_status_responder_struct.xyz = obf_uds_seed_i;  //    [`CLP_OBF_UDS_DWORDS-1:0][31:0] 
       //      cptra_status_responder_struct.xyz = soc_ifc_error_intr_i;  //     
       //      cptra_status_responder_struct.xyz = soc_ifc_notif_intr_i;  //   
       //      cptra_status_responder_struct.xyz = sha_error_intr_i;  //     
       //      cptra_status_responder_struct.xyz = sha_notif_intr_i;  //     
       //      cptra_status_responder_struct.xyz = nmi_vector_i;  //    [31:0] 
       //      cptra_status_responder_struct.xyz = iccm_lock_i;  //     
       //    Responder inout signals
       //    How to assign a signal, named xyz, from an initiator struct member.   
       //    All available responder output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Responder output signals
       //    Responder inout signals
    
//  @(posedge clk_i);
//  if (!first_transfer) begin
//    // Perform transfer response here.   
//    // Reply using data recieved in the cptra_status_responder_struct.
//    @(posedge clk_i);
//    // Reply using data recieved in the transaction handle.
//    @(posedge clk_i);
//  end
    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the cptra_status_initiator_struct.
    do begin
        soc_ifc_error_intr_o           <= soc_ifc_error_intr_i;
        soc_ifc_notif_intr_o           <= soc_ifc_notif_intr_i;
        sha_error_intr_o               <= sha_error_intr_i    ;
        sha_notif_intr_o               <= sha_notif_intr_i    ;
        @(posedge clk_i);
    end
    while (!any_signal_changed());
    cptra_noncore_rst_b_o          <= cptra_noncore_rst_b_i ;
    cptra_uc_rst_b_o               <= cptra_uc_rst_b_i      ;
    cptra_obf_key_reg_o            <= cptra_obf_key_reg_i   ;
    obf_field_entropy_o            <= obf_field_entropy_i   ;
    obf_uds_seed_o                 <= obf_uds_seed_i        ;
    soc_ifc_error_intr_o           <= soc_ifc_error_intr_i  ;
    soc_ifc_notif_intr_o           <= soc_ifc_notif_intr_i  ;
    sha_error_intr_o               <= sha_error_intr_i      ;
    sha_notif_intr_o               <= sha_notif_intr_i      ;
    nmi_vector_o                   <= nmi_vector_i          ;
    iccm_lock_o                    <= iccm_lock_i           ;
//    @(posedge clk_i);
    first_transfer = 0;
    begin: build_return_struct
  // Variables within the cptra_status_initiator_struct:
         cptra_status_initiator_struct.soc_ifc_err_intr_pending   = soc_ifc_error_intr_i;
         cptra_status_initiator_struct.soc_ifc_notif_intr_pending = soc_ifc_notif_intr_i;
         cptra_status_initiator_struct.sha_err_intr_pending       = sha_error_intr_i;
         cptra_status_initiator_struct.sha_notif_intr_pending     = sha_notif_intr_i;
         cptra_status_initiator_struct.noncore_rst_asserted       = !cptra_noncore_rst_b_i;
         cptra_status_initiator_struct.uc_rst_asserted            = !cptra_uc_rst_b_i;
         cptra_status_initiator_struct.cptra_obf_key_reg          = cptra_obf_key_reg_i;
         cptra_status_initiator_struct.obf_field_entropy          = obf_field_entropy_i;
         cptra_status_initiator_struct.obf_uds_seed               = obf_uds_seed_i;
         cptra_status_initiator_struct.nmi_vector                 = nmi_vector_i;
         cptra_status_initiator_struct.iccm_locked                = iccm_lock_i;
    end
  endtask
// pragma uvmf custom respond_and_wait_for_next_transfer end

 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

