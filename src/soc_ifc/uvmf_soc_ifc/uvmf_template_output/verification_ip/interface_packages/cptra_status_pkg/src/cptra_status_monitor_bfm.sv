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
// DESCRIPTION: This interface performs the cptra_status signal monitoring.
//      It is accessed by the uvm cptra_status monitor through a virtual
//      interface handle in the cptra_status configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type cptra_status_if.
//
//     Input signals from the cptra_status_if are assigned to an internal input
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
//                   blocks until an operation on the cptra_status bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import cptra_status_pkg_hdl::*;
`include "src/cptra_status_macros.svh"


interface cptra_status_monitor_bfm
  ( cptra_status_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute cptra_status_monitor_bfm partition_interface_xif

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
`cptra_status_MONITOR_STRUCT
  cptra_status_monitor_s cptra_status_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `cptra_status_CONFIGURATION_STRUCT


  // Config value to determine if this is an initiator or a responder
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri dummy_i;
  tri  cptra_noncore_rst_b_i;
  tri  cptra_uc_rst_b_i;
  tri [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key_reg_i;
  tri [`CLP_OBF_FE_DWORDS-1:0][31:0] obf_field_entropy_i;
  tri [`CLP_OBF_UDS_DWORDS-1:0][31:0] obf_uds_seed_i;
  tri  soc_ifc_error_intr_i;
  tri  soc_ifc_notif_intr_i;
  tri  sha_error_intr_i;
  tri  sha_notif_intr_i;
  tri  timer_intr_i;
  tri [31:0] nmi_vector_i;
  tri  nmi_intr_i;
  tri  iccm_lock_i;
  assign clk_i = bus.clk;
  assign dummy_i = bus.dummy;
  assign cptra_noncore_rst_b_i = bus.cptra_noncore_rst_b;
  assign cptra_uc_rst_b_i = bus.cptra_uc_rst_b;
  assign cptra_obf_key_reg_i = bus.cptra_obf_key_reg;
  assign obf_field_entropy_i = bus.obf_field_entropy;
  assign obf_uds_seed_i = bus.obf_uds_seed;
  assign soc_ifc_error_intr_i = bus.soc_ifc_error_intr;
  assign soc_ifc_notif_intr_i = bus.soc_ifc_notif_intr;
  assign sha_error_intr_i = bus.sha_error_intr;
  assign sha_notif_intr_i = bus.sha_notif_intr;
  assign timer_intr_i = bus.timer_intr;
  assign nmi_vector_i = bus.nmi_vector;
  assign nmi_intr_i = bus.nmi_intr;
  assign iccm_lock_i = bus.iccm_lock;

  // Proxy handle to UVM monitor
  cptra_status_pkg::cptra_status_monitor  proxy;
  // pragma tbx oneway proxy.notify_transaction

  // pragma uvmf custom interface_item_additional begin
  reg  cptra_noncore_rst_b_o = 'b0;
  reg  cptra_uc_rst_b_o = 'b0;
  reg [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key_reg_o = 'b0;
  reg [`CLP_OBF_FE_DWORDS-1:0][31:0] obf_field_entropy_o = 'b0;
  reg [`CLP_OBF_UDS_DWORDS-1:0][31:0] obf_uds_seed_o = 'b0;
  reg  soc_ifc_error_intr_o = 'b0;
  reg  soc_ifc_notif_intr_o = 'b0;
  reg  sha_error_intr_o = 'b0;
  reg  sha_notif_intr_o = 'b0;
  reg  timer_intr_o = 'b0;
  reg [31:0] nmi_vector_o = 'b0;
  reg  nmi_intr_o = 'b0;
  reg  iccm_lock_o = 'b0;
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
                 |(timer_intr_i           & !timer_intr_o               ) ||
                 |(nmi_vector_i           ^  nmi_vector_o               ) ||
                 |(nmi_intr_i             & !nmi_intr_o                 ) ||
                 |(iccm_lock_i            ^  iccm_lock_o                );
  endfunction
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
      do_monitor( cptra_status_monitor_struct );


      proxy.notify_transaction( cptra_status_monitor_struct );

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
    function void configure(cptra_status_configuration_s cptra_status_configuration_arg); // pragma tbx xtf
    initiator_responder = cptra_status_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction


  // ****************************************************************************

  task do_monitor(output cptra_status_monitor_s cptra_status_monitor_struct);
    //
    // Available struct members:
    //     //    cptra_status_monitor_struct.soc_ifc_err_intr_pending
    //     //    cptra_status_monitor_struct.soc_ifc_notif_intr_pending
    //     //    cptra_status_monitor_struct.sha_err_intr_pending
    //     //    cptra_status_monitor_struct.sha_notif_intr_pending
    //     //    cptra_status_monitor_struct.timer_intr_pending
    //     //    cptra_status_monitor_struct.noncore_rst_asserted
    //     //    cptra_status_monitor_struct.uc_rst_asserted
    //     //    cptra_status_monitor_struct.cptra_obf_key_reg
    //     //    cptra_status_monitor_struct.obf_field_entropy
    //     //    cptra_status_monitor_struct.obf_uds_seed
    //     //    cptra_status_monitor_struct.nmi_vector
    //     //    cptra_status_monitor_struct.nmi_intr_pending
    //     //    cptra_status_monitor_struct.iccm_locked
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal === 1'b1) @(posedge clk_i);
    //
    //    How to assign a struct member, named xyz, from a signal.
    //    All available input signals listed.
    //      cptra_status_monitor_struct.xyz = cptra_noncore_rst_b_i;  //     
    //      cptra_status_monitor_struct.xyz = cptra_uc_rst_b_i;  //     
    //      cptra_status_monitor_struct.xyz = cptra_obf_key_reg_i;  //    [`CLP_OBF_KEY_DWORDS-1:0][31:0] 
    //      cptra_status_monitor_struct.xyz = obf_field_entropy_i;  //    [`CLP_OBF_FE_DWORDS-1:0][31:0] 
    //      cptra_status_monitor_struct.xyz = obf_uds_seed_i;  //    [`CLP_OBF_UDS_DWORDS-1:0][31:0] 
    //      cptra_status_monitor_struct.xyz = soc_ifc_error_intr_i;  //     
    //      cptra_status_monitor_struct.xyz = soc_ifc_notif_intr_i;  //     
    //      cptra_status_monitor_struct.xyz = sha_error_intr_i;  //     
    //      cptra_status_monitor_struct.xyz = sha_notif_intr_i;  //     
    //      cptra_status_monitor_struct.xyz = timer_intr_i;  //     
    //      cptra_status_monitor_struct.xyz = nmi_vector_i;  //    [31:0] 
    //      cptra_status_monitor_struct.xyz = nmi_intr_i;  //     
    //      cptra_status_monitor_struct.xyz = iccm_lock_i;  //     
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code
    // below are examples of how to capture signal values and assign them to
    // structure members.  All available input signals are listed.  The 'while'
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe
    // the next transfer. One clock cycle is consumed between calls to do_monitor.

    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the cptra_status_initiator_struct.
    while (!any_signal_changed()) begin
        // These only trigger a transaction on rising edge. This assignment uses
        // the falling edge to reset the detection logic.
        soc_ifc_error_intr_o           <= soc_ifc_error_intr_i  ;
        soc_ifc_notif_intr_o           <= soc_ifc_notif_intr_i  ;
        sha_error_intr_o               <= sha_error_intr_i      ;
        sha_notif_intr_o               <= sha_notif_intr_i      ;
        timer_intr_o                   <= timer_intr_i          ;
        nmi_intr_o                     <= nmi_intr_i            ;
        @(posedge clk_i);
    end
    cptra_noncore_rst_b_o          <= cptra_noncore_rst_b_i ;
    cptra_uc_rst_b_o               <= cptra_uc_rst_b_i      ;
    cptra_obf_key_reg_o            <= cptra_obf_key_reg_i   ;
    obf_field_entropy_o            <= obf_field_entropy_i   ;
    obf_uds_seed_o                 <= obf_uds_seed_i        ;
    soc_ifc_error_intr_o           <= soc_ifc_error_intr_i  ;
    soc_ifc_notif_intr_o           <= soc_ifc_notif_intr_i  ;
    sha_error_intr_o               <= sha_error_intr_i      ;
    sha_notif_intr_o               <= sha_notif_intr_i      ;
    timer_intr_o                   <= timer_intr_i          ;
    nmi_vector_o                   <= nmi_vector_i          ;
    nmi_intr_o                     <= nmi_intr_i            ;
    iccm_lock_o                    <= iccm_lock_i           ;
//    @(posedge clk_i);
    begin: build_return_struct
  // Variables within the cptra_status_initiator_struct:
         cptra_status_monitor_struct.noncore_rst_asserted       = !cptra_noncore_rst_b_i;
         cptra_status_monitor_struct.uc_rst_asserted            = !cptra_uc_rst_b_i;
         cptra_status_monitor_struct.soc_ifc_err_intr_pending   =  soc_ifc_error_intr_i;
         cptra_status_monitor_struct.soc_ifc_notif_intr_pending =  soc_ifc_notif_intr_i;
         cptra_status_monitor_struct.sha_err_intr_pending       =  sha_error_intr_i;
         cptra_status_monitor_struct.sha_notif_intr_pending     =  sha_notif_intr_i;
         cptra_status_monitor_struct.timer_intr_pending         =  timer_intr_i;
         cptra_status_monitor_struct.cptra_obf_key_reg          =  cptra_obf_key_reg_i;
         cptra_status_monitor_struct.obf_field_entropy          =  obf_field_entropy_i;
         cptra_status_monitor_struct.obf_uds_seed               =  obf_uds_seed_i;
         cptra_status_monitor_struct.nmi_vector                 =  nmi_vector_i;
         cptra_status_monitor_struct.nmi_intr_pending           =  nmi_intr_i;
         cptra_status_monitor_struct.iccm_locked                =  iccm_lock_i;
    end
    // pragma uvmf custom do_monitor end
  endtask


endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

