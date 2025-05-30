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
// DESCRIPTION: This interface performs the ss_mode_ctrl signal monitoring.
//      It is accessed by the uvm ss_mode_ctrl monitor through a virtual
//      interface handle in the ss_mode_ctrl configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type ss_mode_ctrl_if.
//
//     Input signals from the ss_mode_ctrl_if are assigned to an internal input
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
//                   blocks until an operation on the ss_mode_ctrl bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import ss_mode_ctrl_pkg_hdl::*;
`include "src/ss_mode_ctrl_macros.svh"


interface ss_mode_ctrl_monitor_bfm
  ( ss_mode_ctrl_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute ss_mode_ctrl_monitor_bfm partition_interface_xif

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
`ss_mode_ctrl_MONITOR_STRUCT
  ss_mode_ctrl_monitor_s ss_mode_ctrl_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `ss_mode_ctrl_CONFIGURATION_STRUCT


  // Config value to determine if this is an initiator or a responder
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri dummy_i;
  tri [63:0] strap_ss_caliptra_base_addr_i;
  tri [63:0] strap_ss_mci_base_addr_i;
  tri [63:0] strap_ss_recovery_ifc_base_addr_i;
  tri [63:0] strap_ss_otp_fc_base_addr_i;
  tri [63:0] strap_ss_uds_seed_base_addr_i;
  tri [31:0] strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i;
  tri [31:0] strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_i;
  tri [31:0] strap_ss_strap_generic_0_i;
  tri [31:0] strap_ss_strap_generic_1_i;
  tri [31:0] strap_ss_strap_generic_2_i;
  tri [31:0] strap_ss_strap_generic_3_i;
  tri [31:0] strap_ss_caliptra_dma_axi_user_i;
  tri        ss_debug_intent_i;
  assign clk_i = bus.clk;
  assign dummy_i = bus.dummy;
  assign strap_ss_caliptra_base_addr_i = bus.strap_ss_caliptra_base_addr;
  assign strap_ss_mci_base_addr_i = bus.strap_ss_mci_base_addr;
  assign strap_ss_recovery_ifc_base_addr_i = bus.strap_ss_recovery_ifc_base_addr;
  assign strap_ss_otp_fc_base_addr_i = bus.strap_ss_otp_fc_base_addr;
  assign strap_ss_uds_seed_base_addr_i = bus.strap_ss_uds_seed_base_addr;
  assign strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i = bus.strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset;
  assign strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_i = bus.strap_ss_num_of_prod_debug_unlock_auth_pk_hashes;
  assign strap_ss_strap_generic_0_i = bus.strap_ss_strap_generic_0;
  assign strap_ss_strap_generic_1_i = bus.strap_ss_strap_generic_1;
  assign strap_ss_strap_generic_2_i = bus.strap_ss_strap_generic_2;
  assign strap_ss_strap_generic_3_i = bus.strap_ss_strap_generic_3;
  assign strap_ss_caliptra_dma_axi_user_i = bus.strap_ss_caliptra_dma_axi_user;
  assign ss_debug_intent_i = bus.ss_debug_intent;

  // Proxy handle to UVM monitor
  ss_mode_ctrl_pkg::ss_mode_ctrl_monitor  proxy;
  // pragma tbx oneway proxy.notify_transaction

  // pragma uvmf custom interface_item_additional begin
  logic [63:0] strap_ss_caliptra_base_addr_r                             = 64'h0;
  logic [63:0] strap_ss_mci_base_addr_r                                  = 64'h0;
  logic [63:0] strap_ss_recovery_ifc_base_addr_r                         = 64'h0;
  logic [63:0] strap_ss_otp_fc_base_addr_r                               = 64'h0;
  logic [63:0] strap_ss_uds_seed_base_addr_r                             = 64'h0;
  logic [31:0] strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_r = 32'h0;
  logic [31:0] strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_r        = 32'h0;
  logic [31:0] strap_ss_strap_generic_0_r                                = 32'h0;
  logic [31:0] strap_ss_strap_generic_1_r                                = 32'h0;
  logic [31:0] strap_ss_strap_generic_2_r                                = 32'h0;
  logic [31:0] strap_ss_strap_generic_3_r                                = 32'h0;
  logic        ss_debug_intent_r                                         = 1'b0;
  logic [31:0] strap_ss_caliptra_dma_axi_user_r                          = 32'h0;
  function bit any_signal_changed();
      return |(strap_ss_caliptra_base_addr_i                             ^ strap_ss_caliptra_base_addr_r                            ) ||
             |(strap_ss_mci_base_addr_i                                  ^ strap_ss_mci_base_addr_r                                 ) ||
             |(strap_ss_recovery_ifc_base_addr_i                         ^ strap_ss_recovery_ifc_base_addr_r                        ) ||
             |(strap_ss_otp_fc_base_addr_i                               ^ strap_ss_otp_fc_base_addr_r                              ) ||
             |(strap_ss_uds_seed_base_addr_i                             ^ strap_ss_uds_seed_base_addr_r                            ) ||
             |(strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i ^ strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_r) ||
             |(strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_i        ^ strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_r       ) ||
             |(strap_ss_strap_generic_0_i                                ^ strap_ss_strap_generic_0_r                               ) ||
             |(strap_ss_strap_generic_1_i                                ^ strap_ss_strap_generic_1_r                               ) ||
             |(strap_ss_strap_generic_2_i                                ^ strap_ss_strap_generic_2_r                               ) ||
             |(strap_ss_strap_generic_3_i                                ^ strap_ss_strap_generic_3_r                               ) ||
             |(strap_ss_caliptra_dma_axi_user_i                          ^ strap_ss_caliptra_dma_axi_user_r                         ) ||
             |(ss_debug_intent_i                                         ^ ss_debug_intent_r                                        );
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

  // pragma uvmf custom wait_for_num_clocks begin
  //****************************************************************************
  // Inject pragmas's here to throw a warning on regeneration.
  // Task must have automatic lifetime so that it can be concurrently invoked
  // by multiple entities with a different wait value.
  task automatic wait_for_num_clocks(input int unsigned count); // pragma tbx xtf
    if (count == 0) `uvm_fatal("CFG", "wait_for_num_clocks called with count of 0 - this will lead to a hang");
    @(posedge clk_i);
    repeat (count-1) @(posedge clk_i);
  endtask
  // pragma uvmf custom wait_for_num_clocks end

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
      do_monitor( ss_mode_ctrl_monitor_struct );


      proxy.notify_transaction( ss_mode_ctrl_monitor_struct );

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
    function void configure(ss_mode_ctrl_configuration_s ss_mode_ctrl_configuration_arg); // pragma tbx xtf
    initiator_responder = ss_mode_ctrl_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction


  // ****************************************************************************

  task do_monitor(output ss_mode_ctrl_monitor_s ss_mode_ctrl_monitor_struct);
    //
    // Available struct members:
    //     //    ss_mode_ctrl_monitor_struct.strap_ss_caliptra_base_addr
    //     //    ss_mode_ctrl_monitor_struct.strap_ss_mci_base_addr
    //     //    ss_mode_ctrl_monitor_struct.strap_ss_recovery_ifc_base_addr
    //     //    ss_mode_ctrl_monitor_struct.strap_ss_otp_fc_base_addr
    //     //    ss_mode_ctrl_monitor_struct.strap_ss_uds_seed_base_addr
    //     //    ss_mode_ctrl_monitor_struct.strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset
    //     //    ss_mode_ctrl_monitor_struct.strap_ss_num_of_prod_debug_unlock_auth_pk_hashes
    //     //    ss_mode_ctrl_monitor_struct.strap_ss_strap_generic_0
    //     //    ss_mode_ctrl_monitor_struct.strap_ss_strap_generic_1
    //     //    ss_mode_ctrl_monitor_struct.strap_ss_strap_generic_2
    //     //    ss_mode_ctrl_monitor_struct.strap_ss_strap_generic_3
    //     //    ss_mode_ctrl_monitor_struct.strap_ss_caliptra_dma_axi_user
    //     //    ss_mode_ctrl_monitor_struct.ss_debug_intent
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal === 1'b1) @(posedge clk_i);
    //
    //    How to assign a struct member, named xyz, from a signal.
    //    All available input signals listed.
    //      ss_mode_ctrl_monitor_struct.xyz = strap_ss_caliptra_base_addr_i;  //    [63:0]
    //      ss_mode_ctrl_monitor_struct.xyz = strap_ss_mci_base_addr_i;  //    [63:0]
    //      ss_mode_ctrl_monitor_struct.xyz = strap_ss_recovery_ifc_base_addr_i;  //    [63:0]
    //      ss_mode_ctrl_monitor_struct.xyz = strap_ss_otp_fc_base_addr_i;  //    [63:0]
    //      ss_mode_ctrl_monitor_struct.xyz = strap_ss_uds_seed_base_addr_i;  //    [63:0]
    //      ss_mode_ctrl_monitor_struct.xyz = strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i;  //    [31:0]
    //      ss_mode_ctrl_monitor_struct.xyz = strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_i;  //    [31:0]
    //      ss_mode_ctrl_monitor_struct.xyz = strap_ss_strap_generic_0_i;  //    [31:0]
    //      ss_mode_ctrl_monitor_struct.xyz = strap_ss_strap_generic_1_i;  //    [31:0]
    //      ss_mode_ctrl_monitor_struct.xyz = strap_ss_strap_generic_2_i;  //    [31:0]
    //      ss_mode_ctrl_monitor_struct.xyz = strap_ss_strap_generic_3_i;  //    [31:0]
    //      ss_mode_ctrl_monitor_struct.xyz = strap_ss_caliptra_dma_axi_user_i;  //    [31:0] 
    //      ss_mode_ctrl_monitor_struct.xyz = ss_debug_intent_i;  //
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code
    // below are examples of how to capture signal values and assign them to
    // structure members.  All available input signals are listed.  The 'while'
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe
    // the next transfer. One clock cycle is consumed between calls to do_monitor.
    while (!any_signal_changed()) @(posedge clk_i);
    strap_ss_caliptra_base_addr_r                             = strap_ss_caliptra_base_addr_i;
    strap_ss_mci_base_addr_r                                  = strap_ss_mci_base_addr_i;
    strap_ss_recovery_ifc_base_addr_r                         = strap_ss_recovery_ifc_base_addr_i;
    strap_ss_otp_fc_base_addr_r                               = strap_ss_otp_fc_base_addr_i;
    strap_ss_uds_seed_base_addr_r                             = strap_ss_uds_seed_base_addr_i;
    strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_r = strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i;
    strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_r        = strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_i;
    strap_ss_strap_generic_0_r                                = strap_ss_strap_generic_0_i;
    strap_ss_strap_generic_1_r                                = strap_ss_strap_generic_1_i;
    strap_ss_strap_generic_2_r                                = strap_ss_strap_generic_2_i;
    strap_ss_strap_generic_3_r                                = strap_ss_strap_generic_3_i;
    ss_debug_intent_r                                         = ss_debug_intent_i;
    strap_ss_caliptra_dma_axi_user_r                          = strap_ss_caliptra_dma_axi_user_i;
    begin: build_return_struct
    // Available struct members:
        ss_mode_ctrl_monitor_struct.strap_ss_caliptra_base_addr                             = strap_ss_caliptra_base_addr_i;
        ss_mode_ctrl_monitor_struct.strap_ss_mci_base_addr                                  = strap_ss_mci_base_addr_i;
        ss_mode_ctrl_monitor_struct.strap_ss_recovery_ifc_base_addr                         = strap_ss_recovery_ifc_base_addr_i;
        ss_mode_ctrl_monitor_struct.strap_ss_otp_fc_base_addr                               = strap_ss_otp_fc_base_addr_i;
        ss_mode_ctrl_monitor_struct.strap_ss_uds_seed_base_addr                             = strap_ss_uds_seed_base_addr_i;
        ss_mode_ctrl_monitor_struct.strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset = strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i;
        ss_mode_ctrl_monitor_struct.strap_ss_num_of_prod_debug_unlock_auth_pk_hashes        = strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_i;
        ss_mode_ctrl_monitor_struct.strap_ss_strap_generic_0                                = strap_ss_strap_generic_0_i;
        ss_mode_ctrl_monitor_struct.strap_ss_strap_generic_1                                = strap_ss_strap_generic_1_i;
        ss_mode_ctrl_monitor_struct.strap_ss_strap_generic_2                                = strap_ss_strap_generic_2_i;
        ss_mode_ctrl_monitor_struct.strap_ss_strap_generic_3                                = strap_ss_strap_generic_3_i;
        ss_mode_ctrl_monitor_struct.ss_debug_intent                                         = ss_debug_intent_i;
        ss_mode_ctrl_monitor_struct.strap_ss_caliptra_dma_axi_user                          = strap_ss_caliptra_dma_axi_user_i;
    end
    // pragma uvmf custom do_monitor end
  endtask


endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

