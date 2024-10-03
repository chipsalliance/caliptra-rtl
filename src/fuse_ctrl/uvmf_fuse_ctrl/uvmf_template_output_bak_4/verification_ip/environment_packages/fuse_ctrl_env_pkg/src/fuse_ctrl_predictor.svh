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
//
//----------------------------------------------------------------------
//
// DESCRIPTION: This analysis component contains analysis_exports for receiving
//   data and analysis_ports for sending data.
// 
//   This analysis component has the following analysis_exports that receive the 
//   listed transaction type.
//   
//   fuse_ctrl_rst_agent_ae receives transactions of type  fuse_ctrl_rst_transaction
//   fuse_ctrl_core_axi_write_agent_ae receives transactions of type  fuse_ctrl_write_transaction
//   fuse_ctrl_prim_axi_write_agent_ae receives transactions of type  fuse_ctrl_write_transaction
//   fuse_ctrl_core_axi_read_agent_ae receives transactions of type  fuse_ctrl_read_transaction
//   fuse_ctrl_prim_axi_read_agent_ae receives transactions of type  fuse_ctrl_read_transaction
//   fuse_ctrl_secreg_axi_read_agent_ae receives transactions of type  fuse_ctrl_read_transaction
//   fuse_ctrl_lc_otp_if_agent_ae receives transactions of type  fuse_ctrl_read_transaction
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//  fuse_ctrl_sb_ap broadcasts transactions of type fuse_ctrl_read_transaction
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class fuse_ctrl_predictor #(
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  // Factory registration of this class
  `uvm_component_param_utils( fuse_ctrl_predictor #(
                              CONFIG_T,
                              BASE_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;

  
  // Instantiate the analysis exports
  uvm_analysis_imp_fuse_ctrl_rst_agent_ae #(fuse_ctrl_rst_transaction, fuse_ctrl_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_rst_agent_ae;
  uvm_analysis_imp_fuse_ctrl_core_axi_write_agent_ae #(fuse_ctrl_write_transaction, fuse_ctrl_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_core_axi_write_agent_ae;
  uvm_analysis_imp_fuse_ctrl_prim_axi_write_agent_ae #(fuse_ctrl_write_transaction, fuse_ctrl_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_prim_axi_write_agent_ae;
  uvm_analysis_imp_fuse_ctrl_core_axi_read_agent_ae #(fuse_ctrl_read_transaction, fuse_ctrl_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_core_axi_read_agent_ae;
  uvm_analysis_imp_fuse_ctrl_prim_axi_read_agent_ae #(fuse_ctrl_read_transaction, fuse_ctrl_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_prim_axi_read_agent_ae;
  uvm_analysis_imp_fuse_ctrl_secreg_axi_read_agent_ae #(fuse_ctrl_read_transaction, fuse_ctrl_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_secreg_axi_read_agent_ae;
  uvm_analysis_imp_fuse_ctrl_lc_otp_if_agent_ae #(fuse_ctrl_read_transaction, fuse_ctrl_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_lc_otp_if_agent_ae;

  
  // Instantiate the analysis ports
  uvm_analysis_port #(fuse_ctrl_read_transaction) fuse_ctrl_sb_ap;


  // Transaction variable for predicted values to be sent out fuse_ctrl_sb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction. 
  typedef fuse_ctrl_read_transaction fuse_ctrl_sb_ap_output_transaction_t;
  fuse_ctrl_sb_ap_output_transaction_t fuse_ctrl_sb_ap_output_transaction;
  // Code for sending output transaction out through fuse_ctrl_sb_ap
  // fuse_ctrl_sb_ap.write(fuse_ctrl_sb_ap_output_transaction);

  // Define transaction handles for debug visibility 
  fuse_ctrl_rst_transaction fuse_ctrl_rst_agent_ae_debug;
  fuse_ctrl_write_transaction fuse_ctrl_core_axi_write_agent_ae_debug;
  fuse_ctrl_write_transaction fuse_ctrl_prim_axi_write_agent_ae_debug;
  fuse_ctrl_read_transaction fuse_ctrl_core_axi_read_agent_ae_debug;
  fuse_ctrl_read_transaction fuse_ctrl_prim_axi_read_agent_ae_debug;
  fuse_ctrl_read_transaction fuse_ctrl_secreg_axi_read_agent_ae_debug;
  fuse_ctrl_read_transaction fuse_ctrl_lc_otp_if_agent_ae_debug;


  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  // FUNCTION: new
  function new(string name, uvm_component parent);
     super.new(name,parent);
    `uvm_warning("PREDICTOR_REVIEW", "This predictor has been created either through generation or re-generation with merging.  Remove this warning after the predictor has been reviewed.")
  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

  // FUNCTION: build_phase
  virtual function void build_phase (uvm_phase phase);

    fuse_ctrl_rst_agent_ae = new("fuse_ctrl_rst_agent_ae", this);
    fuse_ctrl_core_axi_write_agent_ae = new("fuse_ctrl_core_axi_write_agent_ae", this);
    fuse_ctrl_prim_axi_write_agent_ae = new("fuse_ctrl_prim_axi_write_agent_ae", this);
    fuse_ctrl_core_axi_read_agent_ae = new("fuse_ctrl_core_axi_read_agent_ae", this);
    fuse_ctrl_prim_axi_read_agent_ae = new("fuse_ctrl_prim_axi_read_agent_ae", this);
    fuse_ctrl_secreg_axi_read_agent_ae = new("fuse_ctrl_secreg_axi_read_agent_ae", this);
    fuse_ctrl_lc_otp_if_agent_ae = new("fuse_ctrl_lc_otp_if_agent_ae", this);
    fuse_ctrl_sb_ap =new("fuse_ctrl_sb_ap", this );
  // pragma uvmf custom build_phase begin
  // pragma uvmf custom build_phase end
  endfunction

  // FUNCTION: write_fuse_ctrl_rst_agent_ae
  // Transactions received through fuse_ctrl_rst_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_rst_agent_ae(fuse_ctrl_rst_transaction t);
    // pragma uvmf custom fuse_ctrl_rst_agent_ae_predictor begin
    fuse_ctrl_rst_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_rst_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    fuse_ctrl_sb_ap_output_transaction = fuse_ctrl_sb_ap_output_transaction_t::type_id::create("fuse_ctrl_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The fuse_ctrl_predictor::write_fuse_ctrl_rst_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through fuse_ctrl_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    fuse_ctrl_sb_ap.write(fuse_ctrl_sb_ap_output_transaction);
    // pragma uvmf custom fuse_ctrl_rst_agent_ae_predictor end
  endfunction

  // FUNCTION: write_fuse_ctrl_core_axi_write_agent_ae
  // Transactions received through fuse_ctrl_core_axi_write_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_core_axi_write_agent_ae(fuse_ctrl_write_transaction t);
    // pragma uvmf custom fuse_ctrl_core_axi_write_agent_ae_predictor begin
    fuse_ctrl_core_axi_write_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_core_axi_write_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    fuse_ctrl_sb_ap_output_transaction = fuse_ctrl_sb_ap_output_transaction_t::type_id::create("fuse_ctrl_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The fuse_ctrl_predictor::write_fuse_ctrl_core_axi_write_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through fuse_ctrl_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    fuse_ctrl_sb_ap.write(fuse_ctrl_sb_ap_output_transaction);
    // pragma uvmf custom fuse_ctrl_core_axi_write_agent_ae_predictor end
  endfunction

  // FUNCTION: write_fuse_ctrl_prim_axi_write_agent_ae
  // Transactions received through fuse_ctrl_prim_axi_write_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_prim_axi_write_agent_ae(fuse_ctrl_write_transaction t);
    // pragma uvmf custom fuse_ctrl_prim_axi_write_agent_ae_predictor begin
    fuse_ctrl_prim_axi_write_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_prim_axi_write_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    fuse_ctrl_sb_ap_output_transaction = fuse_ctrl_sb_ap_output_transaction_t::type_id::create("fuse_ctrl_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The fuse_ctrl_predictor::write_fuse_ctrl_prim_axi_write_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through fuse_ctrl_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    fuse_ctrl_sb_ap.write(fuse_ctrl_sb_ap_output_transaction);
    // pragma uvmf custom fuse_ctrl_prim_axi_write_agent_ae_predictor end
  endfunction

  // FUNCTION: write_fuse_ctrl_core_axi_read_agent_ae
  // Transactions received through fuse_ctrl_core_axi_read_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_core_axi_read_agent_ae(fuse_ctrl_read_transaction t);
    // pragma uvmf custom fuse_ctrl_core_axi_read_agent_ae_predictor begin
    fuse_ctrl_core_axi_read_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_core_axi_read_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    fuse_ctrl_sb_ap_output_transaction = fuse_ctrl_sb_ap_output_transaction_t::type_id::create("fuse_ctrl_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The fuse_ctrl_predictor::write_fuse_ctrl_core_axi_read_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through fuse_ctrl_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    fuse_ctrl_sb_ap.write(fuse_ctrl_sb_ap_output_transaction);
    // pragma uvmf custom fuse_ctrl_core_axi_read_agent_ae_predictor end
  endfunction

  // FUNCTION: write_fuse_ctrl_prim_axi_read_agent_ae
  // Transactions received through fuse_ctrl_prim_axi_read_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_prim_axi_read_agent_ae(fuse_ctrl_read_transaction t);
    // pragma uvmf custom fuse_ctrl_prim_axi_read_agent_ae_predictor begin
    fuse_ctrl_prim_axi_read_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_prim_axi_read_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    fuse_ctrl_sb_ap_output_transaction = fuse_ctrl_sb_ap_output_transaction_t::type_id::create("fuse_ctrl_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The fuse_ctrl_predictor::write_fuse_ctrl_prim_axi_read_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through fuse_ctrl_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    fuse_ctrl_sb_ap.write(fuse_ctrl_sb_ap_output_transaction);
    // pragma uvmf custom fuse_ctrl_prim_axi_read_agent_ae_predictor end
  endfunction

  // FUNCTION: write_fuse_ctrl_secreg_axi_read_agent_ae
  // Transactions received through fuse_ctrl_secreg_axi_read_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_secreg_axi_read_agent_ae(fuse_ctrl_read_transaction t);
    // pragma uvmf custom fuse_ctrl_secreg_axi_read_agent_ae_predictor begin
    fuse_ctrl_secreg_axi_read_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_secreg_axi_read_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    fuse_ctrl_sb_ap_output_transaction = fuse_ctrl_sb_ap_output_transaction_t::type_id::create("fuse_ctrl_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The fuse_ctrl_predictor::write_fuse_ctrl_secreg_axi_read_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through fuse_ctrl_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    fuse_ctrl_sb_ap.write(fuse_ctrl_sb_ap_output_transaction);
    // pragma uvmf custom fuse_ctrl_secreg_axi_read_agent_ae_predictor end
  endfunction

  // FUNCTION: write_fuse_ctrl_lc_otp_if_agent_ae
  // Transactions received through fuse_ctrl_lc_otp_if_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_lc_otp_if_agent_ae(fuse_ctrl_read_transaction t);
    // pragma uvmf custom fuse_ctrl_lc_otp_if_agent_ae_predictor begin
    fuse_ctrl_lc_otp_if_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_lc_otp_if_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    fuse_ctrl_sb_ap_output_transaction = fuse_ctrl_sb_ap_output_transaction_t::type_id::create("fuse_ctrl_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The fuse_ctrl_predictor::write_fuse_ctrl_lc_otp_if_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through fuse_ctrl_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    fuse_ctrl_sb_ap.write(fuse_ctrl_sb_ap_output_transaction);
    // pragma uvmf custom fuse_ctrl_lc_otp_if_agent_ae_predictor end
  endfunction


endclass 

// pragma uvmf custom external begin
// pragma uvmf custom external end

