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
//   kv_rst_agent_ae receives transactions of type  kv_rst_transaction
//   kv_hmac_write_agent_ae receives transactions of type  kv_write_transaction
//   kv_sha512_write_agent_ae receives transactions of type  kv_write_transaction
//   kv_ecc_write_agent_ae receives transactions of type  kv_write_transaction
//   kv_doe_write_agent_ae receives transactions of type  kv_write_transaction
//   kv_hmac_key_read_agent_ae receives transactions of type  kv_read_transaction
//   kv_hmac_block_read_agent_ae receives transactions of type  kv_read_transaction
//   kv_hmac_sha512_read_agent_ae receives transactions of type  kv_read_transaction
//   kv_hmac_ecc_privkey_read_agent_ae receives transactions of type  kv_read_transaction
//   kv_ecc_seed_read_agent_ae receives transactions of type  kv_read_transaction
//   kv_ecc_msg_read_agent_ae receives transactions of type  kv_read_transaction
//   ahb_slave_0_ae receives transactions of type  mvc_sequence_item_base
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//  kv_sb_ap broadcasts transactions of type kv_read_transaction
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class kv_predictor #(
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  // Factory registration of this class
  `uvm_component_param_utils( kv_predictor #(
                              CONFIG_T,
                              BASE_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;

  
  // Instantiate the analysis exports
  uvm_analysis_imp_kv_rst_agent_ae #(kv_rst_transaction, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) kv_rst_agent_ae;

  uvm_analysis_imp_kv_hmac_write_agent_ae #(kv_write_transaction, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) kv_hmac_write_agent_ae;
  uvm_analysis_imp_kv_sha512_write_agent_ae #(kv_write_transaction, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) kv_sha512_write_agent_ae;
  uvm_analysis_imp_kv_ecc_write_agent_ae #(kv_write_transaction, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) kv_ecc_write_agent_ae;
  uvm_analysis_imp_kv_doe_write_agent_ae #(kv_write_transaction, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) kv_doe_write_agent_ae;
  uvm_analysis_imp_kv_hmac_key_read_agent_ae #(kv_read_transaction, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) kv_hmac_key_read_agent_ae;
  uvm_analysis_imp_kv_hmac_block_read_agent_ae #(kv_read_transaction, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) kv_hmac_block_read_agent_ae;
  uvm_analysis_imp_kv_hmac_sha512_read_agent_ae #(kv_read_transaction, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) kv_hmac_sha512_read_agent_ae;
  uvm_analysis_imp_kv_hmac_ecc_privkey_read_agent_ae #(kv_read_transaction, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) kv_hmac_ecc_privkey_read_agent_ae;
  uvm_analysis_imp_kv_ecc_seed_read_agent_ae #(kv_read_transaction, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) kv_ecc_seed_read_agent_ae;
  uvm_analysis_imp_kv_ecc_msg_read_agent_ae #(kv_read_transaction, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) kv_ecc_msg_read_agent_ae;
  uvm_analysis_imp_ahb_slave_0_ae #(mvc_sequence_item_base, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) ahb_slave_0_ae;

  
  // Instantiate the analysis ports
  uvm_analysis_port #(kv_read_transaction) kv_sb_ap;


  // Transaction variable for predicted values to be sent out kv_sb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction. 
  typedef kv_read_transaction kv_sb_ap_output_transaction_t;
  kv_sb_ap_output_transaction_t kv_sb_ap_output_transaction;
  // Code for sending output transaction out through kv_sb_ap
  // kv_sb_ap.write(kv_sb_ap_output_transaction);

  // Define transaction handles for debug visibility 
  kv_rst_transaction kv_rst_agent_ae_debug;
  kv_write_transaction kv_hmac_write_agent_ae_debug;
  kv_write_transaction kv_sha512_write_agent_ae_debug;
  kv_write_transaction kv_ecc_write_agent_ae_debug;
  kv_write_transaction kv_doe_write_agent_ae_debug;
  kv_read_transaction kv_hmac_key_read_agent_ae_debug;
  kv_read_transaction kv_hmac_block_read_agent_ae_debug;
  kv_read_transaction kv_hmac_sha512_read_agent_ae_debug;
  kv_read_transaction kv_hmac_ecc_privkey_read_agent_ae_debug;
  kv_read_transaction kv_ecc_seed_read_agent_ae_debug;
  kv_read_transaction kv_ecc_msg_read_agent_ae_debug;
  mvc_sequence_item_base ahb_slave_0_ae_debug;


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

    kv_rst_agent_ae = new("kv_rst_agent_ae", this);
    kv_hmac_write_agent_ae = new("kv_hmac_write_agent_ae", this);
    kv_sha512_write_agent_ae = new("kv_sha512_write_agent_ae", this);
    kv_ecc_write_agent_ae = new("kv_ecc_write_agent_ae", this);
    kv_doe_write_agent_ae = new("kv_doe_write_agent_ae", this);
    kv_hmac_key_read_agent_ae = new("kv_hmac_key_read_agent_ae", this);
    kv_hmac_block_read_agent_ae = new("kv_hmac_block_read_agent_ae", this);
    kv_hmac_sha512_read_agent_ae = new("kv_hmac_sha512_read_agent_ae", this);
    kv_hmac_ecc_privkey_read_agent_ae = new("kv_hmac_ecc_privkey_read_agent_ae", this);
    kv_ecc_seed_read_agent_ae = new("kv_ecc_seed_read_agent_ae", this);
    kv_ecc_msg_read_agent_ae = new("kv_ecc_msg_read_agent_ae", this);
    ahb_slave_0_ae = new("ahb_slave_0_ae", this);
    kv_sb_ap =new("kv_sb_ap", this );
  // pragma uvmf custom build_phase begin
  // pragma uvmf custom build_phase end
  endfunction

  // FUNCTION: write_kv_rst_agent_ae
  // Transactions received through kv_rst_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_rst_agent_ae(kv_rst_transaction t);
    // pragma uvmf custom kv_rst_agent_ae_predictor begin
    kv_rst_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_rst_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The kv_predictor::write_kv_rst_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_rst_agent_ae_predictor end
  endfunction

  // FUNCTION: write_kv_hmac_write_agent_ae
  // Transactions received through kv_hmac_write_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_hmac_write_agent_ae(kv_write_transaction t);
    // pragma uvmf custom kv_hmac_write_agent_ae_predictor begin
    kv_hmac_write_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_hmac_write_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The kv_predictor::write_kv_hmac_write_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_hmac_write_agent_ae_predictor end
  endfunction

  // FUNCTION: write_kv_sha512_write_agent_ae
  // Transactions received through kv_sha512_write_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_sha512_write_agent_ae(kv_write_transaction t);
    // pragma uvmf custom kv_sha512_write_agent_ae_predictor begin
    kv_sha512_write_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_sha512_write_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The kv_predictor::write_kv_sha512_write_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_sha512_write_agent_ae_predictor end
  endfunction

  // FUNCTION: write_kv_ecc_write_agent_ae
  // Transactions received through kv_ecc_write_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_ecc_write_agent_ae(kv_write_transaction t);
    // pragma uvmf custom kv_ecc_write_agent_ae_predictor begin
    kv_ecc_write_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_ecc_write_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The kv_predictor::write_kv_ecc_write_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_ecc_write_agent_ae_predictor end
  endfunction

  // FUNCTION: write_kv_doe_write_agent_ae
  // Transactions received through kv_doe_write_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_doe_write_agent_ae(kv_write_transaction t);
    // pragma uvmf custom kv_doe_write_agent_ae_predictor begin
    kv_doe_write_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_doe_write_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The kv_predictor::write_kv_doe_write_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_doe_write_agent_ae_predictor end
  endfunction

  // FUNCTION: write_kv_hmac_key_read_agent_ae
  // Transactions received through kv_hmac_key_read_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_hmac_key_read_agent_ae(kv_read_transaction t);
    // pragma uvmf custom kv_hmac_key_read_agent_ae_predictor begin
    kv_hmac_key_read_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_hmac_key_read_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The kv_predictor::write_kv_hmac_key_read_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_hmac_key_read_agent_ae_predictor end
  endfunction

  // FUNCTION: write_kv_hmac_block_read_agent_ae
  // Transactions received through kv_hmac_block_read_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_hmac_block_read_agent_ae(kv_read_transaction t);
    // pragma uvmf custom kv_hmac_block_read_agent_ae_predictor begin
    kv_hmac_block_read_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_hmac_block_read_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The kv_predictor::write_kv_hmac_block_read_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_hmac_block_read_agent_ae_predictor end
  endfunction

  // FUNCTION: write_kv_hmac_sha512_read_agent_ae
  // Transactions received through kv_hmac_sha512_read_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_hmac_sha512_read_agent_ae(kv_read_transaction t);
    // pragma uvmf custom kv_hmac_sha512_read_agent_ae_predictor begin
    kv_hmac_sha512_read_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_hmac_sha512_read_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The kv_predictor::write_kv_hmac_sha512_read_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_hmac_sha512_read_agent_ae_predictor end
  endfunction

  // FUNCTION: write_kv_hmac_ecc_privkey_read_agent_ae
  // Transactions received through kv_hmac_ecc_privkey_read_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_hmac_ecc_privkey_read_agent_ae(kv_read_transaction t);
    // pragma uvmf custom kv_hmac_ecc_privkey_read_agent_ae_predictor begin
    kv_hmac_ecc_privkey_read_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_hmac_ecc_privkey_read_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The kv_predictor::write_kv_hmac_ecc_privkey_read_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_hmac_ecc_privkey_read_agent_ae_predictor end
  endfunction

  // FUNCTION: write_kv_ecc_seed_read_agent_ae
  // Transactions received through kv_ecc_seed_read_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_ecc_seed_read_agent_ae(kv_read_transaction t);
    // pragma uvmf custom kv_ecc_seed_read_agent_ae_predictor begin
    kv_ecc_seed_read_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_ecc_seed_read_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The kv_predictor::write_kv_ecc_seed_read_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_ecc_seed_read_agent_ae_predictor end
  endfunction

  // FUNCTION: write_kv_ecc_msg_read_agent_ae
  // Transactions received through kv_ecc_msg_read_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_ecc_msg_read_agent_ae(kv_read_transaction t);
    // pragma uvmf custom kv_ecc_msg_read_agent_ae_predictor begin
    kv_ecc_msg_read_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_ecc_msg_read_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The kv_predictor::write_kv_ecc_msg_read_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_ecc_msg_read_agent_ae_predictor end
  endfunction

  // FUNCTION: write_ahb_slave_0_ae
  // Transactions received through ahb_slave_0_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_ahb_slave_0_ae(mvc_sequence_item_base t);
    // pragma uvmf custom ahb_slave_0_ae_predictor begin
    ahb_slave_0_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through ahb_slave_0_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The kv_predictor::write_ahb_slave_0_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom ahb_slave_0_ae_predictor end
  endfunction


endclass 

// pragma uvmf custom external begin
// pragma uvmf custom external end

