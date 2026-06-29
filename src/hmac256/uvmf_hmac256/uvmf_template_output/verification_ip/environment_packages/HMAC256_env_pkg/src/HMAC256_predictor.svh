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
//   hmac256_rst_agent_ae receives transactions of type  HMAC256_rst_transaction
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//  hmac256_sb_ahb_ap broadcasts transactions of type ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH)
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class HMAC256_predictor #(
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  // Factory registration of this class
  `uvm_component_param_utils( HMAC256_predictor #(
                              CONFIG_T,
                              BASE_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;

  
  // Instantiate the analysis exports
  uvm_analysis_imp_hmac_rst_agent_ae #(HMAC256_rst_transaction, HMAC256_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) hmac256_rst_agent_ae;

  
  // Instantiate the analysis ports
  uvm_analysis_port #(mvc_sequence_item_base) hmac256_sb_ahb_ap;

 
  // Instantiate QVIP analysis exports
  uvm_analysis_imp_ahb_slave_0_ae #(mvc_sequence_item_base, HMAC256_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) ahb_slave_0_ae;

  // Transaction variable for predicted values to be sent out hmac256_sb_ahb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction. 
  typedef ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) hmac256_sb_ahb_ap_output_transaction_t;
  hmac256_sb_ahb_ap_output_transaction_t hmac256_sb_ahb_ap_output_transaction;
  // Code for sending output transaction out through hmac256_sb_ahb_ap
  // hmac256_sb_ahb_ap.write(hmac256_sb_ahb_ap_output_transaction);

  // Define transaction handles for debug visibility 
  HMAC256_rst_transaction hmac256_rst_agent_ae_debug;

  // Create QVIP transaction handles for debug visibility 
  mvc_sequence_item_base ahb_slave_0_ae_debug_t;
  // Create transaction handles for visibility in visualizer

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  // FUNCTION: new
  function new(string name, uvm_component parent);
     super.new(name,parent);
  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

  // FUNCTION: build_phase
  virtual function void build_phase (uvm_phase phase);

    hmac256_rst_agent_ae = new("hmac256_rst_agent_ae", this);
    ahb_slave_0_ae = new("ahb_slave_0_ae", this);
    hmac256_sb_ahb_ap =new("hmac256_sb_ahb_ap", this );
  // pragma uvmf custom build_phase begin
  // pragma uvmf custom build_phase end
  endfunction

  // FUNCTION: write_hmac_rst_agent_ae
  // Transactions received through hmac256_rst_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_hmac_rst_agent_ae(HMAC256_rst_transaction t);
    // pragma uvmf custom hmac256_rst_agent_ae_predictor begin
    hmac256_rst_agent_ae_debug = t;
    // pragma uvmf custom hmac256_rst_agent_ae_predictor end
  endfunction


  // FUNCTION: write_ahb_slave_0_ae
  // QVIP transactions received through ahb_slave_0_ae initiate the execution of this function.
  // This function casts incoming QVIP transactions into the correct protocol type and then performs prediction 
  // of DUT output values based on DUT input, configuration and state
  virtual function void write_ahb_slave_0_ae(mvc_sequence_item_base _t);
    // pragma uvmf custom ahb_slave_0_ae_predictor begin
    ahb_slave_0_ae_debug_t = _t;
    // pragma uvmf custom ahb_slave_0_ae_predictor end
  endfunction
  
endclass 

// pragma uvmf custom external begin
// pragma uvmf custom external end

