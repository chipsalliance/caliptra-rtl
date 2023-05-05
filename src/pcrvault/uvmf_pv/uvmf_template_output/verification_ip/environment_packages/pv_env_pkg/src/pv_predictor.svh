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
//   pv_rst_agent_ae receives transactions of type  pv_rst_transaction
//   pv_sha512_write_agent_ae receives transactions of type  pv_write_transaction
//   pv_sha512_block_read_agent_ae receives transactions of type  pv_read_transaction
//   ahb_slave_0_ae receives transactions of type  mvc_sequence_item_base
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//  pv_sha512_write_sb_ap broadcasts transactions of type pv_write_transaction
//  pv_sha512_block_read_sb_ap broadcasts transactions of type pv_read_transaction
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

import pv_reg_adapter_functions_pkg::*;
class pv_predictor #(
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  // Factory registration of this class
  `uvm_component_param_utils( pv_predictor #(
                              CONFIG_T,
                              BASE_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;

  //TODO: Add to predictor class level param inputs?
  localparam CLP_DEBUG_MODE_PV_0 = 32'hAAAA_AAAA;
  localparam CLP_DEBUG_MODE_PV_1 = 32'h5555_5555;

  // Instantiate the analysis exports
  uvm_analysis_imp_pv_rst_agent_ae #(pv_rst_transaction, pv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) pv_rst_agent_ae;
  uvm_analysis_imp_pv_sha512_write_agent_ae #(pv_write_transaction, pv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) pv_sha512_write_agent_ae;
  uvm_analysis_imp_pv_sha512_block_read_agent_ae #(pv_read_transaction, pv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) pv_sha512_block_read_agent_ae;
  uvm_analysis_imp_ahb_slave_0_ae #(mvc_sequence_item_base, pv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) ahb_slave_0_ae;

  
  // Instantiate the analysis ports
  uvm_analysis_port #(pv_write_transaction) pv_sha512_write_sb_ap;
  uvm_analysis_port #(pv_read_transaction)  pv_sha512_block_read_sb_ap;
  uvm_analysis_port #(mvc_sequence_item_base) pv_sb_ahb_ap;

  // Transaction variable for predicted values to be sent out pv_sha512_write_sb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction. 
  typedef pv_write_transaction pv_sha512_write_sb_ap_output_transaction_t;
  pv_sha512_write_sb_ap_output_transaction_t pv_sha512_write_sb_ap_output_transaction;
  // Code for sending output transaction out through pv_sha512_write_sb_ap
  // pv_sha512_write_sb_ap.write(pv_sha512_write_sb_ap_output_transaction);
  // Transaction variable for predicted values to be sent out pv_sha512_block_read_sb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction. 
  typedef pv_read_transaction pv_sha512_block_read_sb_ap_output_transaction_t;
  pv_sha512_block_read_sb_ap_output_transaction_t pv_sha512_block_read_sb_ap_output_transaction;
  // Code for sending output transaction out through pv_sha512_block_read_sb_ap
  // pv_sha512_block_read_sb_ap.write(pv_sha512_block_read_sb_ap_output_transaction);

  typedef ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                                      ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                                      ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                                      ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                                      ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                                      ahb_lite_slave_0_params::AHB_RDATA_WIDTH) pv_sb_ahb_ap_output_transaction_t;
  pv_sb_ahb_ap_output_transaction_t pv_sb_ahb_ap_output_transaction;

  // Define transaction handles for debug visibility 
  pv_rst_transaction pv_rst_agent_ae_debug;
  pv_write_transaction pv_sha512_write_agent_ae_debug;
  pv_read_transaction pv_sha512_block_read_agent_ae_debug;
  mvc_sequence_item_base ahb_slave_0_ae_debug;


  // pragma uvmf custom class_item_additional begin
  pv_reg_model_top p_pv_rm;

  uvm_reg_map p_pv_sha512_write_map;
  uvm_reg_map p_pv_AHB_map;
  uvm_reg_map p_pv_sha512_block_read_map;

  extern function void populate_expected_pv_read_txn(ref pv_sha512_block_read_sb_ap_output_transaction_t t_expected, pv_read_transaction t_received);
  extern function void populate_expected_pv_write_txn(ref pv_sha512_write_sb_ap_output_transaction_t t_expected, pv_write_transaction t_received);

  // pragma uvmf custom class_item_additional end

  // FUNCTION: new
  function new(string name, uvm_component parent);
     super.new(name,parent);
  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

  // FUNCTION: build_phase
  virtual function void build_phase (uvm_phase phase);

    pv_rst_agent_ae               = new("pv_rst_agent_ae", this);
    
    pv_sha512_write_agent_ae      = new("pv_sha512_write_agent_ae", this);
    pv_sha512_block_read_agent_ae = new("pv_sha512_block_read_agent_ae", this);
    ahb_slave_0_ae                = new("ahb_slave_0_ae", this);
    
    pv_sha512_write_sb_ap         = new("pv_sha512_write_sb_ap", this );
    pv_sha512_block_read_sb_ap    = new("pv_sha512_block_read_sb_ap", this );
    pv_sb_ahb_ap                  = new("pv_sb_ahb_ap", this);
  // pragma uvmf custom build_phase begin
    p_pv_rm = configuration.pv_rm;

    p_pv_sha512_write_map         = p_pv_rm.get_map_by_name("pv_sha512_write_map");
    p_pv_sha512_block_read_map    = p_pv_rm.get_map_by_name("pv_sha512_block_read_map");
    p_pv_AHB_map                  = p_pv_rm.get_map_by_name("pv_AHB_map");

  // pragma uvmf custom build_phase end
  endfunction

  // FUNCTION: write_pv_rst_agent_ae
  // Transactions received through pv_rst_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_pv_rst_agent_ae(pv_rst_transaction t);
    // pragma uvmf custom pv_rst_agent_ae_predictor begin
    pv_rst_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through pv_rst_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    pv_sha512_block_read_sb_ap_output_transaction = pv_sha512_block_read_sb_ap_output_transaction_t::type_id::create("pv_sha512_block_read_sb_ap_output_transaction");
    
    //Construct transaction:
    pv_sha512_block_read_sb_ap_output_transaction.read_entry = 'h0;
    pv_sha512_block_read_sb_ap_output_transaction.read_offset = 'h0;
    pv_sha512_block_read_sb_ap_output_transaction.error = 'h0;
    pv_sha512_block_read_sb_ap_output_transaction.last = 'h0;
    pv_sha512_block_read_sb_ap_output_transaction.read_data = 'h0;

    if (!t.set_pwrgood) begin
      //Clear all regs on hard reset
      p_pv_rm.reset();
    end
    
    // Code for sending output transaction out through pv_sha512_block_read_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    pv_sha512_block_read_sb_ap.write(pv_sha512_block_read_sb_ap_output_transaction);
    // pragma uvmf custom pv_rst_agent_ae_predictor end
  endfunction

  // FUNCTION: write_pv_sha512_write_agent_ae
  // Transactions received through pv_sha512_write_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_pv_sha512_write_agent_ae(pv_write_transaction t);
    // pragma uvmf custom pv_sha512_write_agent_ae_predictor begin
    pv_sha512_write_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through pv_sha512_write_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    pv_sha512_write_sb_ap_output_transaction = pv_sha512_write_sb_ap_output_transaction_t::type_id::create("pv_sha512_write_sb_ap_output_transaction");
    
    populate_expected_pv_write_txn(pv_sha512_write_sb_ap_output_transaction, t);
    // Code for sending output transaction out through pv_sha512_write_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    pv_sha512_write_sb_ap.write(pv_sha512_write_sb_ap_output_transaction);
    
    // pragma uvmf custom pv_sha512_write_agent_ae_predictor end
  endfunction

  // FUNCTION: write_pv_sha512_block_read_agent_ae
  // Transactions received through pv_sha512_block_read_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_pv_sha512_block_read_agent_ae(pv_read_transaction t);
    // pragma uvmf custom pv_sha512_block_read_agent_ae_predictor begin
    pv_sha512_block_read_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through pv_sha512_block_read_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    pv_sha512_block_read_sb_ap_output_transaction = pv_sha512_block_read_sb_ap_output_transaction_t::type_id::create("pv_sha512_block_read_sb_ap_output_transaction");
    
    populate_expected_pv_read_txn(pv_sha512_block_read_sb_ap_output_transaction, t);
    
    // Code for sending output transaction out through pv_sha512_block_read_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    pv_sha512_block_read_sb_ap.write(pv_sha512_block_read_sb_ap_output_transaction);
    // pragma uvmf custom pv_sha512_block_read_agent_ae_predictor end
  endfunction

  // FUNCTION: write_ahb_slave_0_ae
  // Transactions received through ahb_slave_0_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_ahb_slave_0_ae(mvc_sequence_item_base t);
    // pragma uvmf custom ahb_slave_0_ae_predictor begin
    ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_txn;
    uvm_reg pv_reg;
    uvm_reg_data_t pv_reg_data;
    uvm_reg val_reg;
    uvm_reg_data_t val_reg_data;
    int entry, offset;
    uvm_status_e sts;
    string reg_name;
    reg [PV_DATA_W-1:0] data_active;
    reg [ahb_lite_slave_0_params::AHB_WDATA_WIDTH-1:0] address_aligned;

    ahb_slave_0_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through ahb_slave_0_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    pv_sb_ahb_ap_output_transaction = pv_sb_ahb_ap_output_transaction_t::type_id::create("pv_sb_ahb_ap_output_transaction");
    $cast(ahb_txn, t);

    //Convert data from AHB to txn
    address_aligned = ahb_txn.address & ~(PV_DATA_W/8 - 1);
    data_active = PV_DATA_W'(ahb_txn.data[0] >> (8*(address_aligned % (ahb_lite_slave_0_params::AHB_WDATA_WIDTH/8))));

    if(ahb_txn.RnW == AHB_WRITE) begin
      //Copy txn and modify required fields later
      pv_sb_ahb_ap_output_transaction.copy(ahb_txn);

      //If this is a write to clear (and lock = 0), clear regs of that entry
      if ((ahb_txn.address >= `PV_REG_PCR_CTRL_0) && (ahb_txn.address < `PV_REG_PCR_ENTRY_0_0)) begin
        pv_reg = p_pv_AHB_map.get_reg_by_offset(ahb_txn.address);
        reg_name = pv_reg.get_full_name();
        pv_reg_data = pv_reg.get_mirrored_value();

        val_reg = p_pv_AHB_map.get_reg_by_offset('h1_0000);
        val_reg_data = val_reg.get();

        
        //Two possible scenarios: lock = 0 and clear = 1
        //lock = 1 and clear = 1 (transition from lock = 0 so this clear would still go through)
        if(pv_reg_data[1:0] inside {'h2, 'h3}) begin
          
          //Clear the entry that is being accessed
          {offset, entry} = convert_addr_to_pv(ahb_txn.address);
          for(offset = 0; offset < PV_NUM_DWORDS; offset++) begin
            p_pv_rm.pv_reg_rm.PCR_ENTRY[entry][offset].predict('h0);
            p_pv_rm.pv_reg_rm.PCR_ENTRY[entry][offset].set('h0);
          end
        end
      end
    end
    else begin
      //AHB Read
      pv_reg = p_pv_AHB_map.get_reg_by_offset(ahb_txn.address);
      pv_reg_data = pv_reg.get_mirrored_value();
      pv_sb_ahb_ap_output_transaction.copy(ahb_txn);
      pv_sb_ahb_ap_output_transaction.data[0] = pv_reg_data;
    end
    // Code for sending output transaction out through pv_sha512_write_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    pv_sb_ahb_ap.write(pv_sb_ahb_ap_output_transaction);
    // pragma uvmf custom ahb_slave_0_ae_predictor end
  endfunction


endclass 

// pragma uvmf custom external begin
  function void pv_predictor::populate_expected_pv_read_txn (ref pv_sha512_block_read_sb_ap_output_transaction_t t_expected, pv_read_transaction t_received);

    uvm_reg pv_reg;
    uvm_reg_data_t pv_reg_data;


    pv_reg = p_pv_rm.get_reg_by_name($sformatf("PCR_ENTRY[%0d][%0d]",t_received.read_entry,t_received.read_offset));
    pv_reg_data = pv_reg.get_mirrored_value();

    t_expected.read_data = pv_reg_data[31:0];
    t_expected.error = 'b0; //Currently no error logic in PCR
    t_expected.last = t_received.last; //TODO fix last flag logic
    t_expected.read_entry = t_received.read_entry;
    t_expected.read_offset = t_received.read_offset;

  endfunction

  function void pv_predictor::populate_expected_pv_write_txn (ref pv_sha512_write_sb_ap_output_transaction_t t_expected, pv_write_transaction t_received);
    
    t_expected = t_received;
    t_expected.error = 'b0; //Currently no error logic in PCR

  endfunction
// pragma uvmf custom external end

