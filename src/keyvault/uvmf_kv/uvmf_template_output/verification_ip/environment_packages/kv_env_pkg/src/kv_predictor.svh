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
//   kv_sha512_block_read_agent_ae receives transactions of type  kv_read_transaction
//   kv_ecc_privkey_read_agent_ae receives transactions of type  kv_read_transaction
//   kv_ecc_seed_read_agent_ae receives transactions of type  kv_read_transaction
//   ahb_slave_0_ae receives transactions of type  mvc_sequence_item_base
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//  kv_sb_ap broadcasts transactions of type kv_read_transaction
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

import kv_reg_adapter_functions_pkg::*;
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

  //TODO: Add to predictor class level param inputs?
  localparam CLP_DEBUG_MODE_KV_0 = 32'hAAAA_AAAA;
  localparam CLP_DEBUG_MODE_KV_1 = 32'h5555_5555;
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
  uvm_analysis_imp_kv_sha512_block_read_agent_ae #(kv_read_transaction, kv_predictor #(
                             .CONFIG_T(CONFIG_T),
                             .BASE_T(BASE_T)
                              )
) kv_sha512_block_read_agent_ae;
  uvm_analysis_imp_kv_ecc_privkey_read_agent_ae #(kv_read_transaction, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) kv_ecc_privkey_read_agent_ae;
  uvm_analysis_imp_kv_ecc_seed_read_agent_ae #(kv_read_transaction, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) kv_ecc_seed_read_agent_ae;
  uvm_analysis_imp_ahb_slave_0_ae #(mvc_sequence_item_base, kv_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) ahb_slave_0_ae;

  
  // Instantiate the analysis ports
  uvm_analysis_port #(kv_write_transaction) kv_hmac_write_sb_ap;
  uvm_analysis_port #(kv_write_transaction) kv_sha512_write_sb_ap;
  uvm_analysis_port #(kv_write_transaction) kv_ecc_write_sb_ap;
  uvm_analysis_port #(kv_write_transaction) kv_doe_write_sb_ap;

  uvm_analysis_port #(kv_read_transaction) kv_sb_ap;
  uvm_analysis_port #(kv_read_transaction) kv_hmac_key_read_sb_ap;
  uvm_analysis_port #(kv_read_transaction) kv_hmac_block_read_sb_ap;
  uvm_analysis_port #(kv_read_transaction) kv_sha512_block_read_sb_ap;
  uvm_analysis_port #(kv_read_transaction) kv_ecc_privkey_read_sb_ap;
  uvm_analysis_port #(kv_read_transaction) kv_ecc_seed_read_sb_ap;
  uvm_analysis_port #(mvc_sequence_item_base) kv_sb_ahb_ap;

  // Transaction variable for predicted values to be sent out kv_sb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction. 
  typedef kv_read_transaction kv_sb_ap_output_transaction_t;
  kv_sb_ap_output_transaction_t kv_sb_ap_output_transaction;

  typedef kv_write_transaction kv_sb_ap_output_transaction_write_t;
  kv_sb_ap_output_transaction_write_t kv_sb_ap_output_transaction_write;

  // typedef mvc_sequence_item_base kv_sb_ahb_ap_output_transaction_t;
  // kv_sb_ahb_ap_output_transaction_t kv_sb_ahb_ap_output_transaction;

  typedef ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                                      ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                                      ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                                      ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                                      ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                                      ahb_lite_slave_0_params::AHB_RDATA_WIDTH) kv_sb_ahb_ap_output_transaction_t;
  kv_sb_ahb_ap_output_transaction_t kv_sb_ahb_ap_output_transaction;

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
  kv_read_transaction kv_sha512_block_read_agent_ae_debug;
  kv_read_transaction kv_ecc_privkey_read_agent_ae_debug;
  kv_read_transaction kv_ecc_seed_read_agent_ae_debug;

  mvc_sequence_item_base ahb_slave_0_ae_debug;


  // pragma uvmf custom class_item_additional begin
  kv_reg_model_top p_kv_rm;

  //Write maps
  uvm_reg_map p_kv_hmac_write_map; //Block map
  uvm_reg_map p_kv_sha512_write_map;
  uvm_reg_map p_kv_ecc_write_map;
  uvm_reg_map p_kv_doe_write_map;

  //AHB map
  uvm_reg_map p_kv_AHB_map; //Block map

  //Read maps
  uvm_reg_map p_kv_hmac_key_read_map;
  uvm_reg_map p_kv_hmac_block_read_map;
  uvm_reg_map p_kv_sha512_block_read_map;
  uvm_reg_map p_kv_ecc_privkey_read_map;
  uvm_reg_map p_kv_ecc_seed_read_map;

  uvm_reg clear_secrets_reg;
  uvm_reg_data_t clear_secrets_data;

  string client;
  logic [KV_ENTRY_SIZE_W-1:0]last_dword_written[0:KV_NUM_KEYS-1];

  // process running_dly_jobs[$];
  // int unsigned job_end_count[time];
  // bit write_entry_pending = 0;
  // bit send_hmac_write_txn = 0;
  bit set_val_ctrl_derived = 0;
  logic [KV_NUM_KEYS-1:0] val_ctrl_derived_data = 0;
  logic [KV_NUM_KEYS-1:0] key_entry_ctrl_we = 0;

  //Set when lock_wr/lock_use is 0 and set by AHB txn. Reset only during reset
  logic [KV_NUM_KEYS-1:0] key_ctrl_lock_wr = 0;
  logic [KV_NUM_KEYS-1:0] key_ctrl_lock_use = 0;

  extern function void populate_expected_kv_read_txn(ref kv_sb_ap_output_transaction_t t_expected, kv_read_transaction t_received, string client);
  extern function void populate_expected_kv_write_txn(ref kv_sb_ap_output_transaction_write_t t_expected, kv_write_transaction t_received);
  extern task          poll_and_run_delay_jobs();
  // extern function      send_delayed_expected_transactions_hmac_write(kv_write_transaction t);
  // extern function      send_delayed_expected_transactions_sha512_write(kv_write_transaction t);
  // extern function      send_delayed_expected_transactions_ecc_write(kv_write_transaction t);
  // extern function      send_delayed_expected_transactions_doe_write(kv_write_transaction t);
  // pragma uvmf custom class_item_additional end

  // FUNCTION: new
  function new(string name, uvm_component parent);
     super.new(name,parent);
  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

  // FUNCTION: build_phase
  virtual function void build_phase (uvm_phase phase);

    kv_rst_agent_ae               = new("kv_rst_agent_ae", this);
    kv_hmac_write_agent_ae        = new("kv_hmac_write_agent_ae", this);
    kv_sha512_write_agent_ae      = new("kv_sha512_write_agent_ae", this);
    kv_ecc_write_agent_ae         = new("kv_ecc_write_agent_ae", this);
    kv_doe_write_agent_ae         = new("kv_doe_write_agent_ae", this);
    kv_hmac_key_read_agent_ae     = new("kv_hmac_key_read_agent_ae", this);
    kv_hmac_block_read_agent_ae   = new("kv_hmac_block_read_agent_ae", this);
    kv_sha512_block_read_agent_ae = new("kv_sha512_block_read_agent_ae", this);
    kv_ecc_privkey_read_agent_ae  = new("kv_ecc_privkey_read_agent_ae", this);
    kv_ecc_seed_read_agent_ae     = new("kv_ecc_seed_read_agent_ae", this);
    ahb_slave_0_ae                = new("ahb_slave_0_ae", this);

    kv_hmac_write_sb_ap           = new("kv_hmac_write_sb_ap",this);
    kv_sha512_write_sb_ap         = new("kv_sha512_write_sb_ap",this);
    kv_ecc_write_sb_ap            = new("kv_ecc_write_sb_ap",this);
    kv_doe_write_sb_ap            = new("kv_doe_write_sb_ap",this);

    kv_sb_ap                      = new("kv_sb_ap", this );
    kv_hmac_key_read_sb_ap        = new("kv_hmac_key_read_sb_ap", this );
    kv_hmac_block_read_sb_ap      = new("kv_hmac_block_read_sb_ap", this );
    kv_sha512_block_read_sb_ap    = new("kv_sha512_block_read_sb_ap", this );
    kv_ecc_privkey_read_sb_ap     = new("kv_ecc_privkey_read_sb_ap", this );
    kv_ecc_seed_read_sb_ap        = new("kv_ecc_seed_read_sb_ap", this );
    kv_sb_ahb_ap                  = new("kv_sb_ahb_ap", this);

  // pragma uvmf custom build_phase begin
    p_kv_rm = configuration.kv_rm;

    //Write maps
    p_kv_hmac_write_map   = p_kv_rm.get_map_by_name("kv_hmac_write_map");
    p_kv_sha512_write_map = p_kv_rm.get_map_by_name("kv_sha512_write_map");
    p_kv_ecc_write_map    = p_kv_rm.get_map_by_name("kv_ecc_write_map");
    p_kv_doe_write_map    = p_kv_rm.get_map_by_name("kv_doe_write_map");

    //AHB map
    p_kv_AHB_map = p_kv_rm.get_map_by_name("kv_AHB_map");

    //Read maps
    p_kv_hmac_key_read_map      = p_kv_rm.get_map_by_name("kv_hmac_key_read_map");
    p_kv_hmac_block_read_map    = p_kv_rm.get_map_by_name("kv_hmac_block_read_map");
    p_kv_sha512_block_read_map  = p_kv_rm.get_map_by_name("kv_sha512_block_read_map");
    p_kv_ecc_privkey_read_map   = p_kv_rm.get_map_by_name("kv_ecc_privkey_read_map");
    p_kv_ecc_seed_read_map      = p_kv_rm.get_map_by_name("kv_ecc_seed_read_map");

    //Init last dword array
    for(int entry = 0; entry < KV_NUM_KEYS; entry++) begin
      last_dword_written[entry] = 'h0;
    end

  // pragma uvmf custom build_phase end
  endfunction

  task run_phase (uvm_phase phase);
    fork
      poll_and_run_delay_jobs();
    join_none
    super.run_phase(phase);
  endtask

  // FUNCTION: write_kv_rst_agent_ae
  // Transactions received through kv_rst_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_rst_agent_ae(kv_rst_transaction t);
    // pragma uvmf custom kv_rst_agent_ae_predictor begin
    int entry, offset;
    uvm_reg kv_reg;
    uvm_reg_data_t kv_reg_data;

    kv_rst_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_rst_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");

    clear_secrets_reg = p_kv_rm.get_reg_by_name("CLEAR_SECRETS");
    clear_secrets_data = clear_secrets_reg.get_mirrored_value();
    
    if (!t.set_pwrgood) begin
      kv_sb_ap_output_transaction.read_entry = 'h0;
      kv_sb_ap_output_transaction.read_offset = 'h0;
      kv_sb_ap_output_transaction.error = 'h0;
      kv_sb_ap_output_transaction.last = 'h0;
      kv_sb_ap_output_transaction.read_data = 'h0;
      p_kv_rm.reset(); //all regs cleared on hard rst
      for(entry = 0; entry < KV_NUM_KEYS; entry++) begin
        last_dword_written[entry] = 'h0; //Clear last dword on hard rst
      end
      key_ctrl_lock_wr = 'h0;
      key_ctrl_lock_use = 'h0;
    end
    else if (t.debug_mode | t.scan_mode) begin
      //Set val_reg to 1 for use in reg predictor
      p_kv_rm.val_reg.debug_mode_unlocked.set(1'b1);
      p_kv_rm.val_reg.cptra_in_debug_scan_mode.set(1'b1);
      
      `uvm_info("PRED", "Clear_secrets reg is set in debug/scan mode. Flushing KV", UVM_MEDIUM)
      if (clear_secrets_data[p_kv_rm.kv_reg_rm.CLEAR_SECRETS.sel_debug_value.get_lsb_pos()] == 'h1) begin
        for(entry = 0; entry < KV_NUM_KEYS; entry++) begin
          //Debug mode should flush all regs inspite of locks
          for(offset = 0; offset < KV_NUM_DWORDS; offset++) begin
            p_kv_rm.kv_reg_rm.KEY_ENTRY[entry][offset].predict(CLP_DEBUG_MODE_KV_1);
            p_kv_rm.kv_reg_rm.KEY_ENTRY[entry][offset].set(CLP_DEBUG_MODE_KV_1);
          end
        end
      end
      else begin
        for(entry = 0; entry < KV_NUM_KEYS; entry++) begin
          for(offset = 0; offset < KV_NUM_DWORDS; offset++) begin
            p_kv_rm.kv_reg_rm.KEY_ENTRY[entry][offset].predict(CLP_DEBUG_MODE_KV_0);
            p_kv_rm.kv_reg_rm.KEY_ENTRY[entry][offset].set(CLP_DEBUG_MODE_KV_0);
          end
        end
      end
    end
    else if(t.assert_rst) begin
      //Reset clear_secrets on warm reset
      clear_secrets_reg.reset();
      kv_sb_ap_output_transaction.read_entry = 'h0;
      kv_sb_ap_output_transaction.read_offset = 'h0;
      kv_sb_ap_output_transaction.error = 'h0;
      kv_sb_ap_output_transaction.last = 'h0;
      kv_sb_ap_output_transaction.read_data = 'h0;
    end
    
    //If warm rst or core rst, reset locks
    if(t.set_pwrgood && (t.assert_rst || t.assert_core_rst)) begin
      for(entry = 0; entry < KV_NUM_KEYS; entry++) begin
        kv_reg = p_kv_rm.get_reg_by_name($sformatf("KEY_CTRL[%0d]",entry));
        kv_reg_data = kv_reg.get_mirrored_value();
        
        //Keep dest field as is and reset others
        kv_reg_data = {kv_reg_data[31:9],9'h0};
        
        p_kv_rm.kv_reg_rm.KEY_CTRL[entry].predict(kv_reg_data);
        p_kv_rm.kv_reg_rm.KEY_CTRL[entry].set(kv_reg_data);

        kv_reg = p_kv_rm.get_reg_by_name($sformatf("KEY_CTRL[%0d]",entry));
        kv_reg_data = kv_reg.get_mirrored_value();
      end
      key_ctrl_lock_wr = 'h0;
      key_ctrl_lock_use = 'h0;
    end

    //If debug mode was unlocked, set a val register to let reg predictor know
    if (!t.debug_mode) begin
      p_kv_rm.val_reg.debug_mode_unlocked.set(1'b0);
      //TODO: resetting debug_scan_mode needed?
      if (!t.scan_mode) begin
        p_kv_rm.val_reg.cptra_in_debug_scan_mode.set(1'b0);
      end
    end
 
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
    kv_sb_ap_output_transaction_write = kv_sb_ap_output_transaction_write_t::type_id::create("kv_sb_ap_output_transaction_write");
    populate_expected_kv_write_txn(kv_sb_ap_output_transaction_write, t);
    // this.write_entry_pending = 1'b1;
    // send_hmac_write_txn = 1'b1;

    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_hmac_write_sb_ap.write(kv_sb_ap_output_transaction_write);
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
    kv_sb_ap_output_transaction_write = kv_sb_ap_output_transaction_write_t::type_id::create("kv_sb_ap_output_transaction_write");
    populate_expected_kv_write_txn(kv_sb_ap_output_transaction_write, t);

    // //  UVMF_CHANGE_ME: Implement predictor model here.  
    // `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    // `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The kv_predictor::write_kv_sha512_write_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    // `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sha512_write_sb_ap.write(kv_sb_ap_output_transaction_write);
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
    kv_sb_ap_output_transaction_write = kv_sb_ap_output_transaction_write_t::type_id::create("kv_sb_ap_output_transaction_write");
    populate_expected_kv_write_txn(kv_sb_ap_output_transaction_write, t);

    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_ecc_write_sb_ap.write(kv_sb_ap_output_transaction_write);
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
    kv_sb_ap_output_transaction_write = kv_sb_ap_output_transaction_write_t::type_id::create("kv_sb_ap_output_transaction_write");
    populate_expected_kv_write_txn(kv_sb_ap_output_transaction_write, t);

    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_doe_write_sb_ap.write(kv_sb_ap_output_transaction_write);
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
    client = "hmac_key_read";
    populate_expected_kv_read_txn(kv_sb_ap_output_transaction, t, client);

 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    //kv_sb_ap.write(kv_sb_ap_output_transaction);
    kv_hmac_key_read_sb_ap.write(kv_sb_ap_output_transaction);
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
    client = "hmac_block_read";
    populate_expected_kv_read_txn(kv_sb_ap_output_transaction, t, client);
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_hmac_block_read_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_hmac_block_read_agent_ae_predictor end
  endfunction

  // FUNCTION: write_kv_sha512_block_read_agent_ae
  // Transactions received through kv_sha512_block_read_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_sha512_block_read_agent_ae(kv_read_transaction t);
    // pragma uvmf custom kv_sha512_block_read_agent_ae_predictor begin
    kv_sha512_block_read_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_sha512_block_read_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    client = "sha512_block_read";
    populate_expected_kv_read_txn(kv_sb_ap_output_transaction, t, client);
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sha512_block_read_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_sha512_block_read_agent_ae_predictor end
  endfunction

  // FUNCTION: write_kv_ecc_privkey_read_agent_ae
  // Transactions received through kv_ecc_privkey_read_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_kv_ecc_privkey_read_agent_ae(kv_read_transaction t);
    // pragma uvmf custom kv_ecc_privkey_read_agent_ae_predictor begin
    kv_ecc_privkey_read_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through kv_ecc_privkey_read_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ap_output_transaction = kv_sb_ap_output_transaction_t::type_id::create("kv_sb_ap_output_transaction");
    client = "ecc_privkey_read";
    populate_expected_kv_read_txn(kv_sb_ap_output_transaction, t, client);
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_ecc_privkey_read_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_ecc_privkey_read_agent_ae_predictor end
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
    
    client = "ecc_seed_read";
    populate_expected_kv_read_txn(kv_sb_ap_output_transaction, t, client);

    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_ecc_seed_read_sb_ap.write(kv_sb_ap_output_transaction);
    // pragma uvmf custom kv_ecc_seed_read_agent_ae_predictor end
  endfunction


  // FUNCTION: write_ahb_slave_0_ae
  // Transactions received through ahb_slave_0_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_ahb_slave_0_ae(mvc_sequence_item_base t);
    // pragma uvmf custom ahb_slave_0_ae_predictor begin
    ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_txn;
    uvm_reg kv_reg;
    uvm_reg_data_t kv_reg_data;
    int entry, offset;
    uvm_status_e sts;
    string reg_name;
    reg [KV_DATA_W-1:0] data_active;
    reg [ahb_lite_slave_0_params::AHB_WDATA_WIDTH-1:0] address_aligned;
    uvm_reg val_ctrl, val_reg, val_ctrl_derived;
    uvm_reg_data_t val_ctrl_data, val_reg_data;

    this.set_val_ctrl_derived = 'b0;
    ahb_slave_0_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through ahb_slave_0_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    kv_sb_ahb_ap_output_transaction = kv_sb_ahb_ap_output_transaction_t::type_id::create("kv_sb_ahb_ap_output_transaction");
    $cast(ahb_txn, t);

    //Convert data from AHB to txn
    address_aligned = ahb_txn.address & ~(KV_DATA_W/8 - 1);
    data_active = KV_DATA_W'(ahb_txn.data[0] >> (8*(address_aligned % (ahb_lite_slave_0_params::AHB_WDATA_WIDTH/8))));

    //Read val reg to determine if we're in debug mode
    val_reg = p_kv_rm.get_reg_by_name("val_reg");
    val_reg_data = val_reg.get();
    
    if(ahb_txn.RnW == AHB_WRITE) begin
      //Copy txn and modify required fields later
      kv_sb_ahb_ap_output_transaction.copy(ahb_txn);

      //Only allow clear_secrets during debug mode
      if ((ahb_txn.address == `KV_REG_CLEAR_SECRETS) ) begin
        //Update val register with CLEAR_SECRETS wr_debug_values field
        p_kv_rm.val_reg.clear_secrets_bit.set(data_active[p_kv_rm.kv_reg_rm.CLEAR_SECRETS.wr_debug_values.get_lsb_pos()]);

        if (val_reg_data[p_kv_rm.val_reg.cptra_in_debug_scan_mode.get_lsb_pos()]) begin //[2]) begin
          //Only allow clear operation if in debug mode
          //if (data_active[1:0] == 'h1) begin
          if (data_active [p_kv_rm.kv_reg_rm.CLEAR_SECRETS.wr_debug_values.get_lsb_pos()] && !data_active[p_kv_rm.kv_reg_rm.CLEAR_SECRETS.sel_debug_value.get_lsb_pos()]) begin
            `uvm_info("PRED", "Clear_secrets reg is set in debug/scan mode. Flushing KV with DEBUG0 values", UVM_MEDIUM)
            for(entry = 0; entry < KV_NUM_KEYS; entry++) begin
              //Read locks before clearing - do not clear if locked
              kv_reg = p_kv_rm.get_reg_by_name($sformatf("KEY_CTRL[%0d]",entry));
              kv_reg_data = kv_reg.get_mirrored_value();
              if(kv_reg_data[1:0] == 2'b00) begin
                for(offset = 0; offset < KV_NUM_DWORDS; offset++) begin              
                  p_kv_rm.kv_reg_rm.KEY_ENTRY[entry][offset].predict(CLP_DEBUG_MODE_KV_0);
                  p_kv_rm.kv_reg_rm.KEY_ENTRY[entry][offset].set(CLP_DEBUG_MODE_KV_0);
                end
              end
            end
          end
          //else if(data_active[1:0] == 'h3) begin
          else if (data_active [p_kv_rm.kv_reg_rm.CLEAR_SECRETS.wr_debug_values.get_lsb_pos()] && data_active[p_kv_rm.kv_reg_rm.CLEAR_SECRETS.sel_debug_value.get_lsb_pos()]) begin
            `uvm_info("PRED", "Clear_secrets reg is set in debug/scan mode. Flushing KV with DEBUG1 values", UVM_MEDIUM)
            for(entry = 0; entry < KV_NUM_KEYS; entry++) begin
              //Read locks before clearing
              kv_reg = p_kv_rm.get_reg_by_name($sformatf("KEY_CTRL[%0d]",entry));
              kv_reg_data = kv_reg.get_mirrored_value();
              if(kv_reg_data[1:0] == 2'b00) begin
                for(offset = 0; offset < KV_NUM_DWORDS; offset++) begin
                  p_kv_rm.kv_reg_rm.KEY_ENTRY[entry][offset].predict(CLP_DEBUG_MODE_KV_1);
                  p_kv_rm.kv_reg_rm.KEY_ENTRY[entry][offset].set(CLP_DEBUG_MODE_KV_1);
                end
              end
            end
          end
        end
      end
      else if ((ahb_txn.address >= `KV_REG_KEY_CTRL_0) && (ahb_txn.address < `KV_REG_KEY_ENTRY_0_0)) begin //KEY CTRL lock_wr or lock_use being set
        kv_reg = p_kv_AHB_map.get_reg_by_offset(ahb_txn.address);
        reg_name = kv_reg.get_full_name();
        kv_reg_data = kv_reg.get_mirrored_value();

        {offset, entry} = convert_addr_to_kv(ahb_txn.address);

        //If clear is set and lock_wr/use is 0, set the val_ctrl [1] to let kv_reg_predictor know
        val_ctrl = p_kv_rm.get_reg_by_name("val_ctrl");
        val_ctrl_data = val_ctrl.get();

        //Once set, keep lock_wr set until a reset is issued. AHB txn with lock_wr = 0 should not have any effect on the reg
        if (data_active[p_kv_rm.kv_reg_rm.KEY_CTRL[entry].lock_wr.get_lsb_pos()]) begin
          key_ctrl_lock_wr[entry] = 'b1;
        end

        //Once set, keep lock_use set until a reset is issued. AHB txn with lock_use = 0 should not have any effect on the reg
        if (data_active[p_kv_rm.kv_reg_rm.KEY_CTRL[entry].lock_use.get_lsb_pos()]) begin
          key_ctrl_lock_use[entry] = 'b1;
        end

        // if(data_active[p_kv_rm.kv_reg_rm.KEY_CTRL[entry].clear.get_lsb_pos()] && !kv_reg_data[p_kv_rm.kv_reg_rm.KEY_CTRL[entry].lock_wr.get_lsb_pos()] && !kv_reg_data[p_kv_rm.kv_reg_rm.KEY_CTRL[entry].lock_use.get_lsb_pos()] && !val_reg_data[p_kv_rm.val_reg.cptra_in_debug_scan_mode.get_lsb_pos()]) begin
        if (data_active[p_kv_rm.kv_reg_rm.KEY_CTRL[entry].clear.get_lsb_pos()] && !key_ctrl_lock_wr[entry] && !key_ctrl_lock_use[entry] && !val_reg_data[p_kv_rm.val_reg.cptra_in_debug_scan_mode.get_lsb_pos()]) begin
          val_ctrl_data[entry] = 'b1; //In design, clear is a single pulse reg. This val_ctrl[*] will be reset in kv_reg_predictor
          // for (int i = 0; i < KV_NUM_KEYS; i++) begin
            this.val_ctrl_derived_data[entry] = 'b1;
            last_dword_written[entry] = 'h0; //clear last dword of that entry
            // this.val_ctrl_derived_data[i] = (i == entry);
          // end
          // this.set_val_ctrl_derived = 'b1;
          //p_kv_rm.kv_reg_rm.kv_val_ctrl.predict(val_ctrl_data);
          p_kv_rm.val_ctrl.set(val_ctrl_data);

          //`uvm_info("PRED", "Setting clear field of val_ctrl_derived register", UVM_MEDIUM)
          // //configuration.kv_hmac_write_agent_config.wait_for_num_clocks(1);
          //p_kv_rm.val_ctrl_derived.set(val_ctrl_derived_data);
          //Clear the entry that is being accessed
          for(offset = 0; offset < KV_NUM_DWORDS; offset++) begin
            p_kv_rm.kv_reg_rm.KEY_ENTRY[entry][offset].predict('h0);
            p_kv_rm.kv_reg_rm.KEY_ENTRY[entry][offset].set('h0);
          end
        end
        //Reset all bits of val_ctrl_derived except current entry irrespective of locks
        this.set_val_ctrl_derived = 'b1;
        for (int i = 0; i < KV_NUM_KEYS; i++) begin
          if (i != entry)
            this.val_ctrl_derived_data[i] = 0;
        end
      end
    end
    else begin
      if ((ahb_txn.address >= `KV_REG_KEY_ENTRY_0_0) && (ahb_txn.address < `KV_REG_CLEAR_SECRETS)) //AHB accesses to KEY ENTRY are not allowed
      begin
        kv_sb_ahb_ap_output_transaction.copy(ahb_txn);
        kv_sb_ahb_ap_output_transaction.data[0] = 'h0;
      end
      else begin
        kv_reg = p_kv_AHB_map.get_reg_by_offset(ahb_txn.address);
        kv_reg_data = kv_reg.get_mirrored_value();
        kv_sb_ahb_ap_output_transaction.copy(ahb_txn);
        kv_sb_ahb_ap_output_transaction.data[0] = kv_reg_data;
      end
    end
 
    // Code for sending output transaction out through kv_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    kv_sb_ahb_ap.write(kv_sb_ahb_ap_output_transaction);
    // pragma uvmf custom ahb_slave_0_ae_predictor end
  endfunction


endclass 

// pragma uvmf custom external begin
  function void kv_predictor::populate_expected_kv_read_txn (ref kv_sb_ap_output_transaction_t t_expected, kv_read_transaction t_received, string client);

    uvm_reg kv_reg;
    uvm_reg_data_t kv_reg_data;
    uvm_reg val_ctrl, val_ctrl_derived;
    uvm_reg_data_t val_ctrl_data, val_ctrl_derived_data;
    logic lock_use;
    logic [KV_NUM_READ-1:0] dest_valid;
    logic client_dest_valid;

    val_ctrl = p_kv_rm.get_reg_by_name("val_ctrl");
    val_ctrl_data = val_ctrl.get();

    val_ctrl_derived = p_kv_rm.get_reg_by_name("val_ctrl_derived");
    val_ctrl_derived_data = val_ctrl_derived.get();

    kv_reg = p_kv_rm.get_reg_by_name($sformatf("KEY_CTRL[%0d]",t_received.read_entry));
    kv_reg_data = kv_reg.get_mirrored_value();
    kv_reg = p_kv_rm.get_reg_by_name($sformatf("KEY_ENTRY[%0d][%0d]",t_received.read_entry,t_received.read_offset));

    lock_use = kv_reg_data[p_kv_rm.kv_reg_rm.KEY_CTRL[t_received.read_entry].lock_use.get_lsb_pos()];
    dest_valid = kv_reg_data[13:9]; //[16:14] are rsvd
    // dest_valid = kv_reg_data[p_kv_rm.kv_reg_rm.KEY_CTRL[entry].dest_valid.get_lsb_pos()];
    
    case(client) inside

      "hmac_key_read"     : client_dest_valid = dest_valid[0];
      "hmac_block_read"   : client_dest_valid = dest_valid[1];
      "sha512_block_read" : client_dest_valid = dest_valid[2];
      "ecc_privkey_read"  : client_dest_valid = dest_valid[3];
      "ecc_seed_read"     : client_dest_valid = dest_valid[4];
      default: begin
        client_dest_valid = 0;
      end

    endcase

    //Scenario: When KEY_CTRL.clear is set, following things happen:
    //1. KEY_ENTRY is cleared
    //2. last_dword is cleared
    //3. dest_valid is cleared
    //kv_predictor takes care of #1. #2 and #3 should be done is custom AHB reg predictor which we don't have
    //As a workaround, setting a val_ctrl reg when clear happens. Until a write occurs on that entry, this bit will remain set
    //During every read, we check val_ctrl[entry] bit. If 1, return 0s, resp.err = 1 and last dword = 0 to mimic design
    if (lock_use || !client_dest_valid || val_ctrl_data[t_received.read_entry] || val_ctrl_derived_data[t_received.read_entry]) begin
      t_expected.read_data = 'h0;
      t_expected.error = 'b1;
    end
    else begin
      kv_reg_data = kv_reg.get_mirrored_value();
      t_expected.read_data = KV_DATA_W'(kv_reg_data); //kv_reg_data[31:0]; //Data from KEY entry
      t_expected.error = 'b0;
    end

    // if (val_ctrl_data[t_received.read_entry]) begin
    // if (val_ctrl_derived_data[t_received.read_entry]) begin
    //   `uvm_info("KNU_DBG","Resetting last_dword because val_ctrl_data is set!", UVM_FULL)
    //   last_dword_written[t_received.read_entry] = 'h0;
    // end

    t_expected.last = (last_dword_written[t_received.read_entry] == t_received.read_offset); 
    t_expected.read_entry = t_received.read_entry;
    t_expected.read_offset = t_received.read_offset;
  endfunction

  function void kv_predictor::populate_expected_kv_write_txn (ref kv_sb_ap_output_transaction_write_t t_expected, kv_write_transaction t_received);
    uvm_reg kv_reg, val_ctrl_derived, val_ctrl;
    uvm_reg_data_t kv_reg_data, val_ctrl_derived_data, val_ctrl_data;
    logic lock_use;
    logic lock_wr;
    logic clear;

    //TODO: This logic takes advantage of the fact that reg model writes happen without a 1 clk delay.
    //So when predictor reads the CTRL reg, the lock info is already up to date
    //If the reg model is modified to account for the 1 clk delay, this logic might need to account for that as well
    kv_reg = p_kv_rm.get_reg_by_name($sformatf("KEY_CTRL[%0d]",t_received.write_entry));
    kv_reg_data = kv_reg.get_mirrored_value();    

    // lock_wr = kv_reg_data[p_kv_rm.kv_reg_rm.KEY_CTRL[t_received.write_entry].lock_wr.get_lsb_pos()];
    // lock_use = kv_reg_data[p_kv_rm.kv_reg_rm.KEY_CTRL[t_received.write_entry].lock_use.get_lsb_pos()];
    lock_wr = key_ctrl_lock_wr[t_received.write_entry];
    lock_use = key_ctrl_lock_use[t_received.write_entry];

    val_ctrl_derived = p_kv_rm.get_reg_by_name("val_ctrl_derived");
    val_ctrl_derived_data = val_ctrl_derived.get();

    val_ctrl = p_kv_rm.get_reg_by_name("val_ctrl");
    val_ctrl_data = val_ctrl.get();

    //Copy received txn
    // t_expected = t_received;
    t_expected.write_en         = t_received.write_en;
    t_expected.write_entry      = t_received.write_entry;
    t_expected.write_offset     = t_received.write_offset;
    t_expected.write_data       = t_received.write_data;
    t_expected.write_dest_valid = t_received.write_dest_valid;

    //Error should be set when writing to locked regs //TODO: error when entry is being cleared during write
    if (t_received.write_en) begin
      if(lock_wr || lock_use) begin
        t_expected.error = 1'b1;
        `uvm_info("PRED", "Trying to write to a locked reg", UVM_MEDIUM)
      end
      else begin
        key_entry_ctrl_we[t_received.write_entry] = 1'b1;
        if (/*this.write_in_progress[t_received.write_entry] &&*/ val_ctrl_derived_data[t_received.write_entry]) begin
          t_expected.error = 1'b1;
          `uvm_info("PRED","Attempts to clear a reg while write is in progress results in an err", UVM_MEDIUM)
        end
        else begin
          t_expected.error = 1'b0;
          //Keep track of last dword written
          last_dword_written[t_received.write_entry] = t_received.write_offset;
        end
      end
    end
    else begin
      t_expected.error = 1'b0;
      //Reset all bits of val_ctrl_derived except current entry irrespective of locks
      this.set_val_ctrl_derived = 'b1;
      for (int i = 0; i < KV_NUM_KEYS; i++) begin
          this.val_ctrl_derived_data[i] = 0;
          key_entry_ctrl_we[i] = 1'b0;
      end

    end

      
  endfunction

  // function void kv_predictor::send_delayed_expected_transactions_hmac_write(kv_write_transaction t);
  //   bit send_hmac_write_txn = 0;

  //   kv_sb_ap_output_transaction_write = kv_sb_ap_output_transaction_write_t::type_id::create("kv_sb_ap_output_transaction_write");

  //   if (this.write_entry_pending) begin
  //     `uvm_info("PRED_DLY", "Delay job to update KEY_ENTRY value", UVM_HIGH)
  //     this.write_entry_pending = 1'b0;
  //   end

  //   //-------------------------------------
  //   //Send expected txns to SCBD
  //   //-------------------------------------
  //   if (send_hmac_write_txn) begin
  //     populate_expected_kv_write_txn(kv_sb_ap_output_transaction_write, t);
  //     kv_hmac_write_sb_ap.write(kv_sb_ap_output_transaction_write);
  //     `uvm_info("PRED_DLY", "Transaction submitted through kv_hmac_write_sb_ap", UVM_MEDIUM)
  //     send_hmac_write_txn = 1'b0;
  //   end

  // endfunction

  // task kv_predictor::poll_and_run_delay_jobs();
  //   forever begin
  //     while (p_kv_rm.delay_jobs.size() > 0) begin
  //       fork
  //         kv_reg_delay_job job = p_kv_rm.delay_jobs.pop_front();
  //         //TODO: add reset check
  //         int idx[$];
  //         time end_time;
  //         this.running_dly_jobs.push_back(process::self()); // This tracks all the delay_jobs that are pending so they can be clobbered on rst
  //         `uvm_info("PRED_DLY", $sformatf("Doing delay of %0d cycles before running delay job with signature: %s", job.get_delay_cycles(), job.get_name()), UVM_HIGH)
  //         end_time = $time + 10*job.get_delay_cycles();
  //         job_end_count[end_time] += 1;
  //         //Delay jobs have 1 cycle inherent delay
  //         if (job.get_delay_cycles()) configuration.kv_hmac_write_agent_config.wait_for_num_clocks(job.get_delay_cycles());
  //         uvm_wait_for_nba_region();
  //         idx = this.running_dly_jobs.find_first_index(pr) with (pr == process::self());
  //         this.running_dly_jobs.delete(idx.pop_front());
  //         job.do_job();
  //         job_end_count[end_time] -= 1;

  //         if (job_end_count[end_time] == 0) begin
  //           job_end_count.delete(end_time);
  //           // send_delayed_expected_transactions_hmac_write(t);
  //         end
  //         //end TODO: add reset check
  //       join_none
  //     end
  //     configuration.kv_hmac_write_agent_config.wait_for_num_clocks(1);
  //   end
  // endtask

  task kv_predictor::poll_and_run_delay_jobs();
    forever begin
      if (this.set_val_ctrl_derived) begin
        // fork
          //Delay by 2 clks to match the clear txn reaching predictor by then 
          configuration.kv_hmac_write_agent_config.wait_for_num_clocks(2); //2
          `uvm_info("PRED", $sformatf("Setting clear field of val_ctrl_derived register from %b to %b",p_kv_rm.val_ctrl_derived.get(), this.val_ctrl_derived_data), UVM_FULL)
          p_kv_rm.val_ctrl_derived.set(this.val_ctrl_derived_data);
          this.set_val_ctrl_derived = 'b0;
        // join_none
      end
      else begin
        for (int i = 0; i < KV_NUM_KEYS; i++) begin
          if (!key_entry_ctrl_we[i]) begin
            this.val_ctrl_derived_data[i] = 'b0; //reset clear bit if there's no write_en for it
          end
          this.set_val_ctrl_derived = 'b1; //update in next clk
        end
      end
      configuration.kv_hmac_write_agent_config.wait_for_num_clocks(1);
    end
  endtask
// pragma uvmf custom external end

