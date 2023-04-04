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
// DESCRIPTION: This analysis component contains analysis_exports for receiving
//   data and analysis_ports for sending data.
// 
//   This analysis component has the following analysis_exports that receive the 
//   listed transaction type.
//   
//   expected_analysis_export receives transactions of type  kv_read_transaction  
//   actual_analysis_export receives transactions of type  kv_read_transaction  
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//


class kv_scoreboard #(
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  // Factory registration of this class
  `uvm_component_param_utils( kv_scoreboard #(
                              CONFIG_T,
                              BASE_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;

  
  // Instantiate the analysis exports
  uvm_analysis_imp_expected_hmac_write_analysis_export #(kv_write_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) expected_hmac_write_analysis_export;
  uvm_analysis_imp_actual_hmac_write_analysis_export #(kv_write_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) actual_hmac_write_analysis_export;
  uvm_analysis_imp_expected_sha512_write_analysis_export #(kv_write_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) expected_sha512_write_analysis_export;
  uvm_analysis_imp_actual_sha512_write_analysis_export #(kv_write_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) actual_sha512_write_analysis_export;
  uvm_analysis_imp_expected_ecc_write_analysis_export #(kv_write_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) expected_ecc_write_analysis_export;
  uvm_analysis_imp_actual_ecc_write_analysis_export #(kv_write_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) actual_ecc_write_analysis_export;
  uvm_analysis_imp_expected_doe_write_analysis_export #(kv_write_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) expected_doe_write_analysis_export;
  uvm_analysis_imp_actual_doe_write_analysis_export #(kv_write_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) actual_doe_write_analysis_export;

  uvm_analysis_imp_expected_hmac_key_read_analysis_export #(kv_read_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) expected_hmac_key_read_analysis_export;
  uvm_analysis_imp_actual_hmac_key_read_analysis_export #(kv_read_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) actual_hmac_key_read_analysis_export;

  uvm_analysis_imp_expected_hmac_block_read_analysis_export #(kv_read_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) expected_hmac_block_read_analysis_export;
  uvm_analysis_imp_actual_hmac_block_read_analysis_export #(kv_read_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) actual_hmac_block_read_analysis_export;

  uvm_analysis_imp_expected_sha512_block_read_analysis_export #(kv_read_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) expected_sha512_block_read_analysis_export;
  uvm_analysis_imp_actual_sha512_block_read_analysis_export #(kv_read_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) actual_sha512_block_read_analysis_export;

  uvm_analysis_imp_expected_ecc_privkey_read_analysis_export #(kv_read_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) expected_ecc_privkey_read_analysis_export;
  uvm_analysis_imp_actual_ecc_privkey_read_analysis_export #(kv_read_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) actual_ecc_privkey_read_analysis_export;

  uvm_analysis_imp_expected_ecc_seed_read_analysis_export #(kv_read_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) expected_ecc_seed_read_analysis_export;
  uvm_analysis_imp_actual_ecc_seed_read_analysis_export #(kv_read_transaction, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
  ) actual_ecc_seed_read_analysis_export;


 
  // Instantiate QVIP analysis exports
  uvm_analysis_imp_expected_ahb_analysis_export #(mvc_sequence_item_base, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) expected_ahb_analysis_export;
  uvm_analysis_imp_actual_ahb_analysis_export #(mvc_sequence_item_base, kv_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) actual_ahb_analysis_export;


  // pragma uvmf custom class_item_additional begin

    //Associative array of expected transactions keyed with the integer accessed using the transactions get_key() interface
    kv_write_transaction kv_hmac_write_expected_hash [int unsigned];
    kv_write_transaction kv_sha512_write_expected_hash [int unsigned];
    kv_write_transaction kv_ecc_write_expected_hash [int unsigned];
    kv_write_transaction kv_doe_write_expected_hash [int unsigned];

    kv_read_transaction kv_hmac_key_read_expected_hash [int unsigned]; //FIXME
    kv_read_transaction kv_hmac_block_read_expected_hash [int unsigned]; //FIXME
    kv_read_transaction kv_sha512_block_read_expected_hash [int unsigned]; //FIXME
    kv_read_transaction kv_ecc_privkey_read_expected_hash [int unsigned]; //FIXME
    kv_read_transaction kv_ecc_seed_read_expected_hash [int unsigned]; //FIXME

    //Use queues for AHB txns since there is no get_key() method
    ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                              ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                              ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                              ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                              ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                              ahb_lite_slave_0_params::AHB_RDATA_WIDTH)     ahb_expected_q       [$]; // FIXME

    // Variables used to report transaction matches and mismatches
  int match_count; // FIXME
  int mismatch_count; // FIXME
  int nothing_to_compare_against_count; // FIXME

  // Variables used for report_phase summary output formatting using report_message()
  int report_variables[]; // FIXME
  string report_hdr = "SCOREBOARD_RESULTS: "; // FIXME

  // Variable used to enable end of test scoreboard empty check
  bit end_of_test_empty_check=1; // FIXME
  int transaction_count; // FIXME

  // Variable used to delay run phase completion until scoreboard empty
  bit wait_for_scoreboard_empty; // FIXME
  event entry_received; // FIXME

  extern function void disable_wait_for_scoreboard_empty();
  extern function void enable_wait_for_scoreboard_empty();
  extern virtual task wait_for_scoreboard_drain();
  extern virtual function void phase_ready_to_end( uvm_phase phase );

  // pragma uvmf custom class_item_additional end

  // FUNCTION: new
  function new(string name, uvm_component parent);
     super.new(name,parent);
  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

  // FUNCTION: build_phase
  virtual function void build_phase (uvm_phase phase);

    expected_hmac_write_analysis_export = new("expected_hmac_write_analysis_export", this);
    actual_hmac_write_analysis_export = new("actual_hmac_write_analysis_export", this);

    expected_sha512_write_analysis_export = new("expected_sha512_write_analysis_export", this);
    actual_sha512_write_analysis_export = new("actual_sha512_write_analysis_export", this);

    expected_ecc_write_analysis_export = new("expected_ecc_write_analysis_export", this);
    actual_ecc_write_analysis_export = new("actual_ecc_write_analysis_export", this);

    expected_doe_write_analysis_export = new("expected_doe_write_analysis_export", this);
    actual_doe_write_analysis_export = new("actual_doe_write_analysis_export", this);

    expected_hmac_key_read_analysis_export = new("expected_hmac_key_read_analysis_export", this);
    actual_hmac_key_read_analysis_export = new("actual_hmac_key_read_analysis_export", this);
    
    expected_hmac_block_read_analysis_export = new("expected_hmac_block_read_analysis_export", this);
    actual_hmac_block_read_analysis_export = new("actual_hmac_block_read_analysis_export", this);
    
    expected_sha512_block_read_analysis_export = new("expected_sha512_block_read_analysis_export", this);
    actual_sha512_block_read_analysis_export = new("actual_sha512_block_read_analysis_export", this);
    
    expected_ecc_privkey_read_analysis_export = new("expected_ecc_privkey_read_analysis_export", this);
    actual_ecc_privkey_read_analysis_export = new("actual_ecc_privkey_read_analysis_export", this);
    
    expected_ecc_seed_read_analysis_export = new("expected_ecc_seed_read_analysis_export", this);
    actual_ecc_seed_read_analysis_export = new("actual_ecc_seed_read_analysis_export", this);
    
    expected_ahb_analysis_export = new("expected_ahb_analysis_export", this);
    actual_ahb_analysis_export = new("actual_ahb_analysis_export", this);

  // pragma uvmf custom build_phase begin
  // pragma uvmf custom build_phase end
  endfunction

  // FUNCTION: write_expected_analysis_export
  // Transactions received through expected_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_expected_hmac_write_analysis_export(kv_write_transaction t);
    // pragma uvmf custom expected_analysis_export_scoreboard begin
    `uvm_info("SCBD_KV_WRITE", "Transaction Received through expected_hmac_write_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_WRITE", {"            Data: ",t.convert2string()}, UVM_FULL)

    kv_hmac_write_expected_hash[t.get_key()] = t;
    `uvm_info("SCBD_KV_WRITE", $sformatf("EXPECTED txn is {Write entry: 0x%x}, {Write offset: 0x%x}, {Write Data: 0x%x}, {Write resp err: %h}", t.write_entry,t.write_offset,t.write_data, t.error ), UVM_MEDIUM)
    
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction

  // FUNCTION: write_expected_analysis_export
  // Transactions received through expected_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_expected_sha512_write_analysis_export(kv_write_transaction t);
    // pragma uvmf custom expected_analysis_export_scoreboard begin
    `uvm_info("SCBD_KV_WRITE", "Transaction Received through expected_sha512_write_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_WRITE", {"            Data: ",t.convert2string()}, UVM_FULL)

    kv_sha512_write_expected_hash[t.get_key()] = t;
    `uvm_info("SCBD_KV_WRITE", $sformatf("EXPECTED txn is {Write entry: 0x%x}, {Write offset: 0x%x}, {Write Data: 0x%x}, {Write resp err: %h}", t.write_entry,t.write_offset,t.write_data, t.error ), UVM_MEDIUM)
    
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction

  // FUNCTION: write_expected_analysis_export
  // Transactions received through expected_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_expected_ecc_write_analysis_export(kv_write_transaction t);
    // pragma uvmf custom expected_analysis_export_scoreboard begin
    `uvm_info("SCBD_KV_WRITE", "Transaction Received through expected_ecc_write_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_WRITE", {"            Data: ",t.convert2string()}, UVM_FULL)

    kv_ecc_write_expected_hash[t.get_key()] = t;
    `uvm_info("SCBD_KV_WRITE", $sformatf("EXPECTED txn is {Write entry: 0x%x}, {Write offset: 0x%x}, {Write Data: 0x%x}, {Write resp err: %h}", t.write_entry,t.write_offset,t.write_data, t.error ), UVM_MEDIUM)
    
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction

  // FUNCTION: write_expected_analysis_export
  // Transactions received through expected_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_expected_doe_write_analysis_export(kv_write_transaction t);
    // pragma uvmf custom expected_analysis_export_scoreboard begin
    `uvm_info("SCBD_KV_WRITE", "Transaction Received through expected_doe_write_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_WRITE", {"            Data: ",t.convert2string()}, UVM_FULL)

    kv_doe_write_expected_hash[t.get_key()] = t;
    `uvm_info("SCBD_KV_WRITE", $sformatf("EXPECTED txn is {Write entry: 0x%x}, {Write offset: 0x%x}, {Write Data: 0x%x}, {Write resp err: %h}", t.write_entry,t.write_offset,t.write_data, t.error ), UVM_MEDIUM)
    
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction


  // FUNCTION: write_actual_analysis_export
  // Transactions received through actual_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_actual_hmac_write_analysis_export(kv_write_transaction t);
    // pragma uvmf custom actual_analysis_export_scoreboard begin
    kv_write_transaction t_expected;
    bit txn_eq;

    `uvm_info("SCBD_KV_WRITE", "Transaction Received through actual_hmac_write_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_WRITE", {"            Data: ",t.convert2string()}, UVM_FULL)

    if (kv_hmac_write_expected_hash.exists(t.get_key())) begin
      t_expected = kv_hmac_write_expected_hash[t.get_key()];
      txn_eq = t.compare(t_expected);

      if(txn_eq) `uvm_info("SCBD_KV_WRITE", $sformatf("Actual txn with {Write entry: 0x%x}, {Write offset: 0x%x}, {Write Data: 0x%x}, {Write resp err: %h} matches expected!", t.write_entry,t.write_offset,t.write_data,t.error ), UVM_HIGH)
      else       `uvm_error("SCBD_KV_WRITE", $sformatf("Actual txn with {Write entry: 0x%x}, {Write offset: 0x%x}, {Write Data: 0x%x}, {Write resp err: %h} does not match expected txn with {Write entry: 0x%x}, {Write offset: 0x%x}, {Write data: 0x%x}, {Write resp err: %h}", t.write_entry,t.write_offset,t.write_data,t.error, t_expected.write_entry,t_expected.write_offset,t_expected.write_data,t_expected.error ))

      if(t.error) `uvm_info("SCBD_KV_WRITE", "Trying to write to a locked reg", UVM_MEDIUM);
    end
    else begin
      `uvm_error("SCBD_KV_WRITE", "Received unmatched write transaction. Cannot find corresponding expected txn!");
    end
    
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction

  // FUNCTION: write_actual_analysis_export
  // Transactions received through actual_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_actual_sha512_write_analysis_export(kv_write_transaction t);
    // pragma uvmf custom actual_analysis_export_scoreboard begin
    kv_write_transaction t_expected;
    bit txn_eq;

    `uvm_info("SCBD_KV_WRITE", "Transaction Received through actual_sha512_write_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_WRITE", {"            Data: ",t.convert2string()}, UVM_FULL)

    if (kv_sha512_write_expected_hash.exists(t.get_key())) begin
      t_expected = kv_sha512_write_expected_hash[t.get_key()];
      txn_eq = t.compare(t_expected);

      if(txn_eq) `uvm_info("SCBD_KV_WRITE", $sformatf("Actual txn with {Write entry: 0x%x}, {Write offset: 0x%x}, {Write Data: 0x%x}, {Write resp err: %h} matches expected!", t.write_entry,t.write_offset,t.write_data,t.error ), UVM_HIGH)
      else       `uvm_error("SCBD_KV_WRITE", $sformatf("Actual txn with {Write entry: 0x%x}, {Write offset: 0x%x}, {Write Data: 0x%x}, {Write resp err: %h} does not match expected txn with {Write entry: 0x%x}, {Write offset: 0x%x}, {Write data: 0x%x}, {Write resp err: %h}", t.write_entry,t.write_offset,t.write_data,t.error, t_expected.write_entry,t_expected.write_offset,t_expected.write_data,t_expected.error ))

      if(t.error) `uvm_info("SCBD_KV_WRITE", "Trying to write to a locked reg", UVM_MEDIUM);
    end
    else begin
      `uvm_error("SCBD_KV_WRITE", "Received unmatched write transaction. Cannot find corresponding expected txn!");
    end
    
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction

  // FUNCTION: write_actual_analysis_export
  // Transactions received through actual_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_actual_ecc_write_analysis_export(kv_write_transaction t);
    // pragma uvmf custom actual_analysis_export_scoreboard begin
    kv_write_transaction t_expected;
    bit txn_eq;

    `uvm_info("SCBD_KV_WRITE", "Transaction Received through actual_ecc_write_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_WRITE", {"            Data: ",t.convert2string()}, UVM_FULL)

    if (kv_ecc_write_expected_hash.exists(t.get_key())) begin
      t_expected = kv_ecc_write_expected_hash[t.get_key()];
      txn_eq = t.compare(t_expected);

      if(txn_eq) `uvm_info("SCBD_KV_WRITE", $sformatf("Actual txn with {Write entry: 0x%x}, {Write offset: 0x%x}, {Write Data: 0x%x}, {Write resp err: %h} matches expected!", t.write_entry,t.write_offset,t.write_data,t.error ), UVM_HIGH)
      else       `uvm_error("SCBD_KV_WRITE", $sformatf("Actual txn with {Write entry: 0x%x}, {Write offset: 0x%x}, {Write Data: 0x%x}, {Write resp err: %h} does not match expected txn with {Write entry: 0x%x}, {Write offset: 0x%x}, {Write data: 0x%x}, {Write resp err: %h}", t.write_entry,t.write_offset,t.write_data,t.error, t_expected.write_entry,t_expected.write_offset,t_expected.write_data,t_expected.error ))

      if(t.error) `uvm_info("SCBD_KV_WRITE", "Trying to write to a locked reg", UVM_MEDIUM);
    end
    else begin
      `uvm_error("SCBD_KV_WRITE", "Received unmatched write transaction. Cannot find corresponding expected txn!");
    end
    
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction

  // FUNCTION: write_actual_analysis_export
  // Transactions received through actual_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_actual_doe_write_analysis_export(kv_write_transaction t);
    // pragma uvmf custom actual_analysis_export_scoreboard begin
    kv_write_transaction t_expected;
    bit txn_eq;

    `uvm_info("SCBD_KV_WRITE", "Transaction Received through actual_doe_write_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_WRITE", {"            Data: ",t.convert2string()}, UVM_FULL)

    if (kv_doe_write_expected_hash.exists(t.get_key())) begin
      t_expected = kv_doe_write_expected_hash[t.get_key()];
      txn_eq = t.compare(t_expected);

      if(txn_eq) `uvm_info("SCBD_KV_WRITE", $sformatf("Actual txn with {Write entry: 0x%x}, {Write offset: 0x%x}, {Write Data: 0x%x}, {Write resp err: %h} matches expected!", t.write_entry,t.write_offset,t.write_data,t.error ), UVM_HIGH)
      else       `uvm_error("SCBD_KV_WRITE", $sformatf("Actual txn with {Write entry: 0x%x}, {Write offset: 0x%x}, {Write Data: 0x%x}, {Write resp err: %h} does not match expected txn with {Write entry: 0x%x}, {Write offset: 0x%x}, {Write data: 0x%x}, {Write resp err: %h}", t.write_entry,t.write_offset,t.write_data,t.error, t_expected.write_entry,t_expected.write_offset,t_expected.write_data,t_expected.error ))

      if(t.error) `uvm_info("SCBD_KV_WRITE", "Trying to write to a locked reg", UVM_MEDIUM);
    end
    else begin
      `uvm_error("SCBD_KV_WRITE", "Received unmatched write transaction. Cannot find corresponding expected txn!");
    end
    
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction

  // FUNCTION: write_expected_analysis_export
  // Transactions received through expected_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_expected_hmac_key_read_analysis_export(kv_read_transaction t);
    // pragma uvmf custom expected_analysis_export_scoreboard begin
    `uvm_info("SCBD_KV_READ", "Transaction Received through expected_hmac_key_read_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_READ", {"            Data: ",t.convert2string()}, UVM_FULL)

    kv_hmac_key_read_expected_hash[t.get_key()] = t;
    `uvm_info("SCBD_KV_READ", $sformatf("EXPECTED txn is {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h}", t.read_entry,t.read_offset,t.read_data,t.last, t.error ), UVM_MEDIUM)
    
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction

  // FUNCTION: write_actual_analysis_export
  // Transactions received through actual_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_actual_hmac_key_read_analysis_export(kv_read_transaction t);
    // pragma uvmf custom actual_analysis_export_scoreboard begin
    kv_read_transaction t_expected;
    bit txn_eq;

    `uvm_info("SCBD_KV_READ", "Transaction Received through actual_hmac_key_read_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_READ", {"            Data: ",t.convert2string()}, UVM_FULL)

    if (kv_hmac_key_read_expected_hash.exists(t.get_key())) begin
        t_expected = kv_hmac_key_read_expected_hash[t.get_key()];
        txn_eq = t.compare(t_expected);

        if(txn_eq) `uvm_info("SCBD_KV_READ", $sformatf("Actual txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h} matches expected!", t.read_entry,t.read_offset,t.read_data,t.last,t.error ), UVM_HIGH)
        else       `uvm_error("SCBD_KV_READ", $sformatf("Actual txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h} does not match expected txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h}", t.read_entry,t.read_offset,t.read_data,t.last,t.error, t_expected.read_entry,t_expected.read_offset,t_expected.read_data,t_expected.last,t_expected.error ))

        if(t.error) `uvm_info("SCBD_KV_READ", "Trying to read a locked reg or reg with dest_valid = 0 will return 0s", UVM_MEDIUM);
    end
    else begin
        `uvm_error("SCBD_KV_READ", "Received unmatched read transaction. Cannot find corresponding expected txn!");
    end
 
    // pragma uvmf custom actual_analysis_export_scoreboard end
  endfunction

  //-------------------------------------------------------

  virtual function void write_expected_hmac_block_read_analysis_export(kv_read_transaction t);
    // pragma uvmf custom expected_analysis_export_scoreboard begin
    `uvm_info("SCBD_KV_READ", "Transaction Received through expected_hmac_block_read_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_READ", {"            Data: ",t.convert2string()}, UVM_FULL)

    kv_hmac_block_read_expected_hash[t.get_key()] = t;
    `uvm_info("SCBD_KV_READ", $sformatf("EXPECTED txn is {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h}", t.read_entry,t.read_offset,t.read_data,t.last,t.error ), UVM_MEDIUM)
    
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction

  virtual function void write_actual_hmac_block_read_analysis_export(kv_read_transaction t);
    // pragma uvmf custom actual_analysis_export_scoreboard begin
    kv_read_transaction t_expected;
    bit txn_eq;

    `uvm_info("SCBD_KV_READ", "Transaction Received through actual_hmac_block_read_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_READ", {"            Data: ",t.convert2string()}, UVM_FULL)

    if (kv_hmac_block_read_expected_hash.exists(t.get_key())) begin
        t_expected = kv_hmac_block_read_expected_hash[t.get_key()];
        txn_eq = t.compare(t_expected);

        if(txn_eq) `uvm_info("SCBD_KV_READ", $sformatf("Actual txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h} matches expected!", t.read_entry,t.read_offset,t.read_data,t.last,t.error ), UVM_HIGH)
        else       `uvm_error("SCBD_KV_READ", $sformatf("Actual txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h} does not match expected txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h}", t.read_entry,t.read_offset,t.read_data,t.last,t.error, t_expected.read_entry,t_expected.read_offset,t_expected.read_data,t_expected.last,t_expected.error ))

        if(t.error) `uvm_info("SCBD_KV_READ", "Trying to read a locked reg or reg with dest_valid = 0 will return 0s", UVM_MEDIUM);
    end
    else begin
        `uvm_error("SCBD_KV_READ", "Received unmatched read transaction. Cannot find corresponding expected txn!");
    end
 
    // pragma uvmf custom actual_analysis_export_scoreboard end
  endfunction

  //------------------------------------------------

  virtual function void write_expected_sha512_block_read_analysis_export(kv_read_transaction t);
    // pragma uvmf custom expected_analysis_export_scoreboard begin
    `uvm_info("SCBD_KV_READ", "Transaction Received through expected_sha512_block_read_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_READ", {"            Data: ",t.convert2string()}, UVM_FULL)

    kv_sha512_block_read_expected_hash[t.get_key()] = t;
    `uvm_info("SCBD_KV_READ", $sformatf("EXPECTED txn is {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h}", t.read_entry,t.read_offset,t.read_data,t.last,t.error ), UVM_MEDIUM)
    
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction

  virtual function void write_actual_sha512_block_read_analysis_export(kv_read_transaction t);
    // pragma uvmf custom actual_analysis_export_scoreboard begin
    kv_read_transaction t_expected;
    bit txn_eq;

    `uvm_info("SCBD_KV_READ", "Transaction Received through actual_sha512_block_read_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_READ", {"            Data: ",t.convert2string()}, UVM_FULL)

    if (kv_sha512_block_read_expected_hash.exists(t.get_key())) begin
        t_expected = kv_sha512_block_read_expected_hash[t.get_key()];
        txn_eq = t.compare(t_expected);

        if(txn_eq) `uvm_info("SCBD_KV_READ", $sformatf("Actual txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h} matches expected!", t.read_entry,t.read_offset,t.read_data,t.last,t.error ), UVM_HIGH)
        else       `uvm_error("SCBD_KV_READ", $sformatf("Actual txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h} does not match expected txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h}", t.read_entry,t.read_offset,t.read_data,t.last,t.error, t_expected.read_entry,t_expected.read_offset,t_expected.read_data,t_expected.last, t_expected.error ))

        if(t.error) `uvm_info("SCBD_KV_READ", "Trying to read a locked reg or reg with dest_valid = 0 will return 0s", UVM_MEDIUM);
    end
    else begin
        `uvm_error("SCBD_KV_READ", "Received unmatched read transaction. Cannot find corresponding expected txn!");
    end
 
    // pragma uvmf custom actual_analysis_export_scoreboard end
  endfunction

  //-----------------------------------------------

  virtual function void write_expected_ecc_privkey_read_analysis_export(kv_read_transaction t);
    // pragma uvmf custom expected_analysis_export_scoreboard begin
    `uvm_info("SCBD_KV_READ", "Transaction Received through expected_ecc_privkey_read_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_READ", {"            Data: ",t.convert2string()}, UVM_FULL)

    kv_ecc_privkey_read_expected_hash[t.get_key()] = t;
    `uvm_info("SCBD_KV_READ", $sformatf("EXPECTED txn is {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h}", t.read_entry,t.read_offset,t.read_data,t.last,t.error ), UVM_MEDIUM)
    
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction

  virtual function void write_actual_ecc_privkey_read_analysis_export(kv_read_transaction t);
    // pragma uvmf custom actual_analysis_export_scoreboard begin
    kv_read_transaction t_expected;
    bit txn_eq;

    `uvm_info("SCBD_KV_READ", "Transaction Received through actual_ecc_privkey_read_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_READ", {"            Data: ",t.convert2string()}, UVM_FULL)

    if (kv_ecc_privkey_read_expected_hash.exists(t.get_key())) begin
        t_expected = kv_ecc_privkey_read_expected_hash[t.get_key()];
        txn_eq = t.compare(t_expected);

        if(txn_eq) `uvm_info("SCBD_KV_READ", $sformatf("Actual txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h} matches expected!", t.read_entry,t.read_offset,t.read_data,t.last,t.error ), UVM_HIGH)
        else       `uvm_error("SCBD_KV_READ", $sformatf("Actual txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h} does not match expected txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h}", t.read_entry,t.read_offset,t.read_data,t.last, t.error, t_expected.read_entry,t_expected.read_offset,t_expected.read_data,t_expected.last, t_expected.error ))

        if(t.error) `uvm_info("SCBD_KV_READ", "Trying to read a locked reg or reg with dest_valid = 0 will return 0s", UVM_MEDIUM);
    end
    else begin
        `uvm_error("SCBD_KV_READ", "Received unmatched read transaction. Cannot find corresponding expected txn!");
    end
 
    // pragma uvmf custom actual_analysis_export_scoreboard end
  endfunction

  //-----------------------------------------------

  virtual function void write_expected_ecc_seed_read_analysis_export(kv_read_transaction t);
    // pragma uvmf custom expected_analysis_export_scoreboard begin
    `uvm_info("SCBD_KV_READ", "Transaction Received through expected_ecc_seed_read_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_READ", {"            Data: ",t.convert2string()}, UVM_FULL)

    kv_ecc_seed_read_expected_hash[t.get_key()] = t;
    `uvm_info("SCBD_KV_READ", $sformatf("EXPECTED txn is {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h}", t.read_entry,t.read_offset,t.read_data,t.last,t.error ), UVM_MEDIUM)
    
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction

  virtual function void write_actual_ecc_seed_read_analysis_export(kv_read_transaction t);
    // pragma uvmf custom actual_analysis_export_scoreboard begin
    kv_read_transaction t_expected;
    bit txn_eq;

    `uvm_info("SCBD_KV_READ", "Transaction Received through actual_ecc_seed_read_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_KV_READ", {"            Data: ",t.convert2string()}, UVM_FULL)

    if (kv_ecc_seed_read_expected_hash.exists(t.get_key())) begin
        t_expected = kv_ecc_seed_read_expected_hash[t.get_key()];
        txn_eq = t.compare(t_expected);

        if(txn_eq) `uvm_info("SCBD_KV_READ", $sformatf("Actual txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h} matches expected!", t.read_entry,t.read_offset,t.read_data,t.last,t.error ), UVM_HIGH)
        else       `uvm_error("SCBD_KV_READ", $sformatf("Actual txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read Data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h} does not match expected txn with {Read entry: 0x%x}, {Read offset: 0x%x}, {Read data: 0x%x}, {Read last dword: 0x%x}, {Read resp err: %h}", t.read_entry,t.read_offset,t.read_data,t.last,t.error, t_expected.read_entry,t_expected.read_offset,t_expected.read_data,t_expected.last,t_expected.error ))

        if(t.error) `uvm_info("SCBD_KV_READ", "Trying to read a locked reg or reg with dest_valid = 0 will return 0s", UVM_MEDIUM);
    end
    else begin
        `uvm_error("SCBD_KV_READ", "Received unmatched read transaction. Cannot find corresponding expected txn!");
    end
 
    // pragma uvmf custom actual_analysis_export_scoreboard end
  endfunction

  //-----------------------------------------------


  // FUNCTION: write_expected_ahb_analysis_export
  // QVIP transactions received through expected_ahb_analysis_export initiate the execution of this function.
  // This function casts incoming QVIP transactions into the correct protocol type and then performs prediction 
  // of DUT output values based on DUT input, configuration and state
  virtual function void write_expected_ahb_analysis_export(mvc_sequence_item_base _t);
    // pragma uvmf custom expected_ahb_analysis_export_scoreboard begin
    ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) t;
    if (!$cast(t,_t)) begin
      `uvm_fatal("SCBD_AHB","Cast from mvc_sequence_item_base to ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) in write_expected_ahb_analysis_export failed!")
    end
    `uvm_info("SCBD_AHB", "Transaction Received through expected_ahb_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_AHB",{"            Data: ",t.convert2string()}, UVM_FULL)

    ahb_expected_q.push_back(t);
    // //  UVMF_CHANGE_ME: Implement custom scoreboard here.  
    // `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
    // `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The kv_scoreboard::write_expected_ahb_analysis_export function needs to be completed with custom scoreboard functionality",UVM_NONE)
    // `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
 
    // pragma uvmf custom expected_ahb_analysis_export_scoreboard end
  endfunction
  
  // FUNCTION: write_actual_ahb_analysis_export
  // QVIP transactions received through actual_ahb_analysis_export initiate the execution of this function.
  // This function casts incoming QVIP transactions into the correct protocol type and then performs prediction 
  // of DUT output values based on DUT input, configuration and state
  virtual function void write_actual_ahb_analysis_export(mvc_sequence_item_base _t);
    // pragma uvmf custom actual_ahb_analysis_export_scoreboard begin
    ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) t;
    ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) t_exp;
    bit txn_eq;
    if (!$cast(t,_t)) begin
      `uvm_fatal("SCBD_AHB","Cast from mvc_sequence_item_base to ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) in write_actual_ahb_analysis_export failed!")
    end
    `uvm_info("SCBD_AHB", "Transaction Received through actual_ahb_analysis_export", UVM_HIGH)
    `uvm_info("SCBD_AHB",{"            Data: ",t.convert2string()}, UVM_FULL)
    if (ahb_expected_q.size() > 0) begin
        t_exp = ahb_expected_q.pop_front();
        txn_eq = t.compare(t_exp);
        if (txn_eq) `uvm_info ("SCBD_AHB", $sformatf("Actual AHB txn with {Address: 0x%x} {Data: 0x%x} {RnW: %p} matches expected",t.address,t.data[0],t.RnW), UVM_MEDIUM)
        else        `uvm_error("SCBD_AHB", $sformatf("Actual AHB txn with {Address: 0x%x} {Data: 0x%x} {RnW: %p} {Resp: %p} does not match expected: {Address: 0x%x} {Data: 0x%x} {RnW: %p} {Resp: %p}",t.address,t.data[0],t.RnW,t.resp[0],t_exp.address,t_exp.data[0],t_exp.RnW,t_exp.resp[0]))
    end
    else begin
    //  UVMF_CHANGE_ME: Implement custom scoreboard here.  
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The kv_scoreboard::write_actual_ahb_analysis_export function needs to be completed with custom scoreboard functionality",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
    end
 
    // pragma uvmf custom actual_ahb_analysis_export_scoreboard end
  endfunction
  

  // FUNCTION: extract_phase
  virtual function void extract_phase(uvm_phase phase);
// pragma uvmf custom extract_phase begin
         super.extract_phase(phase);
// pragma uvmf custom extract_phase end
  endfunction

  // FUNCTION: check_phase
  virtual function void check_phase(uvm_phase phase);
// pragma uvmf custom check_phase begin
         super.check_phase(phase);
// pragma uvmf custom check_phase end
  endfunction

  // FUNCTION: report_phase
  virtual function void report_phase(uvm_phase phase);
// pragma uvmf custom report_phase begin
         super.report_phase(phase);
// pragma uvmf custom report_phase end
  endfunction

endclass 

// pragma uvmf custom external begin

  // FUNCTION: disable_wait_for_scoreboard_empty
  // Used to disable delaying run phase completion until scoreboard empty.
function void kv_scoreboard::disable_wait_for_scoreboard_empty();
    wait_for_scoreboard_empty=0;
 endfunction

 // FUNCTION: enable_wait_for_scoreboard_empty
 // Used to enable delaying run phase completion until scoreboard empty.
 function void kv_scoreboard::enable_wait_for_scoreboard_empty();
    wait_for_scoreboard_empty=1;
 endfunction

 // TASK: wait_for_scoreboard_drain FIXME
 // This task is used to implement a mechanism to delay run_phase termination to allow the scoreboard time to drain.  
 // Extend a scoreboard to override this task based on project requirements.  The delay mechanism can be for instance 
 // a mechanism that ends when the last entry is removed from the scoreboard.
 task kv_scoreboard::wait_for_scoreboard_drain();
     bit entries_remaining = 0;
     if (kv_hmac_key_read_expected_hash.size() != 0) entries_remaining |= 1;
     if (kv_hmac_block_read_expected_hash.size() != 0) entries_remaining |= 1;
     if (kv_sha512_block_read_expected_hash.size() != 0) entries_remaining |= 1;
     if (kv_ecc_privkey_read_expected_hash.size() != 0) entries_remaining |= 1;
     if (kv_ecc_seed_read_expected_hash.size() != 0) entries_remaining |= 1;
     if (ahb_expected_q.size() != 0)        entries_remaining |= 1;
     while (entries_remaining) begin : while_entries_remaining
         @entry_received; // FIXME
         entries_remaining=0;
         if (kv_hmac_key_read_expected_hash.size() != 0) entries_remaining |= 1;
         if (kv_hmac_block_read_expected_hash.size() != 0) entries_remaining |= 1;
         if (kv_sha512_block_read_expected_hash.size() != 0) entries_remaining |= 1;
         if (kv_ecc_privkey_read_expected_hash.size() != 0) entries_remaining |= 1;
         if (kv_ecc_seed_read_expected_hash.size() != 0) entries_remaining |= 1;
         if (ahb_expected_q.size() != 0)        entries_remaining |= 1;
    end : while_entries_remaining
 endtask

 // FUNCTION: phase_ready_to_end FIXME
  // This function is executed at the end of the run_phase.  
  // It allows the simulation to continue so that remaining transactions on the scoreboard can be removed.
 function void kv_scoreboard::phase_ready_to_end( uvm_phase phase );
    if (phase.get_name() == "run") 
       begin : if_run_phase
       if ( wait_for_scoreboard_empty ) 
          begin : if_wait_for_scoreboard_empty
          phase.raise_objection( this , {get_full_name(),"- Delaying run_phase termination to allow scoreboard to empty."} );
          fork 
            begin : wait_for_scoreboard_to_drain
               wait_for_scoreboard_drain();
               phase.drop_objection( this , {get_full_name(),"- Done waiting for scoreboard to empty."});
            end : wait_for_scoreboard_to_drain
          join_none
          end : if_wait_for_scoreboard_empty
       end : if_run_phase
 endfunction

// pragma uvmf custom external end

