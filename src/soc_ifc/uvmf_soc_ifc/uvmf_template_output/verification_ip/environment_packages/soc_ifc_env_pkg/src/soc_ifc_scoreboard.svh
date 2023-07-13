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
//   expected_analysis_export receives transactions of type  soc_ifc_status_transaction  
//   expected_cptra_analysis_export receives transactions of type  cptra_status_transaction  
//   actual_analysis_export receives transactions of type  soc_ifc_status_transaction  
//   actual_cptra_analysis_export receives transactions of type  cptra_status_transaction  
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
`ifndef SOC_IFC_RESET_FLAG
  `define SOC_IFC_RESET_FLAG
class reset_flag extends uvm_object;
    `uvm_object_utils(reset_flag)
    function new (string name ="");
        super.new(name);
    endfunction
endclass
`endif

class soc_ifc_scoreboard #(
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  // Factory registration of this class
  `uvm_component_param_utils( soc_ifc_scoreboard #(
                              CONFIG_T,
                              BASE_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;

  
  // Instantiate the analysis exports
  uvm_analysis_imp_expected_analysis_export #(soc_ifc_status_transaction, soc_ifc_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) expected_analysis_export;
  uvm_analysis_imp_expected_cptra_analysis_export #(cptra_status_transaction, soc_ifc_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) expected_cptra_analysis_export;
  uvm_analysis_imp_actual_analysis_export #(soc_ifc_status_transaction, soc_ifc_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) actual_analysis_export;
  uvm_analysis_imp_actual_cptra_analysis_export #(cptra_status_transaction, soc_ifc_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) actual_cptra_analysis_export;


 
  // Instantiate QVIP analysis exports
  uvm_analysis_imp_expected_ahb_analysis_export #(mvc_sequence_item_base, soc_ifc_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) expected_ahb_analysis_export;
  uvm_analysis_imp_expected_apb_analysis_export #(mvc_sequence_item_base, soc_ifc_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) expected_apb_analysis_export;
  uvm_analysis_imp_actual_ahb_analysis_export #(mvc_sequence_item_base, soc_ifc_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) actual_ahb_analysis_export;
  uvm_analysis_imp_actual_apb_analysis_export #(mvc_sequence_item_base, soc_ifc_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) actual_apb_analysis_export;


  // pragma uvmf custom class_item_additional begin

  // Associative array of exptected transactions keyed with the integer accessed using
  // the transactions get_key() interface.
  soc_ifc_status_transaction                                                soc_ifc_expected_hash[int unsigned]; // FIXME
  cptra_status_transaction                                                  cptra_expected_hash  [int unsigned]; // FIXME
  // Use Queues for AHB/APB txns since there is no get_key() method
  ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                              ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                              ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                              ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                              ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                              ahb_lite_slave_0_params::AHB_RDATA_WIDTH)     ahb_expected_q       [$]; // FIXME
  apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT,
                               apb5_master_0_params::APB3_PADDR_BIT_WIDTH,
                               apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,
                               apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_expected_q       [$]; // FIXME

  // Use an soc_ifc_status_monitor_struct to track the expected state of the
  // soc_ifc_status interface.
  // This definition comes from soc_ifc_status_pkg (specifically, from
  // soc_ifc_status_macros).
  // This scoreboard allows transaction aggregation on this interface, but if
  // any member bit is detected transitioning more than once in between received
  // 'actual' transactions, it suggests that the DUT signal failed to mirror the
  // rise/fall behavior that was predicted.
  `soc_ifc_status_MONITOR_STRUCT
    soc_ifc_status_monitor_s soc_ifc_status_monitor_struct, soc_ifc_status_monitor_struct_prev;
  bit [1:0] soc_ifc_status_monitor_toggle_count [$bits(soc_ifc_status_monitor_s)-1:0] = '{default: 0};

  // Variables used to report transaction matches and mismatches
  int match_count = 0;
  int mismatch_count = 0;
  int nothing_to_compare_against_count = 0;
  int multiple_missed_txn_count = 0;
  bit testcase_passed = 1'b0;

  // Variables used for report_phase summary output formatting using report_message()
  int report_variables[];
  string report_hdr = "SCOREBOARD_RESULTS: ";

  // Variable used to enable end of test scoreboard empty check
  bit end_of_test_empty_check=1; // FIXME
  int transaction_count = 0;

  // Variable used to delay run phase completion until scoreboard empty
  bit wait_for_scoreboard_empty; // FIXME
  event entry_received;

  // Event used for reset management
  uvm_event reset_handled;
  reset_flag hard_reset_flag;
  reset_flag soft_reset_flag;

  extern function void handle_reset(string kind = "HARD");
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

    expected_analysis_export = new("expected_analysis_export", this);
    expected_cptra_analysis_export = new("expected_cptra_analysis_export", this);
    actual_analysis_export = new("actual_analysis_export", this);
    actual_cptra_analysis_export = new("actual_cptra_analysis_export", this);
    expected_ahb_analysis_export = new("expected_ahb_analysis_export", this);
    expected_apb_analysis_export = new("expected_apb_analysis_export", this);
    actual_ahb_analysis_export = new("actual_ahb_analysis_export", this);
    actual_apb_analysis_export = new("actual_apb_analysis_export", this);
  // pragma uvmf custom build_phase begin
    reset_handled = new("reset_handled");
    hard_reset_flag = new("hard_reset_flag"); // Used as trigger data for reset events. In UVM 1.2, data changes from a uvm_object to a string
    soft_reset_flag = new("soft_reset_flag"); // Used as trigger data for reset events. In UVM 1.2, data changes from a uvm_object to a string
  // pragma uvmf custom build_phase end
  endfunction

  // FUNCTION: write_expected_analysis_export
  // Transactions received through expected_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_expected_analysis_export(soc_ifc_status_transaction t);
    // pragma uvmf custom expected_analysis_export_scoreboard begin
    bit multiple_missed_txn_error = 1'b0;
    soc_ifc_status_monitor_s soc_ifc_status_monitor_struct_rpt = '{default:0};

    `uvm_info("SCBD_SOC_IFC_STS", $sformatf("Transaction Received through expected_analysis_export with key: [%0d]", t.get_key()), UVM_MEDIUM)
    `uvm_info("SCBD_SOC_IFC_STS", {"            Data: ",t.convert2string()}, UVM_FULL)

    soc_ifc_expected_hash[t.get_key()] = t;
    soc_ifc_status_monitor_struct_prev = soc_ifc_status_monitor_struct;
    soc_ifc_status_monitor_struct = t.to_monitor_struct();
    foreach (soc_ifc_status_monitor_toggle_count[sts_bit]) begin
        // If a bit has toggled on the status interface since last predicted transaction
        // increment our toggle counter. But don't exceed a count of 2'b10, because
        // we don't want to roll over
        if ((soc_ifc_status_monitor_struct[sts_bit] ^ soc_ifc_status_monitor_struct_prev[sts_bit]) && (soc_ifc_status_monitor_toggle_count[sts_bit] <= 1))
            soc_ifc_status_monitor_toggle_count[sts_bit] += 1;
        if (soc_ifc_status_monitor_toggle_count[sts_bit] > 1) begin
            multiple_missed_txn_error = 1'b1;
            soc_ifc_status_monitor_struct_rpt[sts_bit] = 1'b1;
        end
    end
    if (multiple_missed_txn_error) begin
        multiple_missed_txn_count++;
        `uvm_error("SCBD_SOC_IFC_STS",$sformatf("Received multiple expected transactions without corresponding actual transaction. Problem fields: %p", soc_ifc_status_monitor_struct_rpt))
    end
    transaction_count++;
    -> entry_received;
 
    // pragma uvmf custom expected_analysis_export_scoreboard end
  endfunction

  // FUNCTION: write_expected_cptra_analysis_export
  // Transactions received through expected_cptra_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_expected_cptra_analysis_export(cptra_status_transaction t);
    // pragma uvmf custom expected_cptra_analysis_export_scoreboard begin
    `uvm_info("SCBD_CPTRA_STS", $sformatf("Transaction Received through expected_cptra_analysis_export with key: [%0d]", t.get_key()), UVM_MEDIUM)
    `uvm_info("SCBD_CPTRA_STS", {"            Data: ",t.convert2string()}, UVM_FULL)

    cptra_expected_hash[t.get_key()] = t;
    if (reset_handled.is_on()) begin
        if (!t.noncore_rst_asserted || !t.uc_rst_asserted)
            `uvm_error("SCBD_CPTRA_STS", $sformatf("Unexpected transaction! soc_ifc_scoreboard was reset, but the reset signals in this transaction are not asserted. noncore_rst_asserted: [%d] uc_rst_asserted: [%d]", t.noncore_rst_asserted, t.uc_rst_asserted))
        reset_handled.reset();
    end
    transaction_count++;
    -> entry_received;
 
    // pragma uvmf custom expected_cptra_analysis_export_scoreboard end
  endfunction

  // FUNCTION: write_actual_analysis_export
  // Transactions received through actual_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_actual_analysis_export(soc_ifc_status_transaction t);
    // pragma uvmf custom actual_analysis_export_scoreboard begin
    soc_ifc_status_transaction t_exp;
    bit txn_eq;

    `uvm_info("SCBD_SOC_IFC_STS", $sformatf("Transaction Received through actual_analysis_export with key: [%0d]", t.get_key()), UVM_MEDIUM)
    `uvm_info("SCBD_SOC_IFC_STS", {"            Data: ",t.convert2string()}, UVM_FULL)

    // Check for expected analysis port to receive first transaction after a reset before proceeding with the actual check
    // This indicates the environment level reset is finished and the predictor had time to forward an expected
    // event for soc_ifc_status_if, if applicable
    if (reset_handled.is_on())
        `uvm_error("SCBD_SOC_IFC_STS", "Received actual soc_ifc_status_transaction after a reset event, but prior to receiving the expected transaction!")

    // If there are multiple expected transactions, see if they can be aggregated
    if ((soc_ifc_expected_hash.size() > 1) && soc_ifc_expected_hash.exists(t.get_key())) begin
        int unsigned txn_agg_count;
        int unsigned greatest_matching_key;
        soc_ifc_status_monitor sts_mon_h;
        uvm_component comp_h = this.get_parent().lookup("soc_ifc_status_agent.soc_ifc_status_agent_monitor");

        // Find the latest expected transaction that perfectly matches
        // current actual transaction
        if (!soc_ifc_expected_hash.last(greatest_matching_key))
            `uvm_fatal("SCBD_SOC_IFC_STS", "Failed to run last() when soc_ifc_expected_hash is not empty!")
        t_exp = soc_ifc_expected_hash[greatest_matching_key];
        txn_eq = t.compare(t_exp);
        while(!txn_eq) begin
            if (!soc_ifc_expected_hash.prev(greatest_matching_key)) begin
                txn_eq = 0;
                break;
            end
            else begin
                t_exp = soc_ifc_expected_hash[greatest_matching_key];
                txn_eq = t.compare(t_exp);
            end
        end

        // Based on comparison results, proceed with updating scoreboard state
        if (txn_eq) begin

            `uvm_info("SCBD_SOC_IFC_STS", "write_actual_analysis_export() received transaction matching multiple aggregated expected transactions!", UVM_MEDIUM)
            match_count++;

            // This is a 0's-based count of how many expected transactions
            // were aggregated to the current actual
            txn_agg_count = greatest_matching_key - t.get_key();

            // Reset the toggle counter
            soc_ifc_status_monitor_toggle_count = '{default:2'b00};
            soc_ifc_status_monitor_struct = soc_ifc_expected_hash[greatest_matching_key].to_monitor_struct();

            // Recalculate toggle count and flush aggregated entries
            foreach (soc_ifc_expected_hash[idx]) begin
                // Clear aggregated entries from the table
                if (idx <= greatest_matching_key)
                    soc_ifc_expected_hash.delete(idx);

                // Rebuild the toggle counter based on entries that remain in
                // the expected txn hash
                else begin
                    soc_ifc_status_monitor_struct_prev = soc_ifc_status_monitor_struct;
                    soc_ifc_status_monitor_struct = soc_ifc_expected_hash[idx].to_monitor_struct();
                    foreach (soc_ifc_status_monitor_toggle_count[sts_bit]) begin
                        // If a bit has toggled on the status interface since last predicted transaction
                        // increment our toggle counter. But don't exceed a count of 2'b10, because
                        // we don't want to roll over
                        if ((soc_ifc_status_monitor_struct[sts_bit] ^ soc_ifc_status_monitor_struct_prev[sts_bit]) && (soc_ifc_status_monitor_toggle_count[sts_bit] <= 1))
                            soc_ifc_status_monitor_toggle_count[sts_bit] += 1;
                    end
                end
            end

            // Synchronize the monitor txn_key with the value in the env predictor
            if (!$cast(sts_mon_h, comp_h))
                `uvm_fatal("SCBD_SOC_IFC_STS",$sformatf("Failed to get soc_ifc_status_agent_monitor from %s.lookup()", this.get_parent().get_name()))
            else
                sts_mon_h.force_advance_txn_key(txn_agg_count);
        end
        else begin
            `uvm_error("SCBD_SOC_IFC_STS", $sformatf("write_actual_analysis_export() failed to find matching transaction in soc_ifc_expected_hash while attempting aggregated transaction analysis!\nActual:   %s", t.convert2string()))
            mismatch_count++;
            // Just delete 1 entry from the hash to prevent the hash from exploding
            // in size over the simulation - we've already reported the error
            soc_ifc_expected_hash.delete(t.get_key());
        end
    end
    // 1:1 match of incoming actual transaction with an expected transaction
    else if (soc_ifc_expected_hash.exists(t.get_key())) begin
        t_exp = soc_ifc_expected_hash[t.get_key()];
        txn_eq = t.compare(t_exp);
        if (txn_eq) begin
            `uvm_info("SCBD_SOC_IFC_STS", "write_actual_analysis_export() received transaction matching expected", UVM_HIGH)
            match_count++;
        end
        else begin
            `uvm_error("SCBD_SOC_IFC_STS", $sformatf("write_actual_analysis_export() received transaction not matching expected\nExpected: %s\nActual:   %s", t_exp.convert2string(), t.convert2string()))
            mismatch_count++;
        end
        soc_ifc_expected_hash.delete(t.get_key());
        // Reset the toggle counter
        soc_ifc_status_monitor_toggle_count = '{default:2'b00};
    end
    else begin
        `uvm_info("FIXME_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The soc_ifc_scoreboard::write_actual_analysis_export function needs to be completed with custom scoreboard functionality for unexpected actual transactions",UVM_LOW)
        `uvm_error("SCBD_SOC_IFC_STS",$sformatf("NO PREDICTED ENTRY WITH KEY [%0d] TO COMPARE AGAINST:%s", t.get_key(), t.convert2string()))
        nothing_to_compare_against_count++;
    end
    -> entry_received;
 
    // pragma uvmf custom actual_analysis_export_scoreboard end
  endfunction

  // FUNCTION: write_actual_cptra_analysis_export
  // Transactions received through actual_cptra_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_actual_cptra_analysis_export(cptra_status_transaction t);
    // pragma uvmf custom actual_cptra_analysis_export_scoreboard begin
    cptra_status_transaction t_exp;
    bit txn_eq;

    `uvm_info("SCBD_CPTRA_STS", $sformatf("Transaction Received through actual_cptra_analysis_export with key: [%0d]", t.get_key()), UVM_MEDIUM)
    `uvm_info("SCBD_CPTRA_STS", {"            Data: ",t.convert2string()}, UVM_FULL)

    // Check for expected analysis port to receive first transaction after a reset before proceeding with the actual check
    if (reset_handled.is_on())
        `uvm_error("SCBD_CPTRA_STS", "Received actual cptra_status_transaction after a reset event, but prior to receiving the expected transaction!")
    if (cptra_expected_hash.exists(t.get_key())) begin
        t_exp = cptra_expected_hash[t.get_key()];
        txn_eq = t.compare(t_exp);
        if (txn_eq) begin
            `uvm_info("SCBD_CPTRA_STS", "write_actual_cptra_analysis_export() received transaction matching expected", UVM_HIGH)
            match_count++;
        end
        else begin
            `uvm_error("SCBD_CPTRA_STS", $sformatf("write_actual_cptra_analysis_export() received transaction not matching expected\nExpected: %s\nActual:   %s", t_exp.convert2string(), t.convert2string()))
            mismatch_count++;
        end
        cptra_expected_hash.delete(t.get_key());
    end
    else begin
        `uvm_info("FIXME_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The soc_ifc_scoreboard::write_actual_cptra_analysis_export function needs to be completed with custom scoreboard functionality for unexpected actual transactions",UVM_LOW)
        `uvm_error("SCBD_CPTRA_STS",$sformatf("NO PREDICTED ENTRY WITH KEY [%0d] TO COMPARE AGAINST:%s", t.get_key(), t.convert2string()))
        nothing_to_compare_against_count++;
    end
    -> entry_received;
 
    // pragma uvmf custom actual_cptra_analysis_export_scoreboard end
  endfunction


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

    transaction_count++;
    -> entry_received;
 
    // pragma uvmf custom expected_ahb_analysis_export_scoreboard end
  endfunction
  
  // FUNCTION: write_expected_apb_analysis_export
  // QVIP transactions received through expected_apb_analysis_export initiate the execution of this function.
  // This function casts incoming QVIP transactions into the correct protocol type and then performs prediction 
  // of DUT output values based on DUT input, configuration and state
  virtual function void write_expected_apb_analysis_export(mvc_sequence_item_base _t);
    // pragma uvmf custom expected_apb_analysis_export_scoreboard begin
    apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT, apb5_master_0_params::APB3_PADDR_BIT_WIDTH, apb5_master_0_params::APB3_PWDATA_BIT_WIDTH, apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) t;
    if (!$cast(t,_t)) begin
      `uvm_fatal("SCBD_APB","Cast from mvc_sequence_item_base to apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT, apb5_master_0_params::APB3_PADDR_BIT_WIDTH, apb5_master_0_params::APB3_PWDATA_BIT_WIDTH, apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) in write_expected_apb_analysis_export failed!")
    end
    `uvm_info("SCBD_APB", "Transaction Received through expected_apb_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_APB",{"            Data: ",t.convert2string()}, UVM_FULL)

    apb_expected_q.push_back(t);

    transaction_count++;
    -> entry_received;
 
    // pragma uvmf custom expected_apb_analysis_export_scoreboard end
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
    `uvm_info("SCBD_AHB", "Transaction Received through actual_ahb_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_AHB",{"            Data: ",t.convert2string()}, UVM_FULL)

    if (ahb_expected_q.size() > 0) begin
        t_exp = ahb_expected_q.pop_front();
        txn_eq = t.compare(t_exp);
        if (txn_eq) begin
            match_count++;
            `uvm_info ("SCBD_AHB", $sformatf("Actual AHB txn with {Address: 0x%x} {Data: 0x%x} {RnW: %p} matches expected",t.address,t.data[0],t.RnW), UVM_HIGH)
        end
        else begin
            mismatch_count++;
            `uvm_error("SCBD_AHB", $sformatf("Actual AHB txn with {Address: 0x%x} {Data: 0x%x} {RnW: %p} {Resp: %p} does not match expected: {Address: 0x%x} {Data: 0x%x} {RnW: %p} {Resp: %p}",t.address,t.data[0],t.RnW,t.resp[0],t_exp.address,t_exp.data[0],t_exp.RnW,t_exp.resp[0]))
        end
    end
    else begin
        `uvm_info("FIXME_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The soc_ifc_scoreboard::write_actual_ahb_analysis_export function needs to be completed with custom scoreboard functionality for unexpected actual transactions",UVM_LOW)
        `uvm_error("SCBD_AHB",$sformatf("NO PREDICTED ENTRY TO COMPARE AGAINST:%s",t.convert2string()))
        nothing_to_compare_against_count++;
    end
    -> entry_received;
 
    // pragma uvmf custom actual_ahb_analysis_export_scoreboard end
  endfunction
  
  // FUNCTION: write_actual_apb_analysis_export
  // QVIP transactions received through actual_apb_analysis_export initiate the execution of this function.
  // This function casts incoming QVIP transactions into the correct protocol type and then performs prediction 
  // of DUT output values based on DUT input, configuration and state
  virtual function void write_actual_apb_analysis_export(mvc_sequence_item_base _t);
    // pragma uvmf custom actual_apb_analysis_export_scoreboard begin
    apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT, apb5_master_0_params::APB3_PADDR_BIT_WIDTH, apb5_master_0_params::APB3_PWDATA_BIT_WIDTH, apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) t;
    apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT, apb5_master_0_params::APB3_PADDR_BIT_WIDTH, apb5_master_0_params::APB3_PWDATA_BIT_WIDTH, apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) t_exp;
    bit txn_eq;
    if (!$cast(t,_t)) begin
      `uvm_fatal("SCBD_APB","Cast from mvc_sequence_item_base to apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT, apb5_master_0_params::APB3_PADDR_BIT_WIDTH, apb5_master_0_params::APB3_PWDATA_BIT_WIDTH, apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) in write_actual_apb_analysis_export failed!")
    end
    `uvm_info("SCBD_APB", "Transaction Received through actual_apb_analysis_export", UVM_MEDIUM)
    `uvm_info("SCBD_APB",{"            Data: ",t.convert2string()}, UVM_FULL)

    if (apb_expected_q.size() > 0) begin
        t_exp = apb_expected_q.pop_front();
        txn_eq = t.compare(t_exp);
        if (txn_eq) begin
            match_count++;
            `uvm_info ("SCBD_APB", $sformatf("Actual APB txn with {Address: 0x%x} {Data: 0x%x} {read_or_write: %p} matches expected",t.addr,t.read_or_write == mgc_apb3_v1_0_pkg::APB3_TRANS_READ ? t.rd_data : t.wr_data,t.read_or_write), UVM_HIGH)
        end
        else begin
            mismatch_count++;
            `uvm_error("SCBD_APB", $sformatf("Actual APB txn with {Address: 0x%x} {Data: 0x%x} {read_or_write: %p} {Error: %p} does not match expected: {Address: 0x%x} {Data: 0x%x} {RnW: %p} {Error: %p}",t.addr,t.read_or_write == mgc_apb3_v1_0_pkg::APB3_TRANS_READ ? t.rd_data : t.wr_data,t.read_or_write,t.slave_err,t_exp.addr,t_exp.read_or_write == mgc_apb3_v1_0_pkg::APB3_TRANS_READ ? t_exp.rd_data : t_exp.wr_data,t_exp.read_or_write,t_exp.slave_err))
        end
    end
    else begin
        `uvm_info("FIXME_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The soc_ifc_scoreboard::write_actual_apb_analysis_export function needs to be completed with custom scoreboard functionality for unexpected actual transactions",UVM_LOW)
        `uvm_error("SCBD_APB",$sformatf("NO PREDICTED ENTRY TO COMPARE AGAINST:%s",t.convert2string()))
        nothing_to_compare_against_count++;
    end
    -> entry_received;
 
    // pragma uvmf custom actual_apb_analysis_export_scoreboard end
  endfunction
  

  // FUNCTION: extract_phase
  virtual function void extract_phase(uvm_phase phase);
// pragma uvmf custom extract_phase begin
     super.extract_phase(phase);
     report_variables = {transaction_count, match_count, mismatch_count, nothing_to_compare_against_count, multiple_missed_txn_count};
// pragma uvmf custom extract_phase end
  endfunction

  // FUNCTION: check_phase
  virtual function void check_phase(uvm_phase phase);
// pragma uvmf custom check_phase begin
     super.check_phase(phase);
     if (transaction_count == 0) `uvm_error("SCBD","No Transactions Scoreboarded")
     if ((match_count > 0) && (mismatch_count == 0) && (nothing_to_compare_against_count == 0) && (multiple_missed_txn_count == 0))
        testcase_passed = 1'b1;
// pragma uvmf custom check_phase end
  endfunction

  // FUNCTION: report_message
  // Builds the report_phase message printed for scoreboards derived from this base 
  // Provides for customization of output formatting
  virtual function string report_message(string header, int variables [] );
        return {$sformatf("%s PREDICTED_TRANSACTIONS=%0d MATCHES=%0d MISMATCHES=%0d NO_COMPARISON_TXN=%0d MULTIPLE_MISSED_TXN=%0d", header, variables[0], variables[1], variables[2], variables[3], variables[4])}; 
  endfunction

  // FUNCTION: report_phase
  virtual function void report_phase(uvm_phase phase);
// pragma uvmf custom report_phase begin
      super.report_phase(phase);
      `uvm_info("SCBD", report_message(report_hdr, report_variables),UVM_LOW)
      if (testcase_passed)
          $display("* TESTCASE PASSED");
      else
          $display("* TESTCASE FAILED");
// pragma uvmf custom report_phase end
  endfunction

endclass 

// pragma uvmf custom external begin

  // FUNCTION: handle_reset
  // Used to facilitate reset handling for different kinds of reset
  // that may occur in soc_ifc environment.
  // "SOFT" reset (aka cptra_rst_b=0)
  //   * Causes flush of all expected and actual transactions
  //   * Initiates an event trigger to indicate reset was called
  // "HARD" reset (aka cptra_pwrgood=0)
  //   * Causes flush of all expected and actual transactions
  //   * Initiates an event trigger to indicate reset was called
  function void soc_ifc_scoreboard::handle_reset(string kind = "HARD");
      reset_flag kind_handled;
      kind_handled = kind == "HARD" ? hard_reset_flag :
                     kind == "SOFT" ? soft_reset_flag :
                                      null;

      // Flush transactions
      soc_ifc_expected_hash.delete();
      cptra_expected_hash  .delete();
      ahb_expected_q.delete();
      apb_expected_q.delete();

      // Clear toggle counter
      soc_ifc_status_monitor_struct      = '{default:0};
      soc_ifc_status_monitor_struct_prev = '{default:0};
      soc_ifc_status_monitor_toggle_count = '{default:2'b00};

      // Event trigger
      reset_handled.trigger(kind_handled);
  endfunction

  // FUNCTION: disable_wait_for_scoreboard_empty
  // Used to disable delaying run phase completion until scoreboard empty.
  function void soc_ifc_scoreboard::disable_wait_for_scoreboard_empty();
     wait_for_scoreboard_empty=0;
  endfunction

  // FUNCTION: enable_wait_for_scoreboard_empty
  // Used to enable delaying run phase completion until scoreboard empty.
  function void soc_ifc_scoreboard::enable_wait_for_scoreboard_empty();
     wait_for_scoreboard_empty=1;
  endfunction

  // TASK: wait_for_scoreboard_drain
  // This task is used to implement a mechanism to delay run_phase termination to allow the scoreboard time to drain.  
  // Extend a scoreboard to override this task based on project requirements.  The delay mechanism can be for instance 
  // a mechanism that ends when the last entry is removed from the scoreboard.
  task soc_ifc_scoreboard::wait_for_scoreboard_drain();
      bit entries_remaining = 0;
      if (soc_ifc_expected_hash.size() != 0) entries_remaining |= 1;
      if (cptra_expected_hash.size() != 0)   entries_remaining |= 1;
      if (ahb_expected_q.size() != 0)        entries_remaining |= 1;
      if (apb_expected_q.size() != 0)        entries_remaining |= 1;
      while (entries_remaining) begin : while_entries_remaining
          `uvm_info("SOC_IFC_SCBD_DRAIN",$sformatf("Waiting for entries to drain. Remaining: soc_ifc_exp[%d] cptra_exp[%d] ahb_exp[%d] apb_exp[%d]", soc_ifc_expected_hash.size(), cptra_expected_hash.size(), ahb_expected_q.size(), apb_expected_q.size()),UVM_NONE)
          begin: VERBOSE_TXN_DUMP
              foreach (soc_ifc_expected_hash[ii]) begin `uvm_info("SOC_IFC_SCBD_DRAIN",$sformatf("soc_ifc_expected[%0d]: %s",ii,soc_ifc_expected_hash[ii].convert2string()), UVM_FULL) end
              foreach (cptra_expected_hash  [ii]) begin `uvm_info("SOC_IFC_SCBD_DRAIN",$sformatf("cptra_expected[%0d]:   %s",ii,cptra_expected_hash  [ii].convert2string()), UVM_FULL) end
              foreach (ahb_expected_q       [ii]) begin `uvm_info("SOC_IFC_SCBD_DRAIN",$sformatf("ahb_expected[%0d]:     %s",ii,ahb_expected_q       [ii].convert2string()), UVM_FULL) end
              foreach (apb_expected_q       [ii]) begin `uvm_info("SOC_IFC_SCBD_DRAIN",$sformatf("apb_expected[%0d]:     %s",ii,apb_expected_q       [ii].convert2string()), UVM_FULL) end
          end
          @entry_received;
          entries_remaining=0;
          if (soc_ifc_expected_hash.size() != 0) entries_remaining |= 1;
          if (cptra_expected_hash.size() != 0)   entries_remaining |= 1;
          if (ahb_expected_q.size() != 0)        entries_remaining |= 1;
          if (apb_expected_q.size() != 0)        entries_remaining |= 1;
      end : while_entries_remaining
  endtask

  // FUNCTION: phase_ready_to_end
  // This function is executed at the end of the run_phase.  
  // It allows the simulation to continue so that remaining transactions on the scoreboard can be removed.
  function void soc_ifc_scoreboard::phase_ready_to_end( uvm_phase phase );
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

