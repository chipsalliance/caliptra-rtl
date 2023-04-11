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
//   soc_ifc_ctrl_agent_ae receives transactions of type  soc_ifc_ctrl_transaction
//   cptra_ctrl_agent_ae receives transactions of type  cptra_ctrl_transaction
//   ahb_slave_0_ae receives transactions of type  mvc_sequence_item_base
//   apb5_slave_0_ae receives transactions of type  mvc_sequence_item_base
//
//   This analysis component has the following analysis_ports that can broadcast
//   the listed transaction type.
//
//  soc_ifc_sb_ap broadcasts transactions of type soc_ifc_status_transaction
//  cptra_sb_ap broadcasts transactions of type cptra_status_transaction
//  soc_ifc_sb_ahb_ap broadcasts transactions of type mvc_sequence_item_base
//  soc_ifc_sb_apb_ap broadcasts transactions of type mvc_sequence_item_base
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

class soc_ifc_predictor #(
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  // Factory registration of this class
  `uvm_component_param_utils( soc_ifc_predictor #(
                              CONFIG_T,
                              BASE_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;


  // Instantiate the analysis exports
  uvm_analysis_imp_soc_ifc_ctrl_agent_ae #(soc_ifc_ctrl_transaction, soc_ifc_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) soc_ifc_ctrl_agent_ae;
  uvm_analysis_imp_cptra_ctrl_agent_ae #(cptra_ctrl_transaction, soc_ifc_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) cptra_ctrl_agent_ae;
  uvm_analysis_imp_ahb_slave_0_ae #(mvc_sequence_item_base, soc_ifc_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) ahb_slave_0_ae;
  uvm_analysis_imp_apb5_slave_0_ae #(mvc_sequence_item_base, soc_ifc_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) apb5_slave_0_ae;


  // Instantiate the analysis ports
  uvm_analysis_port #(soc_ifc_status_transaction) soc_ifc_sb_ap;
  uvm_analysis_port #(cptra_status_transaction) cptra_sb_ap;
  uvm_analysis_port #(mvc_sequence_item_base) soc_ifc_sb_ahb_ap;
  uvm_analysis_port #(mvc_sequence_item_base) soc_ifc_sb_apb_ap;


  // Transaction variable for predicted values to be sent out soc_ifc_sb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction.
  typedef soc_ifc_status_transaction soc_ifc_sb_ap_output_transaction_t;
  soc_ifc_sb_ap_output_transaction_t soc_ifc_sb_ap_output_transaction;
  // Code for sending output transaction out through soc_ifc_sb_ap
  // soc_ifc_sb_ap.write(soc_ifc_sb_ap_output_transaction);

  // Transaction variable for predicted values to be sent out cptra_sb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction. 
  typedef cptra_status_transaction cptra_sb_ap_output_transaction_t;
  cptra_sb_ap_output_transaction_t cptra_sb_ap_output_transaction;
  // Code for sending output transaction out through cptra_sb_ap
  // cptra_sb_ap.write(cptra_sb_ap_output_transaction);

  // Transaction variable for predicted values to be sent out soc_ifc_sb_ahb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction. 
  typedef ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                                      ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                                      ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                                      ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                                      ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                                      ahb_lite_slave_0_params::AHB_RDATA_WIDTH) soc_ifc_sb_ahb_ap_output_transaction_t;
  soc_ifc_sb_ahb_ap_output_transaction_t soc_ifc_sb_ahb_ap_output_transaction;
  // Code for sending output transaction out through soc_ifc_sb_ahb_ap
  // soc_ifc_sb_ahb_ap.write(soc_ifc_sb_ahb_ap_output_transaction);

  // Transaction variable for predicted values to be sent out soc_ifc_sb_apb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction. 
  typedef apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT,
                                       apb5_master_0_params::APB3_PADDR_BIT_WIDTH,
                                       apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,
                                       apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) soc_ifc_sb_apb_ap_output_transaction_t;
  soc_ifc_sb_apb_ap_output_transaction_t soc_ifc_sb_apb_ap_output_transaction;
  // Code for sending output transaction out through soc_ifc_sb_apb_ap
  // soc_ifc_sb_apb_ap.write(soc_ifc_sb_apb_ap_output_transaction);

  // Define transaction handles for debug visibility
  soc_ifc_ctrl_transaction soc_ifc_ctrl_agent_ae_debug;
  cptra_ctrl_transaction cptra_ctrl_agent_ae_debug;
  mvc_sequence_item_base ahb_slave_0_ae_debug;
  mvc_sequence_item_base apb5_slave_0_ae_debug;


  // pragma uvmf custom class_item_additional begin
  bit soc_ifc_rst_in_asserted = 1'b1;
  bit noncore_rst_out_asserted = 1'b1;
  bit uc_rst_out_asserted = 1'b1;
  bit sha_err_intr_pending = 1'b0; // TODO
  bit sha_notif_intr_pending = 1'b0; // TODO
  bit fuse_update_enabled = 1'b1;
  bit ready_for_fw_push = 1'b0; // TODO
  bit ready_for_runtime = 1'b0; // TODO
  bit mailbox_flow_done = 1'b0;

  bit mailbox_data_avail = 1'b0;

  bit [31:0] nmi_vector = 32'h0;
  bit iccm_locked = 1'b0; // TODO
  bit [`CLP_OBF_KEY_DWORDS-1:0] [31:0] cptra_obf_key_reg = '{default:32'h0}; // FIXME use reg-model value?
  security_state_t security_state = '{debug_locked: 1'b1, device_lifecycle: DEVICE_UNPROVISIONED};
  bit bootfsm_breakpoint = 1'b0;

  bit [63:0] generic_output_wires = 64'h0;

  bit [apb5_master_0_params::PAUSER_WIDTH-1:0] mbox_valid_users [5]    = '{default: '1};
  bit [4:0]                                    mbox_valid_users_locked = 5'b00000;

  soc_ifc_reg_model_top  p_soc_ifc_rm;
  uvm_reg_map p_soc_ifc_APB_map; // Block map
  uvm_reg_map p_soc_ifc_AHB_map; // Block map

  int unsigned soc_ifc_status_txn_key = 0;
  int unsigned cptra_status_txn_key = 0;

  uvm_event reset_predicted;
  uvm_event reset_handled;

  reset_flag hard_reset_flag;
  reset_flag soft_reset_flag;

  extern task          handle_reset(input string kind = "HARD");
  extern function void predict_reset(input string kind = "HARD");
  extern function bit  soc_ifc_status_txn_expected_after_warm_reset();
  extern function bit  cptra_status_txn_expected_after_warm_reset();
  extern function bit  soc_ifc_status_txn_expected_after_cold_reset();
  extern function bit  cptra_status_txn_expected_after_cold_reset();
  extern function bit [`CLP_OBF_FE_DWORDS-1:0]  [31:0] get_expected_obf_field_entropy();
  extern function bit [`CLP_OBF_UDS_DWORDS-1:0] [31:0] get_expected_obf_uds_seed();
  extern function void populate_expected_soc_ifc_status_txn(ref soc_ifc_sb_ap_output_transaction_t txn);
  extern function void populate_expected_cptra_status_txn(ref cptra_sb_ap_output_transaction_t txn);
  // pragma uvmf custom class_item_additional end

  // FUNCTION: new
  function new(string name, uvm_component parent);
     super.new(name,parent);
    `uvm_info("PREDICTOR_REVIEW", "This predictor has been created either through generation or re-generation with merging.  Remove this message after the predictor has been reviewed. (manually downgraded to uvm_info)", UVM_LOW)
  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

  // FUNCTION: build_phase
  virtual function void build_phase (uvm_phase phase);

    soc_ifc_ctrl_agent_ae = new("soc_ifc_ctrl_agent_ae", this);
    cptra_ctrl_agent_ae = new("cptra_ctrl_agent_ae", this);
    ahb_slave_0_ae = new("ahb_slave_0_ae", this);
    apb5_slave_0_ae = new("apb5_slave_0_ae", this);
    soc_ifc_sb_ap =new("soc_ifc_sb_ap", this );
    cptra_sb_ap =new("cptra_sb_ap", this );
    soc_ifc_sb_ahb_ap =new("soc_ifc_sb_ahb_ap", this );
    soc_ifc_sb_apb_ap =new("soc_ifc_sb_apb_ap", this );
  // pragma uvmf custom build_phase begin
    p_soc_ifc_rm = configuration.soc_ifc_rm;
    p_soc_ifc_AHB_map = p_soc_ifc_rm.get_map_by_name("soc_ifc_AHB_map");
    p_soc_ifc_APB_map = p_soc_ifc_rm.get_map_by_name("soc_ifc_APB_map");
    reset_predicted = new("reset_predicted");
    reset_handled = new("reset_handled");
    hard_reset_flag = new("hard_reset_flag"); // Used as trigger data for reset events. In UVM 1.2, data changes from a uvm_object to a string
    soft_reset_flag = new("soft_reset_flag"); // Used as trigger data for reset events. In UVM 1.2, data changes from a uvm_object to a string
  // pragma uvmf custom build_phase end
  endfunction

  // FUNCTION: write_soc_ifc_ctrl_agent_ae
  // Transactions received through soc_ifc_ctrl_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_soc_ifc_ctrl_agent_ae(soc_ifc_ctrl_transaction t);
    // pragma uvmf custom soc_ifc_ctrl_agent_ae_predictor begin
    // Flags control whether each transaction is sent to scoreboard
    bit send_soc_ifc_sts_txn = 0;
    bit send_cptra_sts_txn = 0;
    bit send_ahb_txn = 0;
    bit send_apb_txn = 0;

    soc_ifc_ctrl_agent_ae_debug = t;
    `uvm_info("PRED_SOC_IFC_CTRL", "Transaction Received through soc_ifc_ctrl_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED_SOC_IFC_CTRL", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");
    cptra_sb_ap_output_transaction = cptra_sb_ap_output_transaction_t::type_id::create("cptra_sb_ap_output_transaction");
    soc_ifc_sb_ahb_ap_output_transaction = soc_ifc_sb_ahb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ahb_ap_output_transaction");
    soc_ifc_sb_apb_ap_output_transaction = soc_ifc_sb_apb_ap_output_transaction_t::type_id::create("soc_ifc_sb_apb_ap_output_transaction");


    // FIXME account for security_state/scan_mode below

    // Initial boot
    if (!t.set_pwrgood && soc_ifc_rst_in_asserted) begin
        cptra_obf_key_reg = t.cptra_obf_key_rand;
        for (byte ii=0; ii < 8; ii++) begin
            // Change from reset value means we expect a transaction
            send_cptra_sts_txn |= (t.cptra_obf_key_rand[ii] != p_soc_ifc_rm.soc_ifc_reg_rm.internal_obf_key[ii].key.get_reset());
        end
        if (!t.assert_rst)
            `uvm_fatal("PRED_SOC_IFC_CTRL", "Bad initial boot with cptra_rst_b deasserted")
        if (reset_handled.is_on()) begin
            `uvm_error("PRED_SOC_IFC_CTRL", "reset_handled event unexpectedly set on receiving soc_ifc_ctrl_transaction for initial boot reset")
            reset_handled.reset();
        end
        predict_reset("HARD");
    end
    // Cold reset assertion
    else if (!t.set_pwrgood) begin
        // FIXME
        // Catch obf_key, uds_seed, field_entropy reset on cold-reset
        if (!t.assert_rst) begin
            `uvm_fatal("PRED_SOC_IFC_CTRL", "Bad cold rst")
        end
        else begin
            send_soc_ifc_sts_txn = soc_ifc_status_txn_expected_after_cold_reset();
            send_cptra_sts_txn = cptra_status_txn_expected_after_cold_reset();
            `uvm_info("PRED_SOC_IFC_CTRL", $sformatf("In response to cold_reset event, send_soc_ifc_sts_txn: %d send_cptra_sts_txn: %d", send_soc_ifc_sts_txn, send_cptra_sts_txn), UVM_NONE)
            if (reset_handled.is_off())
                `uvm_fatal("PRED_SOC_IFC_CTRL", "soc_ifc_ctrl_transaction with cold reset received prior to env-level reset handling")
            else
                reset_handled.reset();
            predict_reset("HARD");
            reset_predicted.trigger(hard_reset_flag/*"HARD"*/);
            // If the obf_key changes, we expect a second cptra_status transaction
            // immediately after all the resets assert, because it takes a few clock cycles
            // for the new key to reflect to the output after cptra_pwrgood deasserts
            // So send the first one to the scoreboard immediately
            if (send_cptra_sts_txn) begin
                populate_expected_cptra_status_txn(cptra_sb_ap_output_transaction);
                cptra_sb_ap.write(cptra_sb_ap_output_transaction);
                cptra_sb_ap_output_transaction = cptra_sb_ap_output_transaction_t::type_id::create("cptra_sb_ap_output_transaction");
                `uvm_info("PRED_SOC_IFC_CTRL", "Transaction submitted through cptra_sb_ap", UVM_MEDIUM)
                send_cptra_sts_txn = 1'b0;
            end
            for (byte ii=0; ii < 8; ii++) begin
                // Change from current value means we expect a transaction
                // due to cptra_obf_key_rand changing during bringup
                send_cptra_sts_txn |= (t.cptra_obf_key_rand[ii] != cptra_obf_key_reg[ii]);
            end
            cptra_obf_key_reg = t.cptra_obf_key_rand;
        end
    end
    // Cold reset deassertion
    else if (t.set_pwrgood && t.assert_rst && soc_ifc_rst_in_asserted) begin
        for (byte ii=0; ii < 8; ii++) begin
            // Change from current value means we expect a transaction
            // due to cptra_obf_key_rand changing during bringup
            send_cptra_sts_txn |= (t.cptra_obf_key_rand[ii] != cptra_obf_key_reg[ii]);
        end
        cptra_obf_key_reg = t.cptra_obf_key_rand;
    end
    // Warm reset assertion
    else if (t.assert_rst && !soc_ifc_rst_in_asserted) begin
        send_soc_ifc_sts_txn = soc_ifc_status_txn_expected_after_warm_reset();
        send_cptra_sts_txn = cptra_status_txn_expected_after_warm_reset();
        `uvm_info("PRED_SOC_IFC_CTRL", $sformatf("In response to warm_reset event, send_soc_ifc_sts_txn: %d send_cptra_sts_txn: %d", send_soc_ifc_sts_txn, send_cptra_sts_txn), UVM_NONE)
        if (reset_handled.is_off())
            `uvm_fatal("PRED_SOC_IFC_CTRL", "soc_ifc_ctrl_transaction with cold reset received prior to env-level reset handling")
        else
            reset_handled.reset();
        predict_reset("SOFT");
        reset_predicted.trigger(soft_reset_flag/*"SOFT"*/);
    end
    // Reset deassertion or normal operation
    else if (!t.assert_rst) begin
        // Reset deassertion
        if (soc_ifc_rst_in_asserted) begin
            // Todo check for breakpoint assertion and flag an expected AHB write to clear it
            soc_ifc_rst_in_asserted = 1'b0;
            p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_fuses.predict(1'b1, -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_APB_map);
            noncore_rst_out_asserted = 1'b1;
            uc_rst_out_asserted = 1'b1;
            bootfsm_breakpoint = t.set_bootfsm_breakpoint;
            send_soc_ifc_sts_txn = 1;
            send_cptra_sts_txn = 0; // cptra sts transaction not expected until after CPTRA_FUSE_WR_DONE
        end
        // Normal operation
        else begin
            //TODO beyond detecting uc_rst_asserted, this block needs more logic
            noncore_rst_out_asserted = 1'b0; // <-- all status transactions after the first one should reflect Caliptra reset deasserted
            uc_rst_out_asserted = 1'b1; // FIXME
            send_cptra_sts_txn = 1;
        end
    end

    // Code for sending output transaction out through soc_ifc_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction
    // using either new() or create().  Broadcasting a transaction object more than once to either the
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_soc_ifc_sts_txn) begin
        populate_expected_soc_ifc_status_txn(soc_ifc_sb_ap_output_transaction);
        soc_ifc_sb_ap.write(soc_ifc_sb_ap_output_transaction);
        `uvm_info("PRED_SOC_IFC_CTRL", "Transaction submitted through soc_ifc_sb_ap", UVM_MEDIUM)
    end
    // TODO
    // Code for sending output transaction out through cptra_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_cptra_sts_txn) begin
        populate_expected_cptra_status_txn(cptra_sb_ap_output_transaction);
        cptra_sb_ap.write(cptra_sb_ap_output_transaction);
        `uvm_info("PRED_SOC_IFC_CTRL", "Transaction submitted through cptra_sb_ap", UVM_MEDIUM)
    end
    // Code for sending output transaction out through soc_ifc_sb_ahb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_ahb_txn) begin
        soc_ifc_sb_ahb_ap.write(soc_ifc_sb_ahb_ap_output_transaction);
        `uvm_error("PRED_SOC_IFC_CTRL", "NULL Transaction submitted through soc_ifc_sb_ahb_ap")
    end
    // Code for sending output transaction out through soc_ifc_sb_apb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_apb_txn) begin
        soc_ifc_sb_apb_ap.write(soc_ifc_sb_apb_ap_output_transaction);
        `uvm_error("PRED_SOC_IFC_CTRL", "NULL Transaction submitted through soc_ifc_sb_apb_ap")
    end
    // pragma uvmf custom soc_ifc_ctrl_agent_ae_predictor end
  endfunction

  // FUNCTION: write_cptra_ctrl_agent_ae
  // Transactions received through cptra_ctrl_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_cptra_ctrl_agent_ae(cptra_ctrl_transaction t);
    // pragma uvmf custom cptra_ctrl_agent_ae_predictor begin
    // Flags control whether each transaction is sent to scoreboard
    bit send_soc_ifc_sts_txn = 0;
    bit send_cptra_sts_txn = 0;
    bit send_ahb_txn = 0;
    bit send_apb_txn = 0;

    cptra_ctrl_agent_ae_debug = t;
    `uvm_info("PRED_CPTRA_CTRL", "Transaction Received through cptra_ctrl_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED_CPTRA_CTRL", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");
    cptra_sb_ap_output_transaction = cptra_sb_ap_output_transaction_t::type_id::create("cptra_sb_ap_output_transaction");
    soc_ifc_sb_ahb_ap_output_transaction = soc_ifc_sb_ahb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ahb_ap_output_transaction");
    soc_ifc_sb_apb_ap_output_transaction = soc_ifc_sb_apb_ap_output_transaction_t::type_id::create("soc_ifc_sb_apb_ap_output_transaction");

    if (t.iccm_axs_blocked) begin
        // Error caused by blocked ICCM write
        p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.error_iccm_blocked_sts.predict(1'b1, -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_AHB_map); /* AHB-access only, use AHB map*/
        if (p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.error_en.get_mirrored_value() &&
            p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_intr_en_r.error_iccm_blocked_en.get_mirrored_value())
        begin
            send_cptra_sts_txn = ~p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.get_mirrored_value();
            p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.predict(1'b1, -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_AHB_map);
        end
    end
    if (t.assert_clear_secrets) begin
        `uvm_error("PRED_CPTRA_CTRL", "Unimplemented predictor for clearing secrets")
    end

    // Code for sending output transaction out through soc_ifc_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_soc_ifc_sts_txn) begin
        populate_expected_soc_ifc_status_txn(soc_ifc_sb_ap_output_transaction);
        soc_ifc_sb_ap.write(soc_ifc_sb_ap_output_transaction);
        `uvm_info("PRED_CPTRA_CTRL", "Transaction submitted through soc_ifc_sb_ap", UVM_MEDIUM)
    end
    // Code for sending output transaction out through cptra_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_cptra_sts_txn) begin
        populate_expected_cptra_status_txn(cptra_sb_ap_output_transaction);
        cptra_sb_ap.write(cptra_sb_ap_output_transaction);
        `uvm_info("PRED_CPTRA_CTRL", "Transaction submitted through cptra_sb_ap", UVM_MEDIUM)
    end
    // Code for sending output transaction out through soc_ifc_sb_ahb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_ahb_txn) begin
        soc_ifc_sb_ahb_ap.write(soc_ifc_sb_ahb_ap_output_transaction);
        `uvm_error("PRED_CPTRA_CTRL", "NULL Transaction submitted through soc_ifc_sb_ahb_ap")
    end
    // Code for sending output transaction out through soc_ifc_sb_apb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_apb_txn) begin
        soc_ifc_sb_apb_ap.write(soc_ifc_sb_apb_ap_output_transaction);
        `uvm_error("PRED_CPTRA_CTRL", "NULL Transaction submitted through soc_ifc_sb_apb_ap")
    end
    // pragma uvmf custom cptra_ctrl_agent_ae_predictor end
  endfunction

  // FUNCTION: write_ahb_slave_0_ae
  // Transactions received through ahb_slave_0_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_ahb_slave_0_ae(mvc_sequence_item_base t);
    // pragma uvmf custom ahb_slave_0_ae_predictor begin
    ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_txn;
    uvm_reg axs_reg;
    bit [SOC_IFC_DATA_W-1:0] data_active;
    bit [ahb_lite_slave_0_params::AHB_WDATA_WIDTH-1:0] address_aligned;
    // Flags control whether each transaction is sent to scoreboard
    bit send_soc_ifc_sts_txn = 0;
    bit send_cptra_sts_txn = 0;
    bit send_ahb_txn = 1;
    bit send_apb_txn = 0;
    ahb_slave_0_ae_debug = t;

    `uvm_info("PRED_AHB", "Transaction Received through ahb_slave_0_ae", UVM_MEDIUM)
    `uvm_info("PRED_AHB", {"            Data: ",t.convert2string()}, UVM_FULL)

    // Construct one of each output transaction type.
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");
    cptra_sb_ap_output_transaction = cptra_sb_ap_output_transaction_t::type_id::create("cptra_sb_ap_output_transaction");
    soc_ifc_sb_ahb_ap_output_transaction = soc_ifc_sb_ahb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ahb_ap_output_transaction");
    soc_ifc_sb_apb_ap_output_transaction = soc_ifc_sb_apb_ap_output_transaction_t::type_id::create("soc_ifc_sb_apb_ap_output_transaction");

    $cast(ahb_txn, t);
    // Address must be aligned to the native data width in the SOC IFC! I.e. 4-byte aligned
    address_aligned = ahb_txn.address & ~(SOC_IFC_DATA_W/8 - 1);
    if (ahb_txn.address & ((SOC_IFC_DATA_W/8 - 1))) begin
        `uvm_error("PRED_AHB", "Detected AHB transfer with bad address alignment! Address: 0x%x, expected alignment: 0x%x")
    end
    // Grab the data from the address offset, similar to how it's done in HW
    // FIXME use bus2reg to do this?
    data_active = SOC_IFC_DATA_W'(ahb_txn.data[0] >> (8*(address_aligned % (ahb_lite_slave_0_params::AHB_WDATA_WIDTH/8))));

    if (p_soc_ifc_AHB_map.get_mem_by_offset(ahb_txn.address) != null) begin: MEM_AXS
        `uvm_info("PRED_AHB", $sformatf("Detected access to mailbox at address: 0x%x", ahb_txn.address), UVM_MEDIUM)
    end// MEM_AXS
    else begin: REG_AXS
        axs_reg = p_soc_ifc_AHB_map.get_reg_by_offset(ahb_txn.address);
        if (axs_reg == null) begin
            `uvm_error("PRED_AHB", $sformatf("AHB transaction to address: 0x%x decodes to null from soc_ifc_AHB_map", ahb_txn.address))
        end
//        else if (uvm_reg_data_t'(data_active) != axs_reg.get() && ahb_txn.RnW == AHB_WRITE) begin
//            // Leave the un-shifted data in the error message to help with debug
//            //TODO `uvm_error("PRED_AHB", $sformatf("AHB transaction to register %s with data: 0x%x (data_active: 0x%x), write: %p, may not match reg model value: %x", axs_reg.get_name(), ahb_txn.data[0], data_active, ahb_txn.RnW, axs_reg.get()))
//        end
        else begin
            `uvm_info("PRED_AHB", {"Detected access to register: ", axs_reg.get_full_name()}, UVM_MEDIUM)
            // Non-interrupt registers have 2-levels of ancestry back to reg_model top
            if (axs_reg.get_parent().get_parent().get_name() == "soc_ifc_rm") begin
                case (axs_reg.get_name()) inside
                    "mbox_status": begin
                        // FIXME needs more intelligence for tracking mailbox flow/PAUSER
                        if (ahb_txn.RnW == AHB_WRITE && ((data_active >> p_soc_ifc_rm.mbox_csr_rm.mbox_status.status.get_lsb_pos()) & 32'hf/*FIXME*/) != mbox_status_e'(CMD_BUSY)) begin
                            mailbox_data_avail = 1'b1;
                            send_soc_ifc_sts_txn = 1'b1;
                        end
                    end
                    "CPTRA_FLOW_STATUS": begin
                        if (ahb_txn.RnW == AHB_WRITE &&
                            ((data_active[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_fw.get_lsb_pos()     ] != this.ready_for_fw_push) ||
                             (data_active[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_runtime.get_lsb_pos()] != this.ready_for_runtime) ||
                             (data_active[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.mailbox_flow_done.get_lsb_pos()] != this.mailbox_flow_done))) begin
                            this.ready_for_fw_push = data_active[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_fw     .get_lsb_pos()];
                            this.ready_for_runtime = data_active[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_runtime.get_lsb_pos()];
                            this.mailbox_flow_done = data_active[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.mailbox_flow_done.get_lsb_pos()];
                            send_soc_ifc_sts_txn = 1'b1;
                        end
                        else if (ahb_txn.RnW == AHB_READ) begin
                            send_soc_ifc_sts_txn = 1'b0;
                        end
                    end
                    "CPTRA_FUSE_WR_DONE": begin
                        `uvm_error("PRED_AHB", "Unexpected write to CPTRA_FUSE_WR_DONE register on AHB interface")
                    end
                    "CPTRA_GENERIC_OUTPUT_WIRES[0]": begin
                        if (ahb_txn.RnW == AHB_WRITE) begin
                            case (data_active) inside
                                32'h0,[32'h2:32'h5],32'h7F,[32'h80:32'hf7]:
                                    `uvm_warning("PRED_AHB", $sformatf("Observed write to CPTRA_GENERIC_OUTPUT_WIRES with an unassigned value: 0x%x", data_active))
                                32'h1:
                                    `uvm_fatal("PRED_AHB", "Observed write to CPTRA_GENERIC_OUTPUT_WIRES to Kill Simulation with Error!") /* TODO put this in the scoreboard? */
                                [32'h6:32'h7E]:
                                    `uvm_info("PRED_AHB", $sformatf("Observed write to CPTRA_GENERIC_OUTPUT_WIRES and translating as ASCII character: %c", data_active[7:0]), UVM_MEDIUM)
                                32'hf8:
                                    `uvm_info("PRED_AHB", "Observed write to CPTRA_GENERIC_OUTPUT_WIRES [Assert interrupt flags at fixed intervals to wake up halted core]", UVM_MEDIUM)
                                32'hf9:
                                    `uvm_info("PRED_AHB", "Observed write to CPTRA_GENERIC_OUTPUT_WIRES [Lock debug in security state]", UVM_MEDIUM)
                                32'hfa:
                                    `uvm_info("PRED_AHB", "Observed write to CPTRA_GENERIC_OUTPUT_WIRES [Unlock debug in security state]", UVM_MEDIUM)
                                32'hfb:
                                    `uvm_info("PRED_AHB", "Observed write to CPTRA_GENERIC_OUTPUT_WIRES [Set the isr_active bit]", UVM_MEDIUM)
                                32'hfc:
                                    `uvm_info("PRED_AHB", "Observed write to CPTRA_GENERIC_OUTPUT_WIRES [Clear the isr_active bit]", UVM_MEDIUM)
                                32'hfd:
                                    `uvm_info("PRED_AHB", "Observed write to CPTRA_GENERIC_OUTPUT_WIRES [Toggle random SRAM single bit error injection]", UVM_MEDIUM)
                                32'hfe:
                                    `uvm_info("PRED_AHB", "Observed write to CPTRA_GENERIC_OUTPUT_WIRES [Toggle random SRAM double bit error injection]", UVM_MEDIUM)
                                32'hff:
                                    `uvm_info("PRED_AHB", "Observed write to CPTRA_GENERIC_OUTPUT_WIRES to End the simulation with a Success status", UVM_LOW)
                            endcase
                            send_soc_ifc_sts_txn = data_active != generic_output_wires[31:0];
                            generic_output_wires = {generic_output_wires[63:32],data_active}; // FIXME for data width?
                        end
                    end
                    "internal_iccm_lock": begin
                        if (ahb_txn.RnW == AHB_WRITE && !iccm_locked) begin
                            iccm_locked = 1'b1;
                            send_cptra_sts_txn = 1;
                        end
                        else if (ahb_txn.RnW == AHB_WRITE) begin
                            `uvm_error("PRED_AHB", {"Unexpected write to ",axs_reg.get_name()," register on AHB interface"})
                        end
                    end
                    "internal_nmi_vector": begin
                        if (ahb_txn.RnW == AHB_WRITE) begin
                            if (nmi_vector != data_active) begin
                                send_cptra_sts_txn = 1;
                                nmi_vector = data_active;
                            end
                        end
                    end
                    default: begin
                        `uvm_warning("PRED_AHB", $sformatf("Prediction for accesses to register '%s' unimplemented! Fix soc_ifc_predictor", axs_reg.get_name()))
                    end
                endcase
            end
            // Interrupt registers have 3-levels of ancestry back to reg_model top
            //                          2-levels of ancestry back to unique parent
            else if (axs_reg.get_parent().get_parent().get_name() == "soc_ifc_reg_rm") begin
                case (axs_reg.get_name()) inside
                    "global_intr_en_r": begin
                        if (ahb_txn.RnW == AHB_WRITE) begin
                            // Notif intr prediction
                            if (data_active[p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_lsb_pos()] &&
                                ~p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.get_mirrored_value() &&
                                |(p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_intr_en_r.get_mirrored_value() &
                                  p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.get_mirrored_value()))
                            begin
                                p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.predict(1'b1, -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_AHB_map);
                                send_cptra_sts_txn = 1'b1;
                            end

                            // Error intr prediction
                            if (data_active[p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.error_en.get_lsb_pos()] &&
                                ~p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.get_mirrored_value() &&
                                |(p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_intr_en_r.get_mirrored_value() &
                                  p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.get_mirrored_value()))
                            begin
                                p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.predict(1'b1, -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_AHB_map);
                                send_cptra_sts_txn = 1'b1;
                            end
                        end
                    end
                    "error_intr_en_r": begin
                        if (ahb_txn.RnW == AHB_WRITE) begin
                            if (p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.error_en.get_mirrored_value() &&
                                ~p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.get_mirrored_value() &&
                                |(data_active &
                                  p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.get_mirrored_value()))
                            begin
                                p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.predict(1'b1, -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_AHB_map);
                                send_cptra_sts_txn = 1'b1;
                            end
                        end
                    end
                    "notif_intr_en_r": begin
                        if (ahb_txn.RnW == AHB_WRITE) begin
                            if (p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_mirrored_value() &&
                                ~p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.get_mirrored_value() &&
                                |(data_active &
                                  p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.get_mirrored_value()))
                            begin
                                p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.predict(1'b1, -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_AHB_map);
                                send_cptra_sts_txn = 1'b1;
                            end
                        end
                    end
                    "error_global_intr_r": begin
                        if (ahb_txn.RnW == AHB_WRITE) begin
                            `uvm_warning("PRED_AHB", $sformatf("Unexpected write to %s will have no effect", axs_reg.get_name()))
                        end
                    end
                    "notif_global_intr_r": begin
                        if (ahb_txn.RnW == AHB_WRITE) begin
                            `uvm_warning("PRED_AHB", $sformatf("Unexpected write to %s will have no effect", axs_reg.get_name()))
                        end
                    end
                    "error_internal_intr_r": begin
                        if (ahb_txn.RnW == AHB_WRITE) begin
                            // If the write clears ALL pending interrupts, global intr signal will deassert
                            if (p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.error_en.get_mirrored_value() &&
                                data_active == (p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_intr_en_r.get_mirrored_value() &
                                                p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.get_mirrored_value()))
                            begin
                                p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.predict(1'b0, -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_AHB_map);
    //                            send_cptra_sts_txn = 1'b1; /* for deassertion of intr pending */
                            end
                        end
                    end
                    "notif_internal_intr_r": begin
                        if (ahb_txn.RnW == AHB_WRITE) begin
                            // If the write clears ALL pending interrupts, global intr signal will deassert
                            if (p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_mirrored_value() &&
                                data_active == (p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_intr_en_r.get_mirrored_value() &
                                                p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.get_mirrored_value()))
                            begin
                                p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.predict(1'b0, -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_AHB_map);
    //                            send_cptra_sts_txn = 1'b1; /* for deassertion of intr pending */
                            end
                        end
                    end
                    "error_intr_trig_r": begin
                        `uvm_fatal("FIXME", "FIXME")
                    end
                    "notif_intr_trig_r": begin
                        `uvm_fatal("FIXME", "FIXME")
                    end
                    "error_internal_intr_count_r",
                    "error_inv_dev_intr_count_r",
                    "error_cmd_fail_intr_count_r",
                    "error_bad_fuse_intr_count_r",
                    "error_iccm_blocked_intr_count_r",
                    "error_mbox_ecc_unc_intr_count_r",
                    "notif_cmd_avail_intr_count_r",
                    "notif_mbox_ecc_cor_intr_count_r",
                    "notif_debug_locked_intr_count_r": begin
                        `uvm_info("PRED_AHB", {"Access to register ", axs_reg.get_name(), " will have no effect on system"}, UVM_HIGH)
                    end
                    "error_internal_intr_count_incr_r",
                    "error_inv_dev_intr_count_incr_r",
                    "error_cmd_fail_intr_count_incr_r",
                    "error_bad_fuse_intr_count_incr_r",
                    "error_iccm_blocked_intr_count_incr_r",
                    "error_mbox_ecc_unc_intr_count_incr_r",
                    "notif_cmd_avail_intr_count_incr_r",
                    "notif_mbox_ecc_cor_intr_count_incr_r",
                    "notif_debug_locked_intr_count_incr_r": begin
                        `uvm_info("PRED_AHB", {"Access to register ", axs_reg.get_name(), " will have no effect on system"}, UVM_HIGH)
                    end
                    default: begin
                        `uvm_warning("PRED_AHB", $sformatf("Prediction for accesses to register '%s' unimplemented! Fix soc_ifc_predictor", axs_reg.get_name()))
                    end
                endcase
            end
            // Interrupt registers have 3-levels of ancestry back to reg_model top
            //                          2-levels of ancestry back to unique parent
            else if (axs_reg.get_parent().get_parent().get_name() == "sha512_acc_csr_rm") begin
                case (axs_reg.get_name()) inside
                    "global_intr_en_r": begin
                        `uvm_warning("PRED_AHB", $sformatf("Prediction for accesses to register '%s' unimplemented! Fix soc_ifc_predictor", axs_reg.get_name()))
                    end
                    "error_intr_en_r": begin
                        `uvm_warning("PRED_AHB", $sformatf("Prediction for accesses to register '%s' unimplemented! Fix soc_ifc_predictor", axs_reg.get_name()))
                    end
                    "notif_intr_en_r": begin
                        `uvm_warning("PRED_AHB", $sformatf("Prediction for accesses to register '%s' unimplemented! Fix soc_ifc_predictor", axs_reg.get_name()))
                    end
                    "error_global_intr_r": begin
                        if (ahb_txn.RnW == AHB_WRITE) begin
                            `uvm_warning("PRED_AHB", $sformatf("Unexpected write to %s will have no effect", axs_reg.get_name()))
                        end
                    end
                    "notif_global_intr_r": begin
                        if (ahb_txn.RnW == AHB_WRITE) begin
                            `uvm_warning("PRED_AHB", $sformatf("Unexpected write to %s will have no effect", axs_reg.get_name()))
                        end
                    end
                    "error_internal_intr_r": begin
                    end
                    "notif_internal_intr_r": begin
                    end
                    "error_intr_trig_r": begin
                        `uvm_fatal("FIXME", "FIXME")
                    end
                    "notif_intr_trig_r": begin
                        `uvm_fatal("FIXME", "FIXME")
                    end
                    default: begin
                        `uvm_warning("PRED_AHB", $sformatf("Prediction for accesses to register '%s' unimplemented! Fix soc_ifc_predictor", axs_reg.get_name()))
                    end
                endcase
            end
        end
    end// REG_AXS

    // Code for sending output transaction out through soc_ifc_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction
    // using either new() or create().  Broadcasting a transaction object more than once to either the
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_soc_ifc_sts_txn) begin
        populate_expected_soc_ifc_status_txn(soc_ifc_sb_ap_output_transaction);
        soc_ifc_sb_ap.write(soc_ifc_sb_ap_output_transaction);
        `uvm_info("PRED_AHB", "Transaction submitted through soc_ifc_sb_ap", UVM_MEDIUM)
    end
    // TODO
    // Code for sending output transaction out through cptra_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_cptra_sts_txn) begin
        populate_expected_cptra_status_txn(cptra_sb_ap_output_transaction);
        cptra_sb_ap.write(cptra_sb_ap_output_transaction);
        `uvm_info("PRED_AHB", "Transaction submitted through cptra_sb_ap", UVM_MEDIUM)
    end
    // Code for sending output transaction out through soc_ifc_sb_ahb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_ahb_txn) begin
        soc_ifc_sb_ahb_ap_output_transaction.copy(ahb_txn);
        soc_ifc_sb_ahb_ap_output_transaction.address = address_aligned;
        soc_ifc_sb_ahb_ap.write(soc_ifc_sb_ahb_ap_output_transaction);
        `uvm_info("PRED_AHB", "Transaction submitted through soc_ifc_sb_ahb_ap", UVM_MEDIUM)
    end
    // Code for sending output transaction out through soc_ifc_sb_apb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_apb_txn) begin
        soc_ifc_sb_apb_ap.write(soc_ifc_sb_apb_ap_output_transaction);
        `uvm_error("PRED_AHB", "NULL Transaction submitted through soc_ifc_sb_apb_ap")
    end
    // pragma uvmf custom ahb_slave_0_ae_predictor end
  endfunction

  // FUNCTION: write_apb5_slave_0_ae
  // Transactions received through apb5_slave_0_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_apb5_slave_0_ae(mvc_sequence_item_base t);
    // pragma uvmf custom apb5_slave_0_ae_predictor begin
    apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT, apb5_master_0_params::APB3_PADDR_BIT_WIDTH, apb5_master_0_params::APB3_PWDATA_BIT_WIDTH, apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_txn;
    uvm_reg            axs_reg;
    // Flags control whether each transaction is sent to scoreboard
    bit send_soc_ifc_sts_txn = 0;
    bit send_cptra_sts_txn = 0;
    bit send_ahb_txn = 0;
    bit send_apb_txn = 1;
    apb5_slave_0_ae_debug = t;

    `uvm_info("PRED_APB", "Transaction Received through apb5_slave_0_ae", UVM_MEDIUM)
    `uvm_info("PRED_APB", {"            Data: ",t.convert2string()}, UVM_FULL)

    // Construct one of each output transaction type.
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");
    cptra_sb_ap_output_transaction = cptra_sb_ap_output_transaction_t::type_id::create("cptra_sb_ap_output_transaction");
    soc_ifc_sb_ahb_ap_output_transaction = soc_ifc_sb_ahb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ahb_ap_output_transaction");
    soc_ifc_sb_apb_ap_output_transaction = soc_ifc_sb_apb_ap_output_transaction_t::type_id::create("soc_ifc_sb_apb_ap_output_transaction");

    $cast(apb_txn, t);
    axs_reg = p_soc_ifc_APB_map.get_reg_by_offset(apb_txn.addr);

    if (axs_reg == null) begin
        `uvm_error("PRED_APB", $sformatf("APB transaction to address: 0x%x decodes to null from soc_ifc_APB_map", apb_txn.addr))
    end
    else begin
        `uvm_info("PRED_APB", {"Detected access to register: ", axs_reg.get_full_name()}, UVM_MEDIUM)
        case (axs_reg.get_name()) inside
            "mbox_lock": begin
                if (apb_txn.read_or_write == APB3_TRANS_READ && apb_txn.addr_user inside mbox_valid_users && !apb_txn.slave_err) begin
                    // Reading mbox_lock when it is already locked has no effect, so
                    // only calculate predictions on acquiring lock (rdata == 0)
                    if (~apb_txn.rd_data[p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_lsb_pos()]) begin
                        `uvm_info("PRED_APB", $sformatf("Predicting new value [0x%x] for mbox_user as APB agent acquires lock",apb_txn.addr_user), UVM_HIGH)
                        p_soc_ifc_rm.mbox_csr_rm.mbox_user.predict(uvm_reg_data_t'(apb_txn.addr_user),
                                                                   -1,
                                                                   UVM_PREDICT_DIRECT,
                                                                   UVM_FRONTDOOR,
                                                                   p_soc_ifc_APB_map);
                        p_soc_ifc_rm.mbox_csr_rm.mbox_status.soc_has_lock.predict(uvm_reg_data_t'(1),
                                                                                  -1,
                                                                                  UVM_PREDICT_DIRECT,
                                                                                  UVM_FRONTDOOR,
                                                                                  p_soc_ifc_APB_map);
                    end
                end
                else if (apb_txn.read_or_write == APB3_TRANS_READ) begin
                    // RS access policy wants to update lock to 1 on a read, but if the PAUSER value is invalid
                    // lock will not be set. It will hold the previous value.
                    p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.predict(p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value(),
                                                                    -1,
                                                                    UVM_PREDICT_DIRECT,
                                                                    UVM_FRONTDOOR,
                                                                    p_soc_ifc_APB_map);
                end
            end
            "mbox_execute": begin
                // FIXME needs more intelligence for tracking mailbox protocol
                // NOTE this logic breaks during the PAUSER test, because mbox allows write to mbox_execute as long as PAUSER is any valid value, not specifically the locked PAUSER, when mbox FSM is in MBOX_EXECUTE_SOC
                // See ADO work item 454525
                if (apb_txn.read_or_write == APB3_TRANS_WRITE && apb_txn.wr_data == 0 && apb_txn.addr_user == p_soc_ifc_rm.mbox_csr_rm.mbox_user.get_mirrored_value()) begin
                    send_soc_ifc_sts_txn = mailbox_data_avail;
                    mailbox_data_avail = 1'b0;
                end
                else if (apb_txn.read_or_write == APB3_TRANS_WRITE && apb_txn.wr_data == 1 && apb_txn.addr_user == p_soc_ifc_rm.mbox_csr_rm.mbox_user.get_mirrored_value()) begin
                    p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_cmd_avail_intr_count_r.cnt.predict(p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_cmd_avail_intr_count_r.cnt.get_mirrored_value() + uvm_reg_data_t'(1), -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_AHB_map); /* AHB-access only, use AHB map*/
                    p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_cmd_avail_sts.predict(1'b1, -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_AHB_map); /* AHB-access only, use AHB map*/
                    if (p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_mirrored_value() &&
                        p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_intr_en_r.notif_cmd_avail_en.get_mirrored_value())
                    begin
                        `uvm_info("PRED_APB", "Write to mbox_execute triggers interrupt output", UVM_LOW)
                        p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.predict(1'b1, -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_AHB_map); /* AHB-access only, use AHB map*/
                        send_cptra_sts_txn = 1;
                    end
                    else begin
                        `uvm_info("PRED_APB",
                                  $sformatf("Write to mbox_execute does not trigger interrupt output due to global_intr_en: [%x] and notif_cmd_avail_en: [%x]",
                                            p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_mirrored_value(),
                                            p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_intr_en_r.notif_cmd_avail_en.get_mirrored_value()),
                                  UVM_LOW)
                    end
                end
                else begin
                    `uvm_info("PRED_APB", $sformatf("In access to mbox_execute, but no predictions made for activity.... FIXME? addr_user: 0x%x, valid_users: %p, mbox_user-mirrored: %p", apb_txn.addr_user, mbox_valid_users, p_soc_ifc_rm.mbox_csr_rm.mbox_user.get_mirrored_value()), UVM_LOW)
                end
            end
            ["CPTRA_VALID_PAUSER[0]":"CPTRA_VALID_PAUSER[4]"]: begin
                int idx = axs_reg.get_offset(p_soc_ifc_APB_map) - p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_VALID_PAUSER[0].get_offset(p_soc_ifc_APB_map);
                idx /= 4;
                if (mbox_valid_users_locked[idx] && apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    `uvm_error("PRED_APB", {"Write attempted to locked register: ", axs_reg.get_name()})
                end
                else if (apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    mbox_valid_users[idx] = apb_txn.wr_data;
                end
            end
            ["CPTRA_PAUSER_LOCK[0]":"CPTRA_PAUSER_LOCK[4]"]: begin
                int idx = axs_reg.get_offset(p_soc_ifc_APB_map) - p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_PAUSER_LOCK[0].get_offset(p_soc_ifc_APB_map);
                idx /= 4;
                if (mbox_valid_users_locked[idx] && apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    `uvm_error("PRED_APB", {"Write attempted to locked register: ", axs_reg.get_name()})
                end
                else if (apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    mbox_valid_users_locked[idx] |= apb_txn.wr_data[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_PAUSER_LOCK[idx].LOCK.get_lsb_pos()];
                    `uvm_info("PRED_APB", $sformatf("mbox_valid_users_locked[%d] set to 0x%x, mbox_valid_users[%d] has value: 0x%x", idx, mbox_valid_users_locked[idx], idx, mbox_valid_users[idx]), UVM_MEDIUM)
                end
                else begin
                    `uvm_info("PRED_APB", $sformatf("mbox_valid_users_locked[%d] read value 0x%x, mbox_valid_users[%d] has value: 0x%x", idx, mbox_valid_users_locked[idx], idx, mbox_valid_users[idx]), UVM_HIGH)
                end
            end
            "CPTRA_FUSE_WR_DONE": begin
                if (apb_txn.wr_data != axs_reg.get() && apb_txn.read_or_write == APB3_TRANS_WRITE)
                    `uvm_error("PRED_APB", $sformatf("APB transaction with data: 0x%x, write: %p, may not match reg model value: %x", apb_txn.wr_data, apb_txn.read_or_write, axs_reg.get()))
                // Only expect a status transaction if this fuse download is occuring during boot sequence // FIXME
                // Even after a warm reset, we expect a write to this register (although the write is dropped)
                if (noncore_rst_out_asserted && (apb_txn.wr_data == 1/*FIXME hardcoded*/) && apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    noncore_rst_out_asserted =  bootfsm_breakpoint;
                    uc_rst_out_asserted      =  bootfsm_breakpoint;
                    send_cptra_sts_txn       = !bootfsm_breakpoint;
                    p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_fuses.predict(1'b0, -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_APB_map);
                    send_soc_ifc_sts_txn = 1'b1;
                    fuse_update_enabled = 1'b0;
                end
            end
            "CPTRA_BOOTFSM_GO": begin
                // FIXME -- use reg predictor somehow?
                uvm_reg_data_t fuse_wr_done = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FUSE_WR_DONE.get();

                if (noncore_rst_out_asserted &&
                    bootfsm_breakpoint &&
                    apb_txn.read_or_write == APB3_TRANS_WRITE &&
                    (apb_txn.wr_data[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_BOOTFSM_GO.GO.get_lsb_pos()])) begin

                    bootfsm_breakpoint = 1'b0;
                    if (fuse_wr_done[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FUSE_WR_DONE.done.get_lsb_pos()]) begin
                        noncore_rst_out_asserted = 1'b0;
                        uc_rst_out_asserted      = 1'b0;
                        send_cptra_sts_txn       = 1'b1;
                    end

                end
            end
            ["fuse_uds_seed[0]" :"fuse_uds_seed[9]" ],
            ["fuse_uds_seed[10]":"fuse_uds_seed[11]"]: begin
//                // FIXME -- use reg predictor somehow?
//                uvm_reg_data_t data = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FUSE_WR_DONE.get();
//                if (!data[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FUSE_WR_DONE.done.get_lsb_pos()]) begin
                if (fuse_update_enabled) begin
                    send_cptra_sts_txn       = 1'b1;
                end
            end
            ["fuse_field_entropy[0]" :"fuse_field_entropy[7]" ]: begin
//                // FIXME -- use reg predictor somehow?
//                uvm_reg_data_t data = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FUSE_WR_DONE.get();
//                if (!data[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FUSE_WR_DONE.done.get_lsb_pos()]) begin
                if (fuse_update_enabled) begin
                    send_cptra_sts_txn       = 1'b1;
                end
            end
            default: begin
                `uvm_warning("PRED_APB", $sformatf("Prediction for accesses to register '%s' unimplemented! Fix soc_ifc_predictor", axs_reg.get_name()))
            end
        endcase
    end

    // Code for sending output transaction out through soc_ifc_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction
    // using either new() or create().  Broadcasting a transaction object more than once to either the
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_soc_ifc_sts_txn) begin
        populate_expected_soc_ifc_status_txn(soc_ifc_sb_ap_output_transaction);
        soc_ifc_sb_ap.write(soc_ifc_sb_ap_output_transaction);
        `uvm_info("PRED_APB", "Transaction submitted through soc_ifc_sb_ap", UVM_MEDIUM)
    end
    // Code for sending output transaction out through cptra_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_cptra_sts_txn) begin
        populate_expected_cptra_status_txn(cptra_sb_ap_output_transaction);
        cptra_sb_ap.write(cptra_sb_ap_output_transaction);
        `uvm_info("PRED_APB", "Transaction submitted through cptra_sb_ap", UVM_MEDIUM)
    end
    // Code for sending output transaction out through soc_ifc_sb_ahb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_ahb_txn) begin
        soc_ifc_sb_ahb_ap.write(soc_ifc_sb_ahb_ap_output_transaction);
        `uvm_error("PRED_APB", "NULL Transaction submitted through soc_ifc_sb_ahb_ap")
    end
    // Code for sending output transaction out through soc_ifc_sb_apb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_apb_txn) begin
        soc_ifc_sb_apb_ap_output_transaction.copy(apb_txn);
        soc_ifc_sb_apb_ap.write(soc_ifc_sb_apb_ap_output_transaction);
        `uvm_info("PRED_APB", "Transaction submitted through soc_ifc_sb_apb_ap", UVM_MEDIUM)
    end
    // pragma uvmf custom apb5_slave_0_ae_predictor end
  endfunction


endclass

// pragma uvmf custom external begin
function bit soc_ifc_predictor::soc_ifc_status_txn_expected_after_warm_reset();
    /* FIXME calculate this from the reg-model somehow? */
    return p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_fuses.get_mirrored_value() || ready_for_fw_push || ready_for_runtime || mailbox_data_avail || |generic_output_wires /*|| trng_req_pending*/; /* only expect a soc_ifc_status_transaction if some signal will transition */
endfunction

function bit soc_ifc_predictor::cptra_status_txn_expected_after_warm_reset();
    /* FIXME calculate this from the reg-model somehow? */
    return !noncore_rst_out_asserted                                                                  ||
           !uc_rst_out_asserted                                                                       ||
           p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.get_mirrored_value() ||
           p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.get_mirrored_value() ||
           sha_err_intr_pending                                                                       ||
           sha_notif_intr_pending                                                                     ||
           iccm_locked                                                                                ||
           |nmi_vector;
endfunction

task soc_ifc_predictor::handle_reset(input string kind = "HARD");
    uvm_object obj_triggered;
    reset_flag kind_predicted;
    reset_flag kind_handled;

    kind_handled = kind == "HARD" ? hard_reset_flag :
                   kind == "SOFT" ? soft_reset_flag :
                                    null;
    reset_handled.trigger(kind_handled);
    reset_predicted.wait_trigger_data(obj_triggered);
    if (!$cast(kind_predicted, obj_triggered))
        `uvm_fatal("SOC_IFC_PRED", "Failed to retrieve triggered reset_flag")
    if (kind_handled != kind_predicted)
        `uvm_error("SOC_IFC_PRED", $sformatf("handle_reset called with different reset type [%s] than was processed in predictor [%s]!", kind_handled.get_name(), kind_predicted.get_name()))
    reset_predicted.reset();
endtask

function void soc_ifc_predictor::predict_reset(input string kind = "HARD");
    `uvm_info("SOC_IFC_PRED", $sformatf("Predicting reset of kind: %p", kind), UVM_LOW)

    // Predict value changes due to reset
    soc_ifc_rst_in_asserted = 1'b1;
    noncore_rst_out_asserted = 1'b1;
    uc_rst_out_asserted = 1'b1;
    p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_fuses.predict(1'b0, -1, UVM_PREDICT_DIRECT, UVM_FRONTDOOR, p_soc_ifc_APB_map);
    // FIXME: Do a reg-model reset and then extract these from the reg_model???
    ready_for_fw_push = 1'b0;
    ready_for_runtime = 1'b0;
    nmi_vector = '0;
    iccm_locked = 1'b0;
    mailbox_data_avail = 1'b0;
    sha_err_intr_pending = 1'b0;
    sha_notif_intr_pending = 1'b0;
    generic_output_wires = '0;

    // FIXME get rid of this variable?
    mbox_valid_users        = '{p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_VALID_PAUSER[4].PAUSER.get_reset(kind),
                                p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_VALID_PAUSER[3].PAUSER.get_reset(kind),
                                p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_VALID_PAUSER[2].PAUSER.get_reset(kind),
                                p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_VALID_PAUSER[1].PAUSER.get_reset(kind),
                                p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_VALID_PAUSER[0].PAUSER.get_reset(kind)};
    mbox_valid_users_locked =  {p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_PAUSER_LOCK[4].LOCK.get_reset(kind),
                                p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_PAUSER_LOCK[3].LOCK.get_reset(kind),
                                p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_PAUSER_LOCK[2].LOCK.get_reset(kind),
                                p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_PAUSER_LOCK[1].LOCK.get_reset(kind),
                                p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_PAUSER_LOCK[0].LOCK.get_reset(kind)};

    if (kind == "HARD") begin
        fuse_update_enabled = 1'b1; // Fuses only latch new values from APB write after a cold-reset (which clears CPTRA_FUSE_WR_DONE)
    end

    // HARD reset is the default for a reg-model
    // FIXME SOFT reset is not fully defined for our reg-model yet
    // FIXME move this to env?
    p_soc_ifc_rm.reset(kind);

    soc_ifc_status_txn_key = 0;
    cptra_status_txn_key = 0;
endfunction

function bit soc_ifc_predictor::soc_ifc_status_txn_expected_after_cold_reset();
    return soc_ifc_status_txn_expected_after_warm_reset(); /* warm reset is expected in conjunction with cold */
endfunction

function bit soc_ifc_predictor::cptra_status_txn_expected_after_cold_reset();
    return cptra_status_txn_expected_after_warm_reset(); /* warm reset is expected in conjunction with cold */
endfunction

function bit [`CLP_OBF_FE_DWORDS-1:0] [31:0] soc_ifc_predictor::get_expected_obf_field_entropy();
    byte ii;
    bit [`CLP_OBF_FE_DWORDS-1:0] [31:0] fe;
    for (ii=0; ii < `CLP_OBF_FE_DWORDS; ii++) begin
        fe[ii] = p_soc_ifc_rm.soc_ifc_reg_rm.fuse_field_entropy[ii].get_mirrored_value();
    end
    return fe;
endfunction

function bit [`CLP_OBF_UDS_DWORDS-1:0] [31:0] soc_ifc_predictor::get_expected_obf_uds_seed();
    byte ii;
    bit [`CLP_OBF_UDS_DWORDS-1:0] [31:0] uds;
    for (ii=0; ii < `CLP_OBF_UDS_DWORDS; ii++) begin
        uds[ii] = p_soc_ifc_rm.soc_ifc_reg_rm.fuse_uds_seed[ii].get_mirrored_value();
    end
    return uds;
endfunction

function void soc_ifc_predictor::populate_expected_soc_ifc_status_txn(ref soc_ifc_sb_ap_output_transaction_t txn);
    txn.ready_for_fuses                    = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_fuses.get_mirrored_value();
    txn.ready_for_fw_push                  = this.ready_for_fw_push;
    txn.ready_for_runtime                  = this.ready_for_runtime;
    txn.mailbox_data_avail                 = this.mailbox_data_avail;
    txn.mailbox_flow_done                  = this.mailbox_flow_done; // FIXME
    txn.cptra_error_fatal_intr_pending     = 1'b0; // FIXME
    txn.cptra_error_non_fatal_intr_pending = 1'b0; // FIXME
    txn.trng_req_pending                   = 1'b0; // FIXME
    txn.generic_output_val                 = this.generic_output_wires;
    txn.set_key(soc_ifc_status_txn_key++);
endfunction

function void soc_ifc_predictor::populate_expected_cptra_status_txn(ref cptra_sb_ap_output_transaction_t txn);
    txn.noncore_rst_asserted       = this.noncore_rst_out_asserted;
    txn.uc_rst_asserted            = this.uc_rst_out_asserted;
    txn.soc_ifc_err_intr_pending   = p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.get_mirrored_value();
    txn.soc_ifc_notif_intr_pending = p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.get_mirrored_value();
    txn.sha_err_intr_pending       = this.sha_err_intr_pending;
    txn.sha_notif_intr_pending     = this.sha_notif_intr_pending;
    txn.cptra_obf_key_reg          = this.cptra_obf_key_reg;
    txn.obf_field_entropy          = this.get_expected_obf_field_entropy();
    txn.obf_uds_seed               = this.get_expected_obf_uds_seed();
    txn.nmi_vector                 = this.nmi_vector;
    txn.iccm_locked                = this.iccm_locked;
    txn.set_key(cptra_status_txn_key++);
endfunction

// pragma uvmf custom external end

