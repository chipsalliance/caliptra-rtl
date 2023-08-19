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
//   mbox_sram_agent_ae receives transactions of type  mbox_sram_transaction
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
  uvm_analysis_imp_mbox_sram_agent_ae #(mbox_sram_transaction, soc_ifc_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) mbox_sram_agent_ae;
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

  uvm_analysis_port #(soc_ifc_ctrl_transaction) soc_ifc_cov_ap;
  uvm_analysis_port #(cptra_ctrl_transaction  ) cptra_cov_ap;


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
  mbox_sram_transaction mbox_sram_agent_ae_debug;
  mvc_sequence_item_base ahb_slave_0_ae_debug;
  mvc_sequence_item_base apb5_slave_0_ae_debug;


  // pragma uvmf custom class_item_additional begin
  uvm_analysis_port #(mvc_sequence_item_base) soc_ifc_ahb_reg_ap;
  uvm_analysis_port #(mvc_sequence_item_base) soc_ifc_apb_reg_ap;

  bit cptra_pwrgood_asserted = 1'b0;
  bit soc_ifc_rst_in_asserted = 1'b1;
  bit noncore_rst_out_asserted = 1'b1;
  bit uc_rst_out_asserted = 1'b1;
  bit fw_update_rst_window = 1'b0;
  bit soc_ifc_error_intr_pending = 1'b0;
  bit soc_ifc_notif_intr_pending = 1'b0;
  bit sha_err_intr_pending = 1'b0; // TODO
  bit sha_notif_intr_pending = 1'b0; // TODO
  bit timer_intr_pending = 1'b1;
  bit nmi_intr_pending = 1'b0;
  bit cptra_error_fatal = 1'b0;
  bit cptra_error_non_fatal = 1'b0;
  bit fuse_update_enabled = 1'b1;
  bit ready_for_fw_push = 1'b0; // TODO
  bit ready_for_runtime = 1'b0;
  bit mailbox_flow_done = 1'b0;
  bit clk_gate_active         = 1'b1; // TODO
  bit rdc_clk_gate_active     = 1'b1;
  bit soc_ifc_clk_gate_active = 1'b1; // TODO

  bit mailbox_data_avail = 1'b0;

  int datain_count = 0;
  int dataout_count = 0;

  bit [31:0] nmi_vector = 32'h0;
  bit iccm_locked = 1'b0;
  bit [`CLP_OBF_KEY_DWORDS-1:0] [31:0] cptra_obf_key_reg = '{default:32'h0}; // FIXME use reg-model value?
  security_state_t security_state = '{debug_locked: 1'b1, device_lifecycle: DEVICE_UNPROVISIONED};
  bit bootfsm_breakpoint = 1'b0;
  bit cptra_in_dbg_or_manuf_mode = 1'b0;
  int unsigned fw_update_wait_count = 0;

  bit [63:0] generic_output_wires = 64'h0;

  bit [apb5_master_0_params::PAUSER_WIDTH-1:0] mbox_valid_users [6]    = '{default: '1};
  bit [4:0]                                    mbox_valid_users_locked = 5'b00000;

  bit trng_data_req = 1'b0;
  bit [apb5_master_0_params::APB3_PWDATA_BIT_WIDTH-1:0] trng_data [12]       = '{default: '0}; // FIXME what is this used for? Can we just use the reg-model mirrors instead?

  // For collecting coverage
  mbox_steps_s prev_step = '{null_action: 1'b1, default: 1'b0};
  mbox_steps_s next_step = '{null_action: 1'b1, default: 1'b0};

  soc_ifc_reg_model_top  p_soc_ifc_rm;
  uvm_reg_map p_soc_ifc_APB_map; // Block map
  uvm_reg_map p_soc_ifc_AHB_map; // Block map

  int unsigned soc_ifc_status_txn_key = 0;
  int unsigned cptra_status_txn_key = 0;

  uvm_event reset_predicted;
  uvm_event reset_handled;

  reset_flag hard_reset_flag;
  reset_flag soft_reset_flag;

  //WDT vars:
  bit [63:0] t1_count, t2_count;
  bit wdt_error_intr_sent;
  bit wdt_t2_error_intr_sent;
  bit wdt_nmi_intr_sent;
  bit reset_wdt_count;
  bit wdt_t1_restart;
  bit wdt_t2_restart;

  extern task          poll_and_run_delay_jobs();
  extern function void send_delayed_expected_transactions();
  extern function bit  check_mbox_no_lock_error(soc_ifc_sb_apb_ap_output_transaction_t txn, uvm_reg axs_reg);
  extern function bit  check_mbox_ooo_error(soc_ifc_sb_apb_ap_output_transaction_t txn, uvm_reg axs_reg);
  extern function bit  check_mbox_inv_user_error(soc_ifc_sb_apb_ap_output_transaction_t txn, uvm_reg axs_reg);
  extern task          update_mtime_mirrors();
  extern task          mtime_counter_task();
  extern function bit  mtime_lt_mtimecmp();
  extern task          wdt_counter_task();
  extern task          wdt_counter_trial();
  extern function bit  valid_requester(input uvm_transaction txn);
  extern function bit  valid_receiver(input uvm_transaction txn);
  extern function bit  sha_valid_user(input uvm_transaction txn);
  extern function void predict_boot_wait_boot_done();
  extern task          handle_reset(input string kind = "HARD");
  extern function void predict_reset(input string kind = "HARD");
  extern function bit  soc_ifc_status_txn_expected_after_noncore_reset();
  extern function bit  cptra_status_txn_expected_after_noncore_reset();
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
  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

  // FUNCTION: build_phase
  virtual function void build_phase (uvm_phase phase);


    soc_ifc_ctrl_agent_ae = new("soc_ifc_ctrl_agent_ae", this);
    cptra_ctrl_agent_ae = new("cptra_ctrl_agent_ae", this);
    mbox_sram_agent_ae = new("mbox_sram_agent_ae", this);
    ahb_slave_0_ae = new("ahb_slave_0_ae", this);
    apb5_slave_0_ae = new("apb5_slave_0_ae", this);
    soc_ifc_sb_ap = new("soc_ifc_sb_ap", this );
    cptra_sb_ap = new("cptra_sb_ap", this );
    soc_ifc_sb_ahb_ap = new("soc_ifc_sb_ahb_ap", this );
    soc_ifc_sb_apb_ap = new("soc_ifc_sb_apb_ap", this );
    soc_ifc_ahb_reg_ap = new("soc_ifc_ahb_reg_ap", this);
    soc_ifc_apb_reg_ap = new("soc_ifc_apb_reg_ap", this);
    soc_ifc_cov_ap = new("soc_ifc_cov_ap", this );
    cptra_cov_ap = new("cptra_cov_ap", this );
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

  task run_phase(uvm_phase phase);
    fork
        poll_and_run_delay_jobs();
        mtime_counter_task();
        wdt_counter_task();
    join_none
    super.run_phase(phase);
  endtask

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
    `uvm_info("PRED_SOC_IFC_CTRL", {"            Data: ",t.convert2string()}, UVM_HIGH)
    // Construct one of each output transaction type.
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");
    cptra_sb_ap_output_transaction = cptra_sb_ap_output_transaction_t::type_id::create("cptra_sb_ap_output_transaction");
    soc_ifc_sb_ahb_ap_output_transaction = soc_ifc_sb_ahb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ahb_ap_output_transaction");
    soc_ifc_sb_apb_ap_output_transaction = soc_ifc_sb_apb_ap_output_transaction_t::type_id::create("soc_ifc_sb_apb_ap_output_transaction");


    // FIXME account for security_state/scan_mode below

    cptra_pwrgood_asserted = t.set_pwrgood;

    // Initial boot
    if (!t.set_pwrgood && soc_ifc_rst_in_asserted) begin
        cptra_obf_key_reg = t.cptra_obf_key_rand;
        for (byte ii=0; ii < 8; ii++) begin
            // Change from reset value means we expect a transaction
            send_cptra_sts_txn |= (t.cptra_obf_key_rand[ii] != p_soc_ifc_rm.soc_ifc_reg_rm.internal_obf_key[ii].key.get_reset());
        end
        if (!t.assert_rst)
            `uvm_fatal("PRED_SOC_IFC_CTRL", "Bad initial boot with cptra_rst_b deasserted")
        if (!p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs.boot_idle)
            `uvm_fatal("PRED_SOC_IFC_CTRL", $sformatf("Bad initial boot FSM prediction: %p", p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs))
        if (reset_handled.is_on()) begin
            `uvm_error("PRED_SOC_IFC_CTRL", "reset_handled event unexpectedly set on receiving soc_ifc_ctrl_transaction for initial boot reset")
            reset_handled.reset();
        end
        predict_reset("HARD");
        reset_predicted.trigger(hard_reset_flag/*"HARD"*/);
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
        reset_predicted.reset();
        // No new signal predictions since it was all done on Cold reset assertion.
        // But trigger the soft reset event to indicate to the predict_reset delay spinoff task
        // that the soft reset is done (once cptra_rst_b deasserts)
        reset_predicted.trigger(soft_reset_flag/*"SOFT"*/);
        `uvm_info("PRED_SOC_IFC_CTRL", $sformatf("In response to cold_reset deassertion, send_cptra_sts_txn: %d", send_cptra_sts_txn), UVM_NONE)
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
            p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_fuses.predict(1'b1);
            cptra_in_dbg_or_manuf_mode = ~t.security_state.debug_locked || t.security_state.device_lifecycle == DEVICE_MANUFACTURING;
            bootfsm_breakpoint = t.set_bootfsm_breakpoint && cptra_in_dbg_or_manuf_mode;
            reset_predicted.reset();
            send_soc_ifc_sts_txn = 1;
            send_cptra_sts_txn = 0; // cptra sts transaction not expected until after CPTRA_FUSE_WR_DONE
            reset_wdt_count = 1'b0;
            fork
                configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(6); // FIXME, correct delay value?
                rdc_clk_gate_active = 1'b0;
            join_none
            `uvm_info("PRED_SOC_IFC_CTRL", $sformatf("In response to warm_reset deassertion, send_soc_ifc_sts_txn: %d", send_soc_ifc_sts_txn), UVM_NONE)
        end
        // Normal operation
        else begin
            //TODO this block needs more logic
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

    if (1/*FIXME*/) begin
        // Forward the received transaction on to the coverage subscriber
        soc_ifc_cov_ap.write(t);
        `uvm_info("PRED_SOC_IFC_CTRL", "Transaction submitted through soc_ifc_cov_ap", UVM_MEDIUM)
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
    `uvm_info("PRED_CPTRA_CTRL", {"            Data: ",t.convert2string()}, UVM_HIGH)
    // Construct one of each output transaction type.
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");
    cptra_sb_ap_output_transaction = cptra_sb_ap_output_transaction_t::type_id::create("cptra_sb_ap_output_transaction");
    soc_ifc_sb_ahb_ap_output_transaction = soc_ifc_sb_ahb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ahb_ap_output_transaction");
    soc_ifc_sb_apb_ap_output_transaction = soc_ifc_sb_apb_ap_output_transaction_t::type_id::create("soc_ifc_sb_apb_ap_output_transaction");

    if (t.iccm_axs_blocked) begin
        // Error caused by blocked ICCM write causes intr bit to set
        //  - Use UVM_PREDICT_READ kind so that all the callbacks associated with
        //    notif_cmd_avail_sts are also called to detect interrupt pin assertion
        //  - Use UVM_PREDICT_READ instead of UVM_PREDICT_WRITE so that
        //    "do_predict" bypasses the access-check and does not enforce W1C
        //    behavior on this attempt to set interrupt status to 1
        p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.error_iccm_blocked_sts.predict(1'b1, -1, UVM_PREDICT_READ, UVM_PREDICT, p_soc_ifc_AHB_map); /* AHB-access only, use AHB map*/
    end
    if (t.assert_clear_secrets) begin
        foreach (p_soc_ifc_rm.soc_ifc_reg_rm.internal_obf_key[ii]) p_soc_ifc_rm.soc_ifc_reg_rm.internal_obf_key[ii].key.reset();
        foreach (p_soc_ifc_rm.soc_ifc_reg_rm.fuse_field_entropy[ii]) p_soc_ifc_rm.soc_ifc_reg_rm.fuse_field_entropy[ii].seed.reset();
        foreach (p_soc_ifc_rm.soc_ifc_reg_rm.fuse_uds_seed[ii]) p_soc_ifc_rm.soc_ifc_reg_rm.fuse_uds_seed[ii].seed.reset;
        this.cptra_obf_key_reg = '{default:32'h0};
        send_cptra_sts_txn = 1'b1;
        `uvm_info("PRED_CPTRA_CTRL", "Received transaction with clear secrets set! Resetting Caliptra model secrets", UVM_MEDIUM)
    end
    if (t.pulse_rv_ecc_error) begin
        `uvm_error("PRED_CPTRA_CTRL", "Unimplemented predictor for signaling RISCV SRAM ECC Errors")
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

    if (1/*FIXME*/) begin
        // Forward the received transaction on to the coverage subscriber
        cptra_cov_ap.write(t);
        `uvm_info("PRED_CPTRA_CTRL", "Transaction submitted through cptra_cov_ap", UVM_MEDIUM)
    end
    // pragma uvmf custom cptra_ctrl_agent_ae_predictor end
  endfunction

  // FUNCTION: write_mbox_sram_agent_ae
  // Transactions received through mbox_sram_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_mbox_sram_agent_ae(mbox_sram_transaction t);
    // pragma uvmf custom mbox_sram_agent_ae_predictor begin
    // Flags control whether each transaction is sent to scoreboard
    bit send_soc_ifc_sts_txn = 0;
    bit send_cptra_sts_txn = 0;
    bit send_ahb_txn = 0;
    bit send_apb_txn = 0;

    mbox_sram_agent_ae_debug = t;
    `uvm_info("PRED_MBOX_SRAM", "Transaction Received through mbox_sram_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED_MBOX_SRAM", {"            Data: ",t.convert2string()}, UVM_HIGH)
    // Construct one of each output transaction type.
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");
    cptra_sb_ap_output_transaction = cptra_sb_ap_output_transaction_t::type_id::create("cptra_sb_ap_output_transaction");
    soc_ifc_sb_ahb_ap_output_transaction = soc_ifc_sb_ahb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ahb_ap_output_transaction");
    soc_ifc_sb_apb_ap_output_transaction = soc_ifc_sb_apb_ap_output_transaction_t::type_id::create("soc_ifc_sb_apb_ap_output_transaction");

    if (t.is_read && t.ecc_double_bit_error) begin
        p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.error_mbox_ecc_unc_sts.predict(1'b1, -1, UVM_PREDICT_READ, UVM_PREDICT, p_soc_ifc_AHB_map); /* AHB-access only, use AHB map*/
        `uvm_info("PRED_MBOX_SRAM", "Received read transaction with Double bit ECC corruption, triggering the err interrupt", UVM_MEDIUM)
    end
    else if (t.is_read && t.ecc_single_bit_error) begin
        p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_mbox_ecc_cor_sts.predict(1'b1, -1, UVM_PREDICT_READ, UVM_PREDICT, p_soc_ifc_AHB_map); /* AHB-access only, use AHB map*/
        `uvm_info("PRED_MBOX_SRAM", "Received read transaction with Single bit ECC corruption, triggering the notification interrupt", UVM_MEDIUM)
    end
    else begin
        `uvm_info("PRED_MBOX_SRAM", "Received mailbox SRAM transaction does not cause a system state change prediction", UVM_FULL)
    end
    // TODO HW_ERROR_NON_FATAL activity?

    // Code for sending output transaction out through soc_ifc_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_soc_ifc_sts_txn) begin
        populate_expected_soc_ifc_status_txn(soc_ifc_sb_ap_output_transaction);
        soc_ifc_sb_ap.write(soc_ifc_sb_ap_output_transaction);
        `uvm_error("PRED_MBOX_SRAM", "NULL Transaction submitted through soc_ifc_sb_ap")
    end
    // Code for sending output transaction out through cptra_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_cptra_sts_txn) begin
        populate_expected_cptra_status_txn(cptra_sb_ap_output_transaction);
        cptra_sb_ap.write(cptra_sb_ap_output_transaction);
        `uvm_error("PRED_MBOX_SRAM", "NULL Transaction submitted through cptra_sb_ap")
    end
    // Code for sending output transaction out through soc_ifc_sb_ahb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_ahb_txn) begin
        soc_ifc_sb_ahb_ap.write(soc_ifc_sb_ahb_ap_output_transaction);
        `uvm_error("PRED_MBOX_SRAM", "NULL Transaction submitted through soc_ifc_sb_ahb_ap")
    end
    // Code for sending output transaction out through soc_ifc_sb_apb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_apb_txn) begin
        soc_ifc_sb_apb_ap.write(soc_ifc_sb_apb_ap_output_transaction);
        `uvm_error("PRED_MBOX_SRAM", "NULL Transaction submitted through soc_ifc_sb_apb_ap")
    end
    // pragma uvmf custom mbox_sram_agent_ae_predictor end
  endfunction

  // FUNCTION: write_ahb_slave_0_ae
  // Transactions received through ahb_slave_0_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_ahb_slave_0_ae(mvc_sequence_item_base t);
    // pragma uvmf custom ahb_slave_0_ae_predictor begin
    ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_txn;
    uvm_reg axs_reg;
    uvm_mem axs_mem;
    bit do_reg_prediction = 1;
    bit [SOC_IFC_DATA_W-1:0] data_active;
    bit [ahb_lite_slave_0_params::AHB_WDATA_WIDTH-1:0] address_aligned;
    // Flags control whether each transaction is sent to scoreboard
    bit send_soc_ifc_sts_txn = 0;
    bit send_cptra_sts_txn = 0;
    bit send_ahb_txn = 1;
    bit send_apb_txn = 0;
    bit wdt_cascade = 0;
    bit wdt_independent = 0;
    bit wdt_t1_timeout = 0;
    bit wdt_t2_timeout = 0;
    ahb_slave_0_ae_debug = t;

    `uvm_info("PRED_AHB", "Transaction Received through ahb_slave_0_ae", UVM_MEDIUM)
    `uvm_info("PRED_AHB", {"            Data: ",t.convert2string()}, UVM_HIGH)

    // Construct one of each output transaction type.
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");
    cptra_sb_ap_output_transaction = cptra_sb_ap_output_transaction_t::type_id::create("cptra_sb_ap_output_transaction");
    soc_ifc_sb_ahb_ap_output_transaction = soc_ifc_sb_ahb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ahb_ap_output_transaction");
    soc_ifc_sb_apb_ap_output_transaction = soc_ifc_sb_apb_ap_output_transaction_t::type_id::create("soc_ifc_sb_apb_ap_output_transaction");

    // Extract info
    $cast(ahb_txn, t);
    soc_ifc_sb_ahb_ap_output_transaction.copy(ahb_txn);
    // Address must be aligned to the native data width in the SOC IFC! I.e. 4-byte aligned
    address_aligned = ahb_txn.address & ~(SOC_IFC_DATA_W/8 - 1);
    if (ahb_txn.address & ((SOC_IFC_DATA_W/8 - 1))) begin
        `uvm_error("PRED_AHB", "Detected AHB transfer with bad address alignment! Address: 0x%x, expected alignment: 0x%x")
    end
    // Grab the data from the address offset, similar to how it's done in HW
    data_active = SOC_IFC_DATA_W'(ahb_txn.data[0] >> (8*(address_aligned % (ahb_lite_slave_0_params::AHB_WDATA_WIDTH/8))));
    if (p_soc_ifc_AHB_map.get_mem_by_offset(ahb_txn.address) != null) begin: MEM_HANDLE
        `uvm_info("PRED_AHB", $sformatf("Detected access to mailbox at address: 0x%x", ahb_txn.address), UVM_MEDIUM)
        axs_mem = p_soc_ifc_AHB_map.get_mem_by_offset(ahb_txn.address);
    end: MEM_HANDLE
    else begin: REG_HANDLE
        axs_reg = p_soc_ifc_AHB_map.get_reg_by_offset(ahb_txn.address);
        if (axs_reg == null) begin
            `uvm_error("PRED_AHB", $sformatf("AHB transaction to address: 0x%x decodes to null from soc_ifc_AHB_map", ahb_txn.address))
        end
    end: REG_HANDLE

    // Determine if we will submit the transaction to reg_predictor to update mirrors
    if (!configuration.enable_reg_prediction) begin
        do_reg_prediction = 1'b0;
    end
    else if (rdc_clk_gate_active || noncore_rst_out_asserted) begin
        do_reg_prediction = 1'b0;
        if (ahb_txn.RnW == AHB_READ)
            soc_ifc_sb_ahb_ap_output_transaction.data[0] = 0;
    end
    else if (axs_mem != null) begin
        do_reg_prediction = 1'b0;
    end
    else if (axs_reg != null) begin
        // Mailbox accesses are discarded based on valid_requester/valid_receiver
        case (axs_reg.get_name()) inside
            "mbox_lock": begin
                if (ahb_txn.RnW == AHB_READ && ahb_txn.resp[0] != AHB_OKAY) begin
                    do_reg_prediction = 1'b0;
                    // "Expected" read data is 0
                    soc_ifc_sb_ahb_ap_output_transaction.data[0] = 0;
                    // Complete any scheduled predictions to 0 (due to other delay jobs)
                    if (p_soc_ifc_rm.mbox_csr_rm.mbox_lock_clr_miss.is_on()) begin
                        p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.predict(0);
                        `uvm_info("PRED_AHB", "Completed mbox_lock deassert prediction (scheduled by mbox_execute) since mbox_lock reg prediction is disabled, due to failed AHB transfer", UVM_MEDIUM)
                        p_soc_ifc_rm.mbox_csr_rm.mbox_lock_clr_miss.reset(0);
                    end
                end
            end
            "mbox_user": begin
                if (ahb_txn.RnW == AHB_READ && ahb_txn.resp[0] != AHB_OKAY) begin
                    do_reg_prediction = 1'b0;
                    // "Expected" read data is 0
                    soc_ifc_sb_ahb_ap_output_transaction.data[0] = 0;
                end
            end
            "mbox_cmd",
            "mbox_dlen",
            "mbox_execute": begin
                if (ahb_txn.RnW == AHB_WRITE) begin
                    do_reg_prediction = valid_requester(ahb_txn) && (ahb_txn.resp[0] == AHB_OKAY);
                end
                else begin
                    if (ahb_txn.resp[0] != AHB_OKAY) begin
                        do_reg_prediction = 1'b0;
                        // "Expected" read data is 0
                        soc_ifc_sb_ahb_ap_output_transaction.data[0] = 0;
                    end
                end
            end
            "mbox_datain": begin
                // The mbox_data_q in the reg-model is used to track
                // datain->dataout integrity.
                // Pushes to datain are gated here by checking FSM state/lock etc.
                if (ahb_txn.RnW == AHB_WRITE) begin
                    if (valid_requester(ahb_txn)) begin
                        do_reg_prediction = 1'b1;
                        datain_count++;
                    end
                    else begin
                        do_reg_prediction = 1'b0;
                    end
                end
                else begin
                    if (ahb_txn.resp[0] != AHB_OKAY) begin
                        do_reg_prediction = 1'b0;
                        // "Expected" read data is 0
                        soc_ifc_sb_ahb_ap_output_transaction.data[0] = 0;
                    end
                end
            end
            "mbox_dataout": begin
                if (ahb_txn.RnW == AHB_WRITE) begin
                    do_reg_prediction = 1'b0;
                    `uvm_warning("PRED_AHB", "Attempted write to mbox_dataout is unsupported and will be dropped")
                end
                else begin
                    if (valid_receiver(ahb_txn) && ahb_txn.resp[0] == AHB_OKAY) begin
                        do_reg_prediction = 1'b1;
                        // "Expected" read data for scoreboard is current
                        // mirrored value prior to running do_predict
                        soc_ifc_sb_ahb_ap_output_transaction.data[0] = axs_reg.get_mirrored_value() << 8*(address_aligned % (ahb_lite_slave_0_params::AHB_WDATA_WIDTH/8));
                        dataout_count++;
                    end
                    else begin
                        do_reg_prediction = 1'b0;
                        // TODO escalate to uvm_warning?
                        `uvm_info("PRED_AHB", "Attempted read from mbox_dataout with invalid receiver", UVM_MEDIUM)
                        // "Expected" read data is 0
                        soc_ifc_sb_ahb_ap_output_transaction.data[0] = uvm_reg_data_t'(0);
                    end
                end
            end
            "mbox_status": begin
                if (ahb_txn.RnW == AHB_WRITE) begin
                    if (!valid_receiver(ahb_txn) || ahb_txn.resp[0] != AHB_OKAY) begin
                        do_reg_prediction = 1'b0;
                        // NOTE: This might happen if a force-unlock is in progress when the mbox_status write is initiated
                        `uvm_info("PRED_AHB",
                                  $sformatf("Write to mbox_status in state [%p] is unexpected! mbox_lock.lock: %0d, soc_has_lock: %0d, valid_receiver: %0d",
                                            p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs,
                                            p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value(),
                                            p_soc_ifc_rm.mbox_csr_rm.mbox_status.soc_has_lock.get_mirrored_value(),
                                            valid_receiver(ahb_txn)),
                                  UVM_LOW)
                    end
                end
                else begin
                    if (ahb_txn.resp[0] != AHB_OKAY) begin
                        do_reg_prediction = 1'b0;
                        // "Expected" read data is 0
                        soc_ifc_sb_ahb_ap_output_transaction.data[0] = 0;
                    end
                end
            end
            //SHA Accelerator Functions
            "LOCK",
            "USER": begin
                if (ahb_txn.RnW == AHB_READ && ahb_txn.resp[0] != AHB_OKAY) begin
                    do_reg_prediction = 1'b0;
                    // "Expected" read data is 0
                    soc_ifc_sb_ahb_ap_output_transaction.data[0] = 0;
                end
            end
            "MODE",
            "START_ADDRESS",
            "DLEN": begin
                if (ahb_txn.RnW == AHB_WRITE) begin
                    do_reg_prediction = sha_valid_user(ahb_txn) && (ahb_txn.resp[0] == AHB_OKAY);
                end
                else begin
                    if (ahb_txn.resp[0] != AHB_OKAY) begin
                        do_reg_prediction = 1'b0;
                        // "Expected" read data is 0
                        soc_ifc_sb_ahb_ap_output_transaction.data[0] = 0;
                    end
                end
            end
            "DATAIN": begin
                if (ahb_txn.resp[0] != AHB_OKAY) begin
                    do_reg_prediction = 1'b0;
                    // "Expected" read data is 0
                    soc_ifc_sb_ahb_ap_output_transaction.data[0] = 0;
                end
            end
            "EXECUTE": begin
                if (ahb_txn.RnW == AHB_WRITE) begin
                    do_reg_prediction = sha_valid_user(ahb_txn) && (ahb_txn.resp[0] == AHB_OKAY);
                end
                else begin
                    if (ahb_txn.resp[0] != AHB_OKAY) begin
                        do_reg_prediction = 1'b0;
                        // "Expected" read data is 0
                        soc_ifc_sb_ahb_ap_output_transaction.data[0] = 0;
                    end
                end
            end
            "STATUS",
            ["DIGEST[0]":"DIGEST[9]"],
            ["DIGEST[10]":"DIGEST[15]"]: begin
                if (ahb_txn.resp[0] != AHB_OKAY) begin
                    do_reg_prediction = 1'b0;
                    // "Expected" read data is 0
                    soc_ifc_sb_ahb_ap_output_transaction.data[0] = 0;
                end
            end
            "CONTROL": begin
            end
            default: begin
                `uvm_info("PRED_AHB", {"Enable reg prediction on access to ", axs_reg.get_name()}, UVM_FULL)
            end
        endcase
    end

    // Submit the transaction to reg_predictor to update mirrors
    if (do_reg_prediction) begin
        `uvm_info("PRED_AHB", "Forwarding transaction to ahb_reg_predictor", UVM_HIGH)
        soc_ifc_ahb_reg_ap.write(ahb_txn);
    end

    // Calculate any other system effects from the register access
    if (rdc_clk_gate_active || noncore_rst_out_asserted) begin
        `uvm_info("PRED_AHB", {"On access to register: ", axs_reg.get_full_name(), " reset is asserted, skipping system prediction"}, UVM_MEDIUM)
    end
    else if (axs_mem != null) begin: MEM_AXS
        `uvm_info("PRED_AHB", $sformatf("Not performing any system prediction for access to mailbox at address: 0x%x", ahb_txn.address), UVM_FULL)
    end// MEM_AXS
    else if (axs_reg != null) begin: REG_AXS
        `uvm_info("PRED_AHB", {"Detected access to register: ", axs_reg.get_full_name()}, UVM_MEDIUM)
        // Non-interrupt registers have 2-levels of ancestry back to reg_model top
        if (axs_reg.get_parent().get_parent().get_name() == "soc_ifc_rm") begin
            case (axs_reg.get_name()) inside
                "mbox_lock": begin
                    // Reading mbox_lock when it is already locked has no effect, so
                    // only calculate predictions on acquiring lock (rdata == 0)
                    // which requires that the AHB transfer was successful in
                    // performing the access
                    if (~data_active[p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_lsb_pos()] &&
                        p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value() &&
                        do_reg_prediction)
                    begin
                        // Cannot put this inside the reg callback because the post_predict
                        // method has no way to access the addr_user value
                        `uvm_info("PRED_AHB", $sformatf("Predicting new value [0x%x] for mbox_user as AHB agent acquires lock",p_soc_ifc_rm.mbox_csr_rm.mbox_user.get_reset("HARD")), UVM_HIGH)
                        p_soc_ifc_rm.mbox_csr_rm.mbox_user.predict(p_soc_ifc_rm.mbox_csr_rm.mbox_user.get_reset("HARD"));
                        // Reset counters at beginning of command
                        datain_count = 0;
                        dataout_count = 0;
                        // Log the step for coverage
                        next_step = '{lock_acquire: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                    else begin
                        `uvm_info("PRED_AHB", $sformatf("Access to mbox_lock of type %p has no effect", ahb_txn.RnW), UVM_MEDIUM)
                        // Log the step for coverage
                        next_step = '{null_action: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                end
                "mbox_user": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_warning("PRED_AHB", {"Write to RO register: ", axs_reg.get_name(), " has no effect on system"})
                    end
                    else begin
                        `uvm_info("PRED_AHB", {"Read to ", axs_reg.get_name(), " has no effect on system"}, UVM_MEDIUM)
                    end
                    // Log the step for coverage
                    next_step = '{null_action: 1'b1, default: 1'b0};
                    `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
                "mbox_cmd": begin
                    if (ahb_txn.RnW == AHB_WRITE && do_reg_prediction) begin
                        // Log the step for coverage
                        next_step = '{cmd_wr: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                    else if (ahb_txn.RnW == AHB_READ && p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.uc_receive_stage) begin
                        // Log the step for coverage
                        next_step = '{cmd_rd: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                    else begin
                        // Log the step for coverage
                        next_step = '{null_action: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                end
                "mbox_dlen": begin
                    if (ahb_txn.RnW == AHB_WRITE && do_reg_prediction) begin
                        // Log the step for coverage
                        if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.uc_dlen_stage)
                            next_step = '{dlen_wr: 1'b1, default: 1'b0};
                        else if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.uc_receive_stage)
                            next_step = '{resp_dlen_wr: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                    else if (ahb_txn.RnW == AHB_READ && p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.uc_receive_stage) begin
                        // Log the step for coverage
                        next_step = '{dlen_rd: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                    else begin
                        // Log the step for coverage
                        next_step = '{null_action: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                end
                "mbox_datain": begin
                    `uvm_info("PRED_AHB", $sformatf("Access to mailbox datain, write count: %d", datain_count), UVM_FULL)
                    if (ahb_txn.RnW == AHB_WRITE && do_reg_prediction) begin
                        // Log the step for coverage
                        if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.uc_data_stage)
                            next_step = '{datain_wr: 1'b1, default: 1'b0};
                        else if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.uc_receive_stage)
                            next_step = '{resp_datain_wr: 1'b1, default: 1'b0};
                        else
                            next_step = '{null_action: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                    else begin
                        // Log the step for coverage
                        next_step = '{null_action: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                end
                "mbox_dataout": begin
                    `uvm_info("PRED_AHB", $sformatf("Access to mailbox dataout, read count: %d", dataout_count), UVM_FULL)
                    // Log the step for coverage
                    next_step = '{null_action: 1'b1, default: 1'b0};
                    if (ahb_txn.RnW == AHB_READ && do_reg_prediction) begin
                        // Log the step for coverage
                        if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.uc_receive_stage) begin
                            next_step = '{dataout_rd: 1'b1, default: 1'b0};
                        end
                    end
                    `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
                "mbox_execute": begin
                    // Log the step for coverage
                    next_step = '{null_action: 1'b1, default: 1'b0};
                    if (ahb_txn.RnW == AHB_WRITE && do_reg_prediction) begin
                        // Log the step for coverage
                        if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.uc_data_stage && p_soc_ifc_rm.mbox_csr_rm.mbox_execute.execute.get_mirrored_value()) begin
                            next_step = '{exec_set: 1'b1, default: 1'b0};
                        end
                        else if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.uc_done_stage && !p_soc_ifc_rm.mbox_csr_rm.mbox_execute.execute.get_mirrored_value()) begin
                            next_step = '{exec_clr: 1'b1, default: 1'b0};
                        end
                    end
                    `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
                "mbox_status": begin
                    if (ahb_txn.RnW == AHB_WRITE && do_reg_prediction) begin
                        // Log the step for coverage
                        next_step = '{status_wr: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                    else if (ahb_txn.RnW == AHB_READ && do_reg_prediction) begin
                        // Log the step for coverage
                        next_step = '{status_rd: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                    else begin
                        // Log the step for coverage
                        next_step = '{null_action: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                end
                "mbox_unlock": begin
                    if (ahb_txn.RnW == AHB_WRITE && do_reg_prediction && p_soc_ifc_rm.mbox_csr_rm.mbox_unlock.unlock.get_mirrored_value()) begin
                        // Log the step for coverage
                        next_step = '{force_unlock: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                    else begin
                        // Log the step for coverage
                        next_step = '{null_action: 1'b1, default: 1'b0};
                        `uvm_info("PRED_AHB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                    end
                end
                //SHA Accelerator Functions
                "LOCK": begin
                    // Reading sha_lock when it is already locked has no effect, so
                    // only calculate predictions on acquiring lock (rdata == 0)
                    // which requires that the AHB transfer was successful in
                    // performing the access
                    if (~data_active[p_soc_ifc_rm.sha512_acc_csr_rm.LOCK.LOCK.get_lsb_pos()] &&
                        p_soc_ifc_rm.sha512_acc_csr_rm.LOCK.LOCK.get_mirrored_value() &&
                        do_reg_prediction)
                    begin
                        // Cannot put this inside the reg callback because the post_predict
                        // method has no way to access the addr_user value
                        `uvm_info("PRED_AHB", $sformatf("Predicting new value [0x%x] for sha_user as AHB agent acquires lock",p_soc_ifc_rm.sha512_acc_csr_rm.USER.get_reset("HARD")), UVM_HIGH)
                        p_soc_ifc_rm.sha512_acc_csr_rm.USER.predict(p_soc_ifc_rm.sha512_acc_csr_rm.USER.get_reset("HARD"));
                    end
                    else begin
                        `uvm_info("PRED_AHB", $sformatf("Access to sha_lock of type %p has no effect", ahb_txn.RnW), UVM_MEDIUM)
                    end
                end
                "USER": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_warning("PRED_AHB", {"Write to RO register: ", axs_reg.get_name(), " has no effect on system"})
                    end
                    else begin
                        `uvm_info("PRED_AHB", {"Read to ", axs_reg.get_name(), " has no effect on system"}, UVM_MEDIUM)
                    end
                end
                "MODE",
                "START_ADDRESS",
                "DLEN",
                "DATAIN",
                "EXECUTE",
                "STATUS",
                ["DIGEST[0]":"DIGEST[9]"],
                ["DIGEST[10]":"DIGEST[15]"],
                "CONTROL": begin
                    `uvm_info("PRED_AHB", $sformatf("Handling access to %s. Nothing to do.", axs_reg.get_name()), UVM_FULL)
                end
                "CPTRA_HW_ERROR_FATAL": begin
                    if (ahb_txn.RnW == AHB_WRITE && |data_active && (p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_HW_ERROR_FATAL.get_mirrored_value() == 0)) begin
                        `uvm_info("PRED_AHB", $sformatf("Write to %s results in all bits cleared, but has no effect on cptra_error_fatal (requires reset)", axs_reg.get_name()), UVM_MEDIUM)
                    end
                end
                "CPTRA_HW_ERROR_NON_FATAL": begin
                    if (p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_HW_ERROR_NON_FATAL.get_mirrored_value() == 0) begin
                        cptra_error_non_fatal = 1'b0;
                    end
                end
                "CPTRA_FW_ERROR_FATAL": begin
                    if (ahb_txn.RnW == AHB_WRITE && |(data_active && ~p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FW_ERROR_FATAL.get_mirrored_value())) begin
                        `uvm_info("PRED_AHB", $sformatf("Write to %s set a new bit, trigger cptra_error_fatal interrupt", axs_reg.get_name()), UVM_MEDIUM)
                        cptra_error_fatal = 1'b1;
                        send_soc_ifc_sts_txn = 1'b1;
                    end
                    if (ahb_txn.RnW == AHB_WRITE && |data_active && (p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FW_ERROR_FATAL.get_mirrored_value() == 0)) begin
                        `uvm_info("PRED_AHB", $sformatf("Write to %s results in all bits cleared, but has no effect on cptra_error_fatal (requires reset)", axs_reg.get_name()), UVM_MEDIUM)
                    end
                end
                "CPTRA_FW_ERROR_NON_FATAL": begin
                    if (p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FW_ERROR_NON_FATAL.get_mirrored_value() == 0) begin
                        cptra_error_non_fatal = 1'b0;
                    end
                end
                "CPTRA_HW_ERROR_ENC",
                "CPTRA_FW_ERROR_ENC",
                ["CPTRA_FW_EXTENDED_ERROR_INFO[0]":"CPTRA_FW_EXTENDED_ERROR_INFO[7]"]: begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_error("PRED_AHB", {"Add prediction for write to ",axs_reg.get_name()," register on AHB interface"}) // TODO
                    end
                end
                "CPTRA_BOOT_STATUS": begin
                    // Handled in callbacks via reg predictor
                    `uvm_info("PRED_AHB", $sformatf("Handling access to %s. Nothing to do.", axs_reg.get_name()), UVM_DEBUG)
                end
                "CPTRA_FLOW_STATUS": begin
                    if (ahb_txn.RnW == AHB_WRITE &&
                        ((p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_fw.get_mirrored_value()      != this.ready_for_fw_push) ||
                         (p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_runtime.get_mirrored_value() != this.ready_for_runtime) ||
                         (p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.mailbox_flow_done.get_mirrored_value() != this.mailbox_flow_done))) begin
                        this.ready_for_fw_push = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_fw     .get_mirrored_value();
                        this.ready_for_runtime = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_runtime.get_mirrored_value();
                        this.mailbox_flow_done = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.mailbox_flow_done.get_mirrored_value();
                        send_soc_ifc_sts_txn = 1'b1;
                    end
                    else if (ahb_txn.RnW == AHB_READ) begin
                        send_soc_ifc_sts_txn = 1'b0;
                    end
                end
                "CPTRA_RESET_REASON",
                "CPTRA_SECURITY_STATE": begin
                    if (ahb_txn.RnW == AHB_WRITE)
                        `uvm_info("PRED_AHB", {"Write to ", axs_reg.get_name(), " has no effect"}, UVM_DEBUG)
                end
                ["CPTRA_MBOX_VALID_PAUSER[0]":"CPTRA_MBOX_VALID_PAUSER[4]"]: begin
                    int idx = axs_reg.get_offset(p_soc_ifc_AHB_map) - p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[0].get_offset(p_soc_ifc_AHB_map);
                    idx /= 4;
                    if (mbox_valid_users_locked[idx] && ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_error("PRED_AHB", {"Write attempted to locked register: ", axs_reg.get_name()})
                    end
                    else if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_info("PRED_AHB", {"Write to ", axs_reg.get_name(), " has no effect on system until locked"}, UVM_MEDIUM)
                    end
                end
                ["CPTRA_MBOX_PAUSER_LOCK[0]":"CPTRA_MBOX_PAUSER_LOCK[4]"]: begin
                    int idx = axs_reg.get_offset(p_soc_ifc_AHB_map) - p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[0].get_offset(p_soc_ifc_AHB_map);
                    idx /= 4;
                    if (mbox_valid_users_locked[idx] && ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_error("PRED_AHB", {"Write attempted to locked register: ", axs_reg.get_name()})
                    end
                    else if (ahb_txn.RnW == AHB_WRITE) begin
                        mbox_valid_users[idx] = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[idx].get_mirrored_value(); // VALID_PAUSER field is only applied when locked
                        mbox_valid_users_locked[idx] |= data_active[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[idx].LOCK.get_lsb_pos()];
                        `uvm_info("PRED_AHB", $sformatf("mbox_valid_users_locked[%d] set to 0x%x, mbox_valid_users[%d] has value: 0x%x", idx, mbox_valid_users_locked[idx], idx, mbox_valid_users[idx]), UVM_MEDIUM)
                    end
                    else begin
                        `uvm_info("PRED_AHB", $sformatf("mbox_valid_users_locked[%d] read value 0x%x, mbox_valid_users[%d] has value: 0x%x", idx, mbox_valid_users_locked[idx], idx, mbox_valid_users[idx]), UVM_HIGH)
                    end
                end
                "CPTRA_TRNG_VALID_PAUSER",
                "CPTRA_TRNG_PAUSER_LOCK",
                ["CPTRA_TRNG_DATA[0]" : "CPTRA_TRNG_DATA[9]"],
                ["CPTRA_TRNG_DATA[10]" : "CPTRA_TRNG_DATA[11]"],
		        "CPTRA_TRNG_CTRL": begin
                    // Handled in callbacks via reg predictor
                    `uvm_info("PRED_AHB", $sformatf("Handling access to %s. Nothing to do.", axs_reg.get_name()), UVM_DEBUG)
                end
                "CPTRA_TRNG_STATUS": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        if (p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_TRNG_STATUS.DATA_REQ.get_mirrored_value() != this.trng_data_req) begin
                            send_soc_ifc_sts_txn = 1'b1;
                        end
                        this.trng_data_req = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_TRNG_STATUS.DATA_REQ.get_mirrored_value();
                    end
                    else if (ahb_txn.RnW == AHB_READ) begin
                        send_soc_ifc_sts_txn = 1'b0;
                    end
                end
                "CPTRA_FUSE_WR_DONE",
                "CPTRA_TIMER_CONFIG",
                "CPTRA_BOOTFSM_GO": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_error("PRED_AHB", $sformatf("Unexpected write to %s register on AHB interface", axs_reg.get_name()))
                    end
                end
                "CPTRA_DBG_MANUF_SERVICE_REG": begin
                    `uvm_info("PRED_AHB", $sformatf("Handling access to %s. Nothing to do.", axs_reg.get_name()), UVM_DEBUG)
                end
                "CPTRA_CLK_GATING_EN": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_error("PRED_AHB", $sformatf("Unexpected write to %s register on AHB interface", axs_reg.get_name()))
                    end
                end
                "CPTRA_GENERIC_INPUT_WIRES[0]",
                "CPTRA_GENERIC_INPUT_WIRES[1]": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_info("PRED_AHB", $sformatf("Write to %s register on AHB interface has no effect", axs_reg.get_name()), UVM_LOW)
                    end
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
                                `uvm_info("PRED_AHB", "Observed write to CPTRA_GENERIC_OUTPUT_WIRES [Toggle random SRAM single bit flip injection]", UVM_MEDIUM)
                            32'hfe:
                                `uvm_info("PRED_AHB", "Observed write to CPTRA_GENERIC_OUTPUT_WIRES [Toggle random SRAM double bit flip injection]", UVM_MEDIUM)
                            32'hff:
                                `uvm_info("PRED_AHB", "Observed write to CPTRA_GENERIC_OUTPUT_WIRES to End the simulation with a Success status", UVM_LOW)
                        endcase
                        send_soc_ifc_sts_txn = data_active != generic_output_wires[31:0];
                        generic_output_wires = {generic_output_wires[63:32],data_active}; // FIXME for data width?
                    end
                end
                "CPTRA_GENERIC_OUTPUT_WIRES[1]": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        send_soc_ifc_sts_txn = data_active != generic_output_wires[63:32];
                        generic_output_wires = {data_active,generic_output_wires[31:0]}; // FIXME for data width?
                    end
                end
                "CPTRA_HW_REV_ID": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_warning("PRED_AHB", {"Write to RO register: ", axs_reg.get_name(), " has no effect on system"})
                    end
                    else begin
                        `uvm_info("PRED_AHB", {"Read to ", axs_reg.get_name(), " has no effect on system"}, UVM_MEDIUM)
                    end
                end
                "CPTRA_FW_REV_ID[0]",
                "CPTRA_FW_REV_ID[1]": begin
                    `uvm_info("PRED_AHB", {"Access to ", axs_reg.get_name(), " has no effect on system"}, UVM_MEDIUM)
                end
                "CPTRA_HW_CONFIG": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_warning("PRED_AHB", {"Write to RO register: ", axs_reg.get_name(), " has no effect on system"})
                    end
                    else begin
                        `uvm_info("PRED_AHB", {"Read to ", axs_reg.get_name(), " has no effect on system"}, UVM_MEDIUM)
                    end
                end
                "CPTRA_WDT_TIMER1_EN": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_info("PRED_AHB", {"Detected write to ", axs_reg.get_name()," register on AHB interface, starting WDT timer1"}, UVM_MEDIUM);
                    end
                end
                "CPTRA_WDT_TIMER1_CTRL": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        // Handled in callbacks via reg predictor
                        `uvm_info("PRED_AHB", $sformatf("Handling access to %s. This will restart WDT timer1", axs_reg.get_name()), UVM_MEDIUM);
                        //Capture restart bit so the counters can be updated
                        wdt_t1_restart = data_active[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER1_CTRL.timer1_restart.get_lsb_pos()];
                    end
                end
                "CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[0]",
                "CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[1]": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_info("PRED_AHB", {"Detected write to ", axs_reg.get_name()," register on AHB interface"}, UVM_MEDIUM);
                    end
                end
                "CPTRA_WDT_TIMER2_EN": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_info("PRED_AHB", {"Detected write to ", axs_reg.get_name(), " register on AHB interface, starting WDT timer2"}, UVM_MEDIUM);
                    end
                end
                "CPTRA_WDT_TIMER2_CTRL": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        // Handled in callbacks via reg predictor
                        `uvm_info("PRED_AHB", $sformatf("Handling access to %s. This will restart WDT timer2", axs_reg.get_name()), UVM_MEDIUM);
                        //Capture restart bit so the counters can be updated
                        wdt_t2_restart = data_active[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER2_CTRL.timer2_restart.get_lsb_pos()];
                    end
                end
                "CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[0]",
                "CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[1]": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_info("PRED_AHB", {"Detected write to ",axs_reg.get_name()," register on AHB interface"}, UVM_LOW) // TODO
                    end
                end
                "CPTRA_WDT_STATUS": begin
                    `uvm_info("PRED_AHB", "AHB access of WDT status", UVM_MEDIUM);
                end
                "CPTRA_FUSE_VALID_PAUSER",
                "CPTRA_FUSE_PAUSER_LOCK": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_error("PRED_AHB", {"Add prediction for write to ",axs_reg.get_name()," register on AHB interface"}) // TODO
                    end
                end
                ["CPTRA_WDT_CFG[0]":"CPTRA_WDT_CFG[1]"],
                ["CPTRA_RSVD_REG[0]":"CPTRA_RSVD_REG[3]"]: begin
                    `uvm_info("PRED_AHB", {"Access to ", axs_reg.get_name(), " has no effect on system"}, UVM_MEDIUM)
                end
                ["fuse_uds_seed[0]" :"fuse_uds_seed[9]" ],
                ["fuse_uds_seed[10]":"fuse_uds_seed[11]"]: begin
                    if (fuse_update_enabled) begin
                        `uvm_error("PRED_AHB", {"Unexpected write to ", axs_reg.get_name(), " should not occur when fuse_update_enabled == 1!"})
                        send_cptra_sts_txn       = 1'b1;
                    end
                end
                ["fuse_field_entropy[0]" :"fuse_field_entropy[7]" ]: begin
                    if (fuse_update_enabled) begin
                        `uvm_error("PRED_AHB", {"Unexpected write to ", axs_reg.get_name(), " should not occur when fuse_update_enabled == 1!"})
                        send_cptra_sts_txn       = 1'b1;
                    end
                end
                ["fuse_key_manifest_pk_hash[0]" :"fuse_key_manifest_pk_hash[9]"],
                ["fuse_key_manifest_pk_hash[10]":"fuse_key_manifest_pk_hash[11]"],
                "fuse_key_manifest_pk_hash_mask",
                ["fuse_owner_pk_hash[0]" :"fuse_owner_pk_hash[9]"],
                ["fuse_owner_pk_hash[10]":"fuse_owner_pk_hash[11]"],
                "fuse_fmc_key_manifest_svn",
                ["fuse_runtime_svn[0]":"fuse_runtime_svn[3]"],
                "fuse_anti_rollback_disable",
                ["fuse_idevid_cert_attr[0]" :"fuse_idevid_cert_attr[9]"],
                ["fuse_idevid_cert_attr[10]":"fuse_idevid_cert_attr[19]"],
                ["fuse_idevid_cert_attr[20]":"fuse_idevid_cert_attr[23]"],
                ["fuse_idevid_manuf_hsm_id[0]":"fuse_idevid_manuf_hsm_id[3]"],
                "fuse_life_cycle",
                "fuse_lms_verify",
                "fuse_lms_revocation",
                "fuse_soc_stepping_id",
                ["internal_obf_key[0]":"internal_obf_key[7]"]: begin
                    // Handled in callbacks via reg predictor
                    `uvm_info("PRED_AHB", $sformatf("Handling access to fuse/key/secret register %s. Nothing to do.", axs_reg.get_name()), UVM_DEBUG)
                end
                "internal_iccm_lock": begin
                    if (ahb_txn.RnW == AHB_WRITE && !iccm_locked) begin
                        iccm_locked = 1'b1;
                        `uvm_info("FW_RST_DEBUG", $sformatf("Write to set iccm lock, value is 0x%x", p_soc_ifc_rm.soc_ifc_reg_rm.internal_iccm_lock.lock.get_mirrored_value()), UVM_LOW)
                        send_cptra_sts_txn = 1;
                    end
                    else if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_error("PRED_AHB", {"Unexpected write to ",axs_reg.get_name()," register on AHB interface"})
                    end
                end
                "internal_fw_update_reset": begin
                    // Handled in callbacks via reg predictor
                    `uvm_info("PRED_AHB", $sformatf("Handling access to register %s. Nothing to do.", axs_reg.get_name()), UVM_DEBUG)
                end
                "internal_fw_update_reset_wait_cycles": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_error("PRED_AHB", $sformatf("FIXME - need to add logic for writes to register %s", axs_reg.get_name())) // TODO
                    end
                    else begin
                        `uvm_info("PRED_AHB", {"Read from ", axs_reg.get_name(), " has no effect"}, UVM_DEBUG)
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
                "internal_hw_error_fatal_mask",
                "internal_hw_error_non_fatal_mask",
                "internal_fw_error_fatal_mask",
                "internal_fw_error_non_fatal_mask": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_error("PRED_AHB", $sformatf("FIXME - need to add logic for error mask register %s", axs_reg.get_name())) // TODO
                    end
                    else begin
                        `uvm_info("PRED_AHB", {"Read from ", axs_reg.get_name(), " has no effect"}, UVM_DEBUG)
                    end
                end
                "internal_rv_mtime_l",
                "internal_rv_mtime_h",
                "internal_rv_mtimecmp_l",
                "internal_rv_mtimecmp_h": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        if (timer_intr_pending && mtime_lt_mtimecmp()) begin
                            `uvm_info("PRED_AHB", $sformatf("Write to %s causes immediate deassertion of timer interrupt", axs_reg.get_name()), UVM_HIGH)
                            timer_intr_pending = 0;
//                            send_cptra_sts_txn = 1; // No transaction captured on deassertion
                        end
                        else if (timer_intr_pending) begin
                            `uvm_info("PRED_AHB", $sformatf("Write to %s does not change the status of timer interrupt", axs_reg.get_name()), UVM_HIGH)
                        end
                        else if (!timer_intr_pending && mtime_lt_mtimecmp()) begin
                            `uvm_info("PRED_AHB", $sformatf("Write to %s does not change the status of timer interrupt", axs_reg.get_name()), UVM_HIGH)
                        end
                        else if (!timer_intr_pending && !mtime_lt_mtimecmp()) begin
                            `uvm_info("PRED_AHB", $sformatf("Write to %s causes immediate assertion of timer interrupt", axs_reg.get_name()), UVM_HIGH)
                            timer_intr_pending = 1;
                            send_cptra_sts_txn = 1;
                        end
                    end
                    else begin
                        `uvm_info("PRED_AHB", $sformatf("Read from %s does not change the status of timer interrupt", axs_reg.get_name()), UVM_FULL)
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
                        send_cptra_sts_txn = (!this.soc_ifc_error_intr_pending && p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.error_en.get_mirrored_value()) ||
                                             (!this.soc_ifc_notif_intr_pending && p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_mirrored_value());
                        this.soc_ifc_error_intr_pending = p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.error_en.get_mirrored_value();
                        this.soc_ifc_notif_intr_pending = p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_mirrored_value();
                    end
                end
                "error_intr_en_r",
                "notif_intr_en_r",
                "error_intr_trig_r",
                "notif_intr_trig_r": begin
                    `uvm_info("PRED_AHB", $sformatf("Write to %s handled in callback", axs_reg.get_name()), UVM_DEBUG)
                end
                "error_global_intr_r",
                "notif_global_intr_r": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_warning("PRED_AHB", $sformatf("Unexpected write to %s will have no effect", axs_reg.get_name()))
                    end
                end
                "error_internal_intr_r",
                "notif_internal_intr_r": begin
                    if (ahb_txn.RnW == AHB_WRITE && |data_active) begin
                        // If the write clears ALL pending interrupts, global intr signal will deassert
                        // but this does not result in a cptra status transaction because we only
                        // capture rising edges as a transaction
                        `uvm_info("PRED_AHB", {"Write to ", axs_reg.get_name(), " attempts to clear an interrupt"}, UVM_HIGH)
                        
                        //If the WDT timeout interrupt bits are being cleared, also reset the t1/t2 count values and the corresponding
                        //interrupt flags (used in wdt_counter_task)
                        wdt_cascade = (p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER1_EN.timer1_en.get_mirrored_value() && !(p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER2_EN.timer2_en.get_mirrored_value()));
                        wdt_independent = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER2_EN.timer2_en.get_mirrored_value();
                        wdt_t1_timeout = (this.t1_count == {p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[1].timer1_timeout_period.get_mirrored_value(), p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[0].timer1_timeout_period.get_mirrored_value()});
                        wdt_t2_timeout = (this.t2_count == {p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[1].timer2_timeout_period.get_mirrored_value(), p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[0].timer2_timeout_period.get_mirrored_value()});

                        if (wdt_cascade && wdt_t1_timeout && data_active[`SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_LOW]) begin
                            this.t1_count = 'h0;
                            this.t2_count = 'h0;
                            this.wdt_error_intr_sent = 1'b0;
                        end
                        else if (wdt_independent) begin
                            if (data_active[`SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_LOW]) begin
                                if (wdt_t1_timeout)
                                    this.t1_count = 'h0;
                                this.wdt_error_intr_sent = 1'b0;
                            end
                            if (data_active[`SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_LOW]) begin
                                if (wdt_t2_timeout)
                                    this.t2_count = 'h0;
                                this.wdt_t2_error_intr_sent = 1'b0;
                            end
                        end

                    end
                end
                "error_internal_intr_count_r",
                "error_inv_dev_intr_count_r",
                "error_cmd_fail_intr_count_r",
                "error_bad_fuse_intr_count_r",
                "error_iccm_blocked_intr_count_r",
                "error_mbox_ecc_unc_intr_count_r",
                "error_wdt_timer1_timeout_intr_count_r",
                "error_wdt_timer2_timeout_intr_count_r",
                "notif_cmd_avail_intr_count_r",
                "notif_mbox_ecc_cor_intr_count_r",
                "notif_debug_locked_intr_count_r",
                "notif_scan_mode_intr_count_r",
                "notif_soc_req_lock_intr_count_r",
                "notif_gen_in_toggle_intr_count_r": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_info("PRED_AHB", {"Write to ", axs_reg.get_name(), " modifies interrupt statistics count"}, UVM_HIGH)
                    end
                    else begin
                        `uvm_info("PRED_AHB", {"Access to register ", axs_reg.get_name(), " will have no effect on system"}, UVM_HIGH)
                    end
                end
                "error_internal_intr_count_incr_r",
                "error_inv_dev_intr_count_incr_r",
                "error_cmd_fail_intr_count_incr_r",
                "error_bad_fuse_intr_count_incr_r",
                "error_iccm_blocked_intr_count_incr_r",
                "error_mbox_ecc_unc_intr_count_incr_r",
                "error_wdt_timer1_timeout_intr_count_incr_r",
                "error_wdt_timer2_timeout_intr_count_incr_r",
                "notif_cmd_avail_intr_count_incr_r",
                "notif_mbox_ecc_cor_intr_count_incr_r",
                "notif_debug_locked_intr_count_incr_r",
                "notif_scan_mode_intr_count_incr_r",
                "notif_soc_req_lock_intr_count_incr_r",
                "notif_gen_in_toggle_intr_count_incr_r": begin
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
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        send_cptra_sts_txn = (!this.sha_err_intr_pending   && p_soc_ifc_rm.sha512_acc_csr_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.sha512_acc_csr_rm.intr_block_rf_ext.global_intr_en_r.error_en.get_mirrored_value()) ||
                                             (!this.sha_notif_intr_pending && p_soc_ifc_rm.sha512_acc_csr_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.sha512_acc_csr_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_mirrored_value());
                        this.sha_err_intr_pending   = p_soc_ifc_rm.sha512_acc_csr_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.sha512_acc_csr_rm.intr_block_rf_ext.global_intr_en_r.error_en.get_mirrored_value();
                        this.sha_notif_intr_pending = p_soc_ifc_rm.sha512_acc_csr_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.sha512_acc_csr_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_mirrored_value();
                    end
                end
                "error_intr_en_r",
                "notif_intr_en_r",
                "error_intr_trig_r",
                "notif_intr_trig_r": begin
                    `uvm_info("PRED_AHB", $sformatf("Write to %s handled in callback", axs_reg.get_name()), UVM_DEBUG)
                end
                "error_global_intr_r",
                "notif_global_intr_r": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_warning("PRED_AHB", $sformatf("Unexpected write to %s will have no effect", axs_reg.get_name()))
                    end
                end
                "error_internal_intr_r",
                "notif_internal_intr_r": begin
                    if (ahb_txn.RnW == AHB_WRITE && |data_active) begin
                        // If the write clears ALL pending interrupts, global intr signal will deassert
                        // but this does not result in a cptra status transaction because we only
                        // capture rising edges as a transaction
                        `uvm_info("PRED_AHB", {"Write to ", axs_reg.get_name(), " attempts to clear an interrupt"}, UVM_HIGH)
                    end
                end
                "error0_intr_count_r",
                "error1_intr_count_r",
                "error2_intr_count_r",
                "error3_intr_count_r",
                "notif_cmd_done_intr_count_r": begin
                    if (ahb_txn.RnW == AHB_WRITE) begin
                        `uvm_info("PRED_AHB", {"Write to ", axs_reg.get_name(), " modifies interrupt statistics count"}, UVM_HIGH)
                    end
                    else begin
                        `uvm_info("PRED_AHB", {"Access to register ", axs_reg.get_name(), " will have no effect on system"}, UVM_HIGH)
                    end
                end
                "error0_intr_count_incr_r",
                "error1_intr_count_incr_r",
                "error2_intr_count_incr_r",
                "error3_intr_count_incr_r",
                "notif_cmd_done_intr_count_incr_r": begin
                    `uvm_info("PRED_AHB", {"Access to register ", axs_reg.get_name(), " will have no effect on system"}, UVM_HIGH)
                end
                default: begin
                    `uvm_warning("PRED_AHB", $sformatf("Prediction for accesses to register '%s' unimplemented! Fix soc_ifc_predictor", axs_reg.get_name()))
                end
            endcase
        end
    end// REG_AXS

    fork
        begin
        // This allows coverage subscriber to observe both prev_step and next_step before the transition
        uvm_wait_for_nba_region();
        prev_step = next_step;
        end
    join_none

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
    bit do_reg_prediction = 1;

    // Flags control whether each transaction is sent to scoreboard
    bit send_soc_ifc_sts_txn = 0;
    bit send_cptra_sts_txn = 0;
    bit send_ahb_txn = 0;
    bit send_apb_txn = 1;
    apb5_slave_0_ae_debug = t;

    `uvm_info("PRED_APB", "Transaction Received through apb5_slave_0_ae", UVM_MEDIUM)
    `uvm_info("PRED_APB", {"            Data: ",t.convert2string()}, UVM_HIGH)

    // Construct one of each output transaction type.
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");
    cptra_sb_ap_output_transaction = cptra_sb_ap_output_transaction_t::type_id::create("cptra_sb_ap_output_transaction");
    soc_ifc_sb_ahb_ap_output_transaction = soc_ifc_sb_ahb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ahb_ap_output_transaction");
    soc_ifc_sb_apb_ap_output_transaction = soc_ifc_sb_apb_ap_output_transaction_t::type_id::create("soc_ifc_sb_apb_ap_output_transaction");

    // Extract info
    $cast(apb_txn, t);
    soc_ifc_sb_apb_ap_output_transaction.copy(apb_txn);
    axs_reg = p_soc_ifc_APB_map.get_reg_by_offset(apb_txn.addr);

    // Determine if we will submit the transaction to reg_predictor to update mirrors
    if (!configuration.enable_reg_prediction) begin
        do_reg_prediction = 1'b0;
    end
    // This is because of the RDC CLK GATE disablement...
    else if (rdc_clk_gate_active || noncore_rst_out_asserted) begin
        do_reg_prediction = 1'b0;
        soc_ifc_sb_apb_ap_output_transaction.rd_data = 0;
    end
    else begin
        // Mailbox accesses are discarded based on valid_requester/valid_receiver
        // (i.e. PAUSER + state info)
        // SHA Accelerator Functions also screened based on PAUSER
        case (axs_reg.get_name()) inside
            "mbox_lock": begin
                // RS access policy wants to update lock to 1 on a read, but if the PAUSER value is invalid
                // lock will not be set. It will hold the previous value.
                if (!(apb_txn.addr_user inside mbox_valid_users) || apb_txn.slave_err) begin
                    // Access to mbox_lock is dropped if PAUSER is not valid
                    do_reg_prediction = 1'b0;
                    // "Expected" read data is 0
                    soc_ifc_sb_apb_ap_output_transaction.rd_data = 0;
                    // Complete any scheduled predictions to 0 (due to other delay jobs)
                    if (p_soc_ifc_rm.mbox_csr_rm.mbox_lock_clr_miss.is_on()) begin
                        p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.predict(0);
                        `uvm_info("PRED_APB", "Completed mbox_lock deassert prediction (scheduled by mbox_execute) since mbox_lock reg prediction is disabled, due to failed APB transfer", UVM_MEDIUM)
                        p_soc_ifc_rm.mbox_csr_rm.mbox_lock_clr_miss.reset(0);
                    end
                end
            end
            "mbox_user",
            "mbox_unlock": begin
                if (!(apb_txn.addr_user inside mbox_valid_users) || apb_txn.slave_err) begin
                    // Access to mbox_lock is dropped if PAUSER is not valid
                    do_reg_prediction = 1'b0;
                    // "Expected" read data is 0
                    soc_ifc_sb_apb_ap_output_transaction.rd_data = 0;
                end
            end
            "mbox_cmd",
            "mbox_dlen",
            "mbox_execute": begin
                if (apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    do_reg_prediction = valid_requester(apb_txn) && !apb_txn.slave_err;
                end
                else begin
                    if (!(apb_txn.addr_user inside mbox_valid_users) || apb_txn.slave_err) begin
                        do_reg_prediction = 1'b0;
                        // "Expected" read data is 0
                        soc_ifc_sb_apb_ap_output_transaction.rd_data = 0;
                    end
                end
            end
            "mbox_datain": begin
                // The mbox_data_q in the reg-model is used to track
                // datain->dataout integrity.
                // Pushes to datain are gated here by checking PAUSER/FSM state/lock etc.
                if (apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    if (valid_requester(apb_txn)) begin
                        do_reg_prediction = 1'b1;
                        datain_count++;
                    end
                    else begin
                        do_reg_prediction = 1'b0;
                    end
                end
                else begin
                    if (!(apb_txn.addr_user inside mbox_valid_users) || apb_txn.slave_err) begin
                        do_reg_prediction = 1'b0;
                        // "Expected" read data is 0
                        soc_ifc_sb_apb_ap_output_transaction.rd_data = 0;
                    end
                end
            end
            "mbox_dataout": begin
                if (apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    do_reg_prediction = 1'b0;
                    `uvm_warning("PRED_APB", "Attempted write to mbox_dataout is unsupported and will be dropped")
                end
                else begin
                    if (valid_receiver(apb_txn) && !apb_txn.slave_err) begin
                        do_reg_prediction = 1'b1;
                        // "Expected" read data for scoreboard is current
                        // mirrored value prior to running do_predict
                        soc_ifc_sb_apb_ap_output_transaction.rd_data = axs_reg.get_mirrored_value();
                        dataout_count++;
                    end
                    else begin
                        do_reg_prediction = 1'b0;
                        // TODO escalate to uvm_warning?
                        `uvm_info("PRED_APB", "Attempted read from mbox_dataout with invalid receiver", UVM_MEDIUM)
                        // "Expected" read data is 0
                        soc_ifc_sb_apb_ap_output_transaction.rd_data = uvm_reg_data_t'(0);
                    end
                end
            end
            "mbox_status": begin
                if (apb_txn.read_or_write == APB3_TRANS_WRITE)
                    do_reg_prediction = valid_receiver(apb_txn) && !apb_txn.slave_err;
                else begin
                    if (!(apb_txn.addr_user inside mbox_valid_users) || apb_txn.slave_err) begin
                        do_reg_prediction = 1'b0;
                        // "Expected" read data is 0
                        soc_ifc_sb_apb_ap_output_transaction.rd_data = 0;
                    end
                end
            end
            //SHA Accelerator Functions
            "LOCK",
            "USER": begin
                if (apb_txn.read_or_write == APB3_TRANS_READ && apb_txn.slave_err) begin
                    do_reg_prediction = 1'b0;
                    // "Expected" read data is 0
                    soc_ifc_sb_apb_ap_output_transaction.rd_data = 0;
                end
            end
            "MODE",
            "START_ADDRESS",
            "DLEN": begin
                if (apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    do_reg_prediction = sha_valid_user(apb_txn) && (!apb_txn.slave_err);
                end
                else begin
                    if (apb_txn.slave_err) begin
                        do_reg_prediction = 1'b0;
                        // "Expected" read data is 0
                        soc_ifc_sb_apb_ap_output_transaction.rd_data = 0;
                    end
                end
            end
            "DATAIN": begin
                if (apb_txn.slave_err) begin
                    do_reg_prediction = 1'b0;
                    // "Expected" read data is 0
                    soc_ifc_sb_apb_ap_output_transaction.rd_data = 0;
                end
            end
            "EXECUTE": begin
                if (apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    do_reg_prediction = sha_valid_user(apb_txn) && (!apb_txn.slave_err);
                end
                else begin
                    if (apb_txn.slave_err) begin
                        do_reg_prediction = 1'b0;
                        // "Expected" read data is 0
                        soc_ifc_sb_apb_ap_output_transaction.rd_data = 0;
                    end
                end
            end
            "STATUS",
            ["DIGEST[0]":"DIGEST[9]"],
            ["DIGEST[10]":"DIGEST[15]"]:begin
                if (apb_txn.slave_err) begin
                    do_reg_prediction = 1'b0;
                    // "Expected" read data is 0
                    soc_ifc_sb_apb_ap_output_transaction.rd_data = 0;
                end
            end
            "CONTROL": begin
            end
            default: begin
                `uvm_info("PRED_APB", {"Enable reg prediction on access to ", axs_reg.get_name()}, UVM_FULL)
            end
        endcase
    end

    // Submit the transaction to reg_predictor to update mirrors
    if (do_reg_prediction) begin
        `uvm_info("PRED_APB", "Forwarding transaction to apb_reg_predictor", UVM_HIGH)
        // NOTE: BACKDOOR accesses, if ever used, will need some way to account
        //       for the PAUSER side-calculation
        soc_ifc_apb_reg_ap.write(apb_txn);
    end
    else begin
        `uvm_info("PRED_APB", $sformatf("Skipping reg prediction on access to register [%s]", axs_reg.get_full_name()), UVM_HIGH)
    end

    // Calculate any other system effects from the register access
    if (rdc_clk_gate_active || noncore_rst_out_asserted) begin
        `uvm_info("PRED_APB", {"On access to register: ", axs_reg.get_full_name(), " reset is asserted, skipping system prediction"}, UVM_MEDIUM)
    end
    else if (axs_reg == null) begin
        `uvm_error("PRED_APB", $sformatf("APB transaction to address: 0x%x decodes to null from soc_ifc_APB_map", apb_txn.addr))
    end
    else begin
        `uvm_info("PRED_APB", {"Detected access to register: ", axs_reg.get_full_name()}, UVM_MEDIUM)
        case (axs_reg.get_name()) inside
            "mbox_lock": begin
                // Reading mbox_lock when it is already locked has no effect, so
                // only calculate predictions on acquiring lock (rdata == 0)
                // which requires that the APB transfer was not blocked due to
                // invalid access
                if (do_reg_prediction &&
                    ~apb_txn.rd_data[p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_lsb_pos()] &&
                    p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value())
                begin
                    // Cannot put this inside the reg callback because the post_predict
                    // method has no way to access the addr_user value
                    `uvm_info("PRED_APB", $sformatf("Predicting new value [0x%x] for mbox_user as APB agent acquires lock",apb_txn.addr_user), UVM_HIGH)
                    p_soc_ifc_rm.mbox_csr_rm.mbox_user.predict(uvm_reg_data_t'(apb_txn.addr_user));
                    // Reset counters at beginning of command
                    datain_count = 0;
                    dataout_count = 0;
                    // Log the step for coverage
                    next_step = '{lock_acquire: 1'b1, default: 1'b0};
                    `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
                else begin
                    `uvm_info("PRED_APB", $sformatf("Access to mbox_lock of type %p has no effect", apb_txn.read_or_write), UVM_MEDIUM)
                    // Log the step for coverage
                    next_step = '{null_action: 1'b1, default: 1'b0};
                    `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
                void'(check_mbox_no_lock_error(apb_txn, axs_reg));
                void'(check_mbox_ooo_error(apb_txn, axs_reg));
                void'(check_mbox_inv_user_error(apb_txn, axs_reg));
                if (mailbox_data_avail && p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.mbox_error) begin
                    mailbox_data_avail = 1'b0;
                    send_soc_ifc_sts_txn = 1'b1;
                end
            end
            "mbox_user": begin
                if (check_mbox_no_lock_error(apb_txn, axs_reg) || check_mbox_ooo_error(apb_txn, axs_reg)) begin
                    `uvm_warning("PRED_APB", {"Access to RO register: ", axs_reg.get_name(), " triggers mailbox protocol violation"})
                end
                else if (mailbox_data_avail && p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.mbox_error) begin
                    mailbox_data_avail = 1'b0;
                    send_soc_ifc_sts_txn = 1'b1;
                end
                else begin
                    `uvm_info("PRED_APB", {"Read to ", axs_reg.get_name(), " has no effect on system"}, UVM_MEDIUM)
                end
                void'(check_mbox_inv_user_error(apb_txn, axs_reg));
                // Log the step for coverage
                next_step = '{null_action: 1'b1, default: 1'b0};
                `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
            end
            "mbox_cmd": begin
                void'(check_mbox_no_lock_error(apb_txn, axs_reg));
                void'(check_mbox_ooo_error(apb_txn, axs_reg));
                void'(check_mbox_inv_user_error(apb_txn, axs_reg));
                if (mailbox_data_avail && p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.mbox_error) begin
                    mailbox_data_avail = 1'b0;
                    send_soc_ifc_sts_txn = 1'b1;
                end
                if (apb_txn.read_or_write == APB3_TRANS_WRITE &&
                    do_reg_prediction &&
                    p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_cmd_stage) begin
                    // Log the step for coverage
                    next_step = '{cmd_wr: 1'b1, default: 1'b0};
                    `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
                else if (apb_txn.read_or_write == APB3_TRANS_READ && p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_receive_stage) begin
                    // Log the step for coverage
                    next_step = '{cmd_rd: 1'b1, default: 1'b0};
                    `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
                else begin
                    // Log the step for coverage
                    next_step = '{null_action: 1'b1, default: 1'b0};
                    `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
            end
            "mbox_dlen": begin
                void'(check_mbox_no_lock_error(apb_txn, axs_reg));
                void'(check_mbox_ooo_error(apb_txn, axs_reg));
                void'(check_mbox_inv_user_error(apb_txn, axs_reg));
                if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.mbox_error && mailbox_data_avail) begin
                    mailbox_data_avail = 1'b0;
                    send_soc_ifc_sts_txn = 1'b1;
                end
                if (apb_txn.read_or_write == APB3_TRANS_WRITE && do_reg_prediction) begin
                    // Log the step for coverage
                    if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_dlen_stage)
                        next_step = '{dlen_wr: 1'b1, default: 1'b0};
                    else if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_receive_stage)
                        next_step = '{resp_dlen_wr: 1'b1, default: 1'b0};
                    `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
                else if (apb_txn.read_or_write == APB3_TRANS_READ) begin
                    // Log the step for coverage
                    if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_receive_stage)
                        next_step = '{dlen_rd: 1'b1, default: 1'b0};
                    else if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_done_stage)
                        next_step = '{resp_dlen_rd: 1'b1, default: 1'b0};
                    `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
                else begin
                    // Log the step for coverage
                    next_step = '{null_action: 1'b1, default: 1'b0};
                    `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
            end
            "mbox_datain": begin
                `uvm_info("PRED_APB", $sformatf("Access to mailbox datain, write count: %d", datain_count), UVM_FULL)
                void'(check_mbox_no_lock_error(apb_txn, axs_reg));
                void'(check_mbox_ooo_error(apb_txn, axs_reg));
                void'(check_mbox_inv_user_error(apb_txn, axs_reg));
                if (mailbox_data_avail && p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.mbox_error) begin
                    mailbox_data_avail = 1'b0;
                    send_soc_ifc_sts_txn = 1'b1;
                end
                if (apb_txn.read_or_write == APB3_TRANS_WRITE && do_reg_prediction) begin
                    // Log the step for coverage
                    if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_data_stage)
                        next_step = '{datain_wr: 1'b1, default: 1'b0};
                    else
                        next_step = '{null_action: 1'b1, default: 1'b0};
                    `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
                else begin
                    // Log the step for coverage
                    next_step = '{null_action: 1'b1, default: 1'b0};
                    `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
            end
            "mbox_dataout": begin
                `uvm_info("PRED_APB", $sformatf("Access to mailbox dataout, read count: %d", dataout_count), UVM_FULL)
                void'(check_mbox_no_lock_error(apb_txn, axs_reg));
                void'(check_mbox_ooo_error(apb_txn, axs_reg));
                void'(check_mbox_inv_user_error(apb_txn, axs_reg));
                if (mailbox_data_avail && p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.mbox_error) begin
                    mailbox_data_avail = 1'b0;
                    send_soc_ifc_sts_txn = 1'b1;
                end
                // Log the step for coverage
                next_step = '{null_action: 1'b1, default: 1'b0};
                if (apb_txn.read_or_write == APB3_TRANS_READ && do_reg_prediction) begin
                    if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_receive_stage) begin
                        next_step = '{dataout_rd: 1'b1, default: 1'b0};
                    end
                    else if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_done_stage) begin
                        next_step = '{resp_dataout_rd: 1'b1, default: 1'b0};
                    end
                end
                `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
            end
            "mbox_execute": begin
                void'(check_mbox_no_lock_error(apb_txn, axs_reg));
                void'(check_mbox_ooo_error(apb_txn, axs_reg));
                void'(check_mbox_inv_user_error(apb_txn, axs_reg));
                if (mailbox_data_avail && p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.mbox_error) begin
                    mailbox_data_avail = 1'b0;
                    send_soc_ifc_sts_txn = 1'b1;
                end
                // Log the step for coverage
                next_step = '{null_action: 1'b1, default: 1'b0};
                if (apb_txn.read_or_write == APB3_TRANS_WRITE && do_reg_prediction) begin
                    // Log the step for coverage
                    if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_data_stage && p_soc_ifc_rm.mbox_csr_rm.mbox_execute.execute.get_mirrored_value()) begin
                        next_step = '{exec_set: 1'b1, default: 1'b0};
                    end
                    else if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_done_stage && !p_soc_ifc_rm.mbox_csr_rm.mbox_execute.execute.get_mirrored_value()) begin
                        next_step = '{exec_clr: 1'b1, default: 1'b0};
                    end
                end
                `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
            end
            "mbox_status": begin
                void'(check_mbox_no_lock_error(apb_txn, axs_reg));
                void'(check_mbox_ooo_error(apb_txn, axs_reg));
                void'(check_mbox_inv_user_error(apb_txn, axs_reg));
                if (mailbox_data_avail && p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.mbox_error) begin
                    mailbox_data_avail = 1'b0;
                    send_soc_ifc_sts_txn = 1'b1;
                end
                if (apb_txn.read_or_write == APB3_TRANS_WRITE && do_reg_prediction) begin
                    // Log the step for coverage
                    next_step = '{status_wr: 1'b1, default: 1'b0};
                    `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
                else if (apb_txn.read_or_write == APB3_TRANS_READ && do_reg_prediction) begin
                    // Log the step for coverage
                    next_step = '{status_rd: 1'b1, default: 1'b0};
                    `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
                else begin
                    // Log the step for coverage
                    next_step = '{null_action: 1'b1, default: 1'b0};
                    `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
                end
            end
            "mbox_unlock": begin
                void'(check_mbox_no_lock_error(apb_txn, axs_reg));
                void'(check_mbox_ooo_error(apb_txn, axs_reg));
                void'(check_mbox_inv_user_error(apb_txn, axs_reg));
                // Log the step for coverage
                next_step = '{null_action: 1'b1, default: 1'b0};
                `uvm_info("PRED_APB", $sformatf("Logged mailbox step [%p]", next_step), UVM_HIGH)
            end
            //SHA Accelerator Functions
            "LOCK": begin 
                // Reading sha_lock when it is already locked has no effect, so
                // only calculate predictions on acquiring lock (rdata == 0)
                // which requires that the AHB transfer was successful in
                // performing the access
                if (do_reg_prediction &&
                    ~apb_txn.rd_data[p_soc_ifc_rm.sha512_acc_csr_rm.LOCK.LOCK.get_lsb_pos()] &&
                    p_soc_ifc_rm.sha512_acc_csr_rm.LOCK.LOCK.get_mirrored_value())
                begin
                    // Cannot put this inside the reg callback because the post_predict
                    // method has no way to access the addr_user value
                    `uvm_info("PRED_APB", $sformatf("Predicting new value [0x%x] for sha_user as AHB agent acquires lock",apb_txn.addr_user), UVM_HIGH)
                    p_soc_ifc_rm.sha512_acc_csr_rm.USER.predict(uvm_reg_data_t'(apb_txn.addr_user));
                end
                else begin
                    `uvm_info("PRED_APB", $sformatf("Access to sha_lock of type %p has no effect", apb_txn.read_or_write), UVM_MEDIUM)
                end
            end
            "USER": begin
                if (apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    `uvm_warning("PRED_APB", {"Write to RO register: ", axs_reg.get_name(), " has no effect on system"})
                end
                else begin
                    `uvm_info("PRED_APB", {"Read to ", axs_reg.get_name(), " has no effect on system"}, UVM_MEDIUM)
                end
            end
            "MODE",
            "START_ADDRESS",
            "DLEN",
            "DATAIN",
            "EXECUTE",
            "STATUS",
            ["DIGEST[0]":"DIGEST[9]"],
            ["DIGEST[10]":"DIGEST[15]"],
            "CONTROL": begin
                `uvm_info("PRED_APB", $sformatf("Handling access to %s. Nothing to do.", axs_reg.get_name()), UVM_FULL)
            end
            "CPTRA_HW_ERROR_FATAL": begin
                if (apb_txn.read_or_write == APB3_TRANS_WRITE && |apb_txn.wr_data && (p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_HW_ERROR_FATAL.get_mirrored_value() == 0)) begin
                    `uvm_info("PRED_APB", $sformatf("Write to %s results in all bits cleared, but has no effect on cptra_error_fatal (requires reset)", axs_reg.get_name()), UVM_MEDIUM)
                end
            end
            "CPTRA_HW_ERROR_NON_FATAL": begin
                if (p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_HW_ERROR_NON_FATAL.get_mirrored_value() == 0) begin
                    cptra_error_non_fatal = 1'b0;
                end
            end
            "CPTRA_FW_ERROR_FATAL": begin
                if (apb_txn.read_or_write == APB3_TRANS_WRITE && |apb_txn.wr_data && (p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FW_ERROR_FATAL.get_mirrored_value() == 0)) begin
                    `uvm_info("PRED_APB", $sformatf("Write to %s results in all bits cleared, but has no effect on cptra_error_fatal (requires reset)", axs_reg.get_name()), UVM_MEDIUM)
                end
            end
            "CPTRA_FW_ERROR_NON_FATAL": begin
                if (p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FW_ERROR_NON_FATAL.get_mirrored_value() == 0) begin
                    cptra_error_non_fatal = 1'b0;
                end
            end
            "CPTRA_BOOT_STATUS",
            "CPTRA_FLOW_STATUS",
            "CPTRA_RESET_REASON",
            "CPTRA_SECURITY_STATE": begin
                if (apb_txn.read_or_write == APB3_TRANS_WRITE)
                    `uvm_info("PRED_APB", {"Write to ", axs_reg.get_name(), " has no effect"}, UVM_DEBUG)
            end
            ["CPTRA_MBOX_VALID_PAUSER[0]":"CPTRA_MBOX_VALID_PAUSER[4]"]: begin
                int idx = axs_reg.get_offset(p_soc_ifc_APB_map) - p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[0].get_offset(p_soc_ifc_APB_map);
                idx /= 4;
                if (mbox_valid_users_locked[idx] && apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    `uvm_error("PRED_APB", {"Write attempted to locked register: ", axs_reg.get_name()})
                end
                else if (apb_txn.read_or_write == APB3_TRANS_WRITE) begin
//                    mbox_valid_users[idx] = apb_txn.wr_data;
                end
            end
            ["CPTRA_MBOX_PAUSER_LOCK[0]":"CPTRA_MBOX_PAUSER_LOCK[4]"]: begin
                int idx = axs_reg.get_offset(p_soc_ifc_APB_map) - p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[0].get_offset(p_soc_ifc_APB_map);
                idx /= 4;
                if (mbox_valid_users_locked[idx] && apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    `uvm_error("PRED_APB", {"Write attempted to locked register: ", axs_reg.get_name()})
                end
                else if (apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    mbox_valid_users[idx] = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[idx].get_mirrored_value(); // VALID_PAUSER field is only applied when locked
                    mbox_valid_users_locked[idx] |= apb_txn.wr_data[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[idx].LOCK.get_lsb_pos()];
                    `uvm_info("PRED_APB", $sformatf("mbox_valid_users_locked[%d] set to 0x%x, mbox_valid_users[%d] has value: 0x%x", idx, mbox_valid_users_locked[idx], idx, mbox_valid_users[idx]), UVM_MEDIUM)
                end
                else begin
                    `uvm_info("PRED_APB", $sformatf("mbox_valid_users_locked[%d] read value 0x%x, mbox_valid_users[%d] has value: 0x%x", idx, mbox_valid_users_locked[idx], idx, mbox_valid_users[idx]), UVM_HIGH)
                end
            end
            ["CPTRA_TRNG_DATA[0]" : "CPTRA_TRNG_DATA[9]"],
            ["CPTRA_TRNG_DATA[10]" : "CPTRA_TRNG_DATA[11]"]: begin
                int idx = axs_reg.get_offset(p_soc_ifc_APB_map) - p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_TRNG_DATA[0].get_offset(p_soc_ifc_APB_map);
                idx /= 4;
                if (apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    trng_data[idx] = apb_txn.wr_data; // TODO can we just use the reg mirrors and remove this var?
//                    send_soc_ifc_sts_txn = 1'b1;
                end
//                else if (apb_txn.read_or_write == APB3_TRANS_READ) begin
//                    send_soc_ifc_sts_txn = 1'b0;
//                end
            end
            "CPTRA_TRNG_VALID_PAUSER",
            "CPTRA_TRNG_PAUSER_LOCK",
            "CPTRA_TRNG_CTRL",
            "CPTRA_TRNG_STATUS": begin
                // Handled in callbacks via reg predictor
                `uvm_info("PRED_APB", $sformatf("Handling access to %s. Nothing to do.", axs_reg.get_name()), UVM_DEBUG)
//                if (apb_txn.read_or_write == APB3_TRANS_WRITE && p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_TRNG_STATUS.DATA_WR_DONE.get_mirrored_value()) begin
//                    send_soc_ifc_sts_txn = 1'b1;
//                end
//                else if (apb_txn.read_or_write == APB3_TRANS_READ) begin
//                    send_soc_ifc_sts_txn = 1'b0;
//                end
            end
            "CPTRA_FUSE_WR_DONE": begin
                // Only expect a status transaction if this fuse download is occuring during boot sequence // FIXME
                // Even after a warm reset, we expect a write to this register (although the write is dropped)
                // When writing fuse done, if breakpoint is set we're going to wait state where noncore reset will be de-asserted
                // SoC or JTAG would check for boot fsm to be in wait state before setting GO when ready to advance and bring uc out of reset
                if (p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs.boot_fuse &&
                    apb_txn.wr_data[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FUSE_WR_DONE.done.get_lsb_pos()] &&
                    apb_txn.read_or_write == APB3_TRANS_WRITE)
                begin
                    //predict ready for fuses de-assertion
                    p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_fuses.predict(1'b0);
                    if (bootfsm_breakpoint) begin
                        // Similar logic should be tied to the fw_update_reset reg callback
                        p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs = '{boot_wait: 1'b1, default: 1'b0};
//                        uc_rst_out_asserted = 1; // No transition - this is already asserted on entry to boot_wait by merit of predict_reset("NONCORE")
                        fw_update_rst_window = 1'b1;
                        send_cptra_sts_txn = 1'b1;
                        `uvm_info("PRED_APB", $sformatf("Write to %s results in uc reset assertion and boot FSM state transition to %p", axs_reg.get_name(), p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs), UVM_HIGH)
                        fork
                            begin
                                fw_update_wait_count = p_soc_ifc_rm.soc_ifc_reg_rm.internal_fw_update_reset_wait_cycles.wait_cycles.get_mirrored_value();
                                repeat(32'(p_soc_ifc_rm.soc_ifc_reg_rm.internal_fw_update_reset_wait_cycles.wait_cycles.get_mirrored_value())) begin
                                    configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(1);
                                    if (fw_update_wait_count == 0)
                                        `uvm_fatal("PRED_APB", "Decrement will underflow!")
                                    fw_update_wait_count--;
                                end
                                if (!bootfsm_breakpoint) begin
                                    cptra_sb_ap_output_transaction_t local_cptra_sb_ap_txn;
                                    `uvm_info("PRED_APB", $sformatf("After expiration of fw_update reset counter, bootfsm_breakpoint is already cleared. Submitting transaction prediction immediately for state change."), UVM_HIGH)
                                    predict_boot_wait_boot_done();
                                    local_cptra_sb_ap_txn = cptra_sb_ap_output_transaction_t::type_id::create("local_cptra_sb_ap_txn");
                                    populate_expected_cptra_status_txn(local_cptra_sb_ap_txn); // fw_update_rst_window
                                    cptra_sb_ap.write(local_cptra_sb_ap_txn);
                                    `uvm_info("PRED_APB", "Transaction submitted through cptra_sb_ap", UVM_MEDIUM)
                                end
                                else begin
                                    `uvm_info("PRED_APB", $sformatf("After expiration of fw_update reset counter, bootfsm_breakpoint is still set. Predicted state change and reset signal updates will be handled on BOOTFSM_GO."), UVM_HIGH)
                                end
                            end
                        join_none
                    end
                    else begin
                        predict_boot_wait_boot_done();
//                        send_cptra_sts_txn = 1'b1; // fw_update_rst_window was never asserted
                        `uvm_info("PRED_APB", $sformatf("Write to %s results in uc reset deassertion and boot FSM state transition to %p", axs_reg.get_name(), p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs), UVM_HIGH)
                    end
                    fuse_update_enabled      = 1'b0;
                    send_soc_ifc_sts_txn     = 1'b1; // for ready_for_fuses
                end
                else begin
                    `uvm_info("PRED_APB", $sformatf("Write to %s has no effect on boot FSM due to state [%p] breakpoint [%d] and txn type [%p]", axs_reg.get_name(), p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs, bootfsm_breakpoint, apb_txn.read_or_write), UVM_FULL)
                end
            end
            "CPTRA_BOOTFSM_GO": begin
                // FIXME -- use reg predictor somehow?
                //When uc reset is still asserted and we're writing to bootfsm go, expect uc to be brough out of reset
                bit setting_go = apb_txn.read_or_write == APB3_TRANS_WRITE &&
                                 apb_txn.wr_data[p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_BOOTFSM_GO.GO.get_lsb_pos()];

                if (p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs.boot_wait &&
                    bootfsm_breakpoint &&
                    setting_go) begin

                    if (fw_update_wait_count == 0) begin
                        `uvm_info("PRED_APB", $sformatf("Write to %s results in boot FSM state transition and uC reset deassertion", axs_reg.get_name()), UVM_MEDIUM)
                        predict_boot_wait_boot_done();
                        send_cptra_sts_txn = 1'b1; // fw_update_rst_window
                    end
                    else begin
                        // State transition will be triggered in the thread spawned by CPTRA_FUSE_WR_DONE write instead
                        `uvm_info("PRED_APB", $sformatf("Write to %s clears bootfsm_breakpoint, but state transition is delayed by %d cycles", axs_reg.get_name(), fw_update_wait_count), UVM_HIGH)
                    end

                end
                else begin
                    `uvm_info("PRED_APB", $sformatf("Write to %s has no effect on boot FSM due to state [%p] breakpoint [%d] and 'setting_go' [%d]", axs_reg.get_name(), p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs, bootfsm_breakpoint, setting_go), UVM_DEBUG)
                end
                bootfsm_breakpoint &= ~setting_go;
            end
            "CPTRA_DBG_MANUF_SERVICE_REG": begin
                `uvm_info("PRED_APB", $sformatf("Handling access to %s. Nothing to do.", axs_reg.get_name()), UVM_DEBUG)
            end
            ["CPTRA_WDT_CFG[0]":"CPTRA_WDT_CFG[1]"],
            ["CPTRA_RSVD_REG[0]":"CPTRA_RSVD_REG[3]"]: begin
                `uvm_info("PRED_APB", {"Access to ", axs_reg.get_name(), " has no effect on system"}, UVM_MEDIUM)
            end
            ["fuse_uds_seed[0]" :"fuse_uds_seed[9]" ],
            ["fuse_uds_seed[10]":"fuse_uds_seed[11]"]: begin
                if (fuse_update_enabled) begin
                    send_cptra_sts_txn       = 1'b1;
                end
            end
            ["fuse_field_entropy[0]" :"fuse_field_entropy[7]" ]: begin
                if (fuse_update_enabled) begin
                    send_cptra_sts_txn       = 1'b1;
                end
            end
            ["fuse_key_manifest_pk_hash[0]" :"fuse_key_manifest_pk_hash[9]"],
            ["fuse_key_manifest_pk_hash[10]":"fuse_key_manifest_pk_hash[11]"],
            "fuse_key_manifest_pk_hash_mask",
            ["fuse_owner_pk_hash[0]" :"fuse_owner_pk_hash[9]"],
            ["fuse_owner_pk_hash[10]":"fuse_owner_pk_hash[11]"],
            "fuse_fmc_key_manifest_svn",
            ["fuse_runtime_svn[0]":"fuse_runtime_svn[3]"],
            "fuse_anti_rollback_disable",
            ["fuse_idevid_cert_attr[0]" :"fuse_idevid_cert_attr[9]"],
            ["fuse_idevid_cert_attr[10]":"fuse_idevid_cert_attr[19]"],
            ["fuse_idevid_cert_attr[20]":"fuse_idevid_cert_attr[23]"],
            ["fuse_idevid_manuf_hsm_id[0]":"fuse_idevid_manuf_hsm_id[3]"],
            "fuse_life_cycle",
            "fuse_lms_verify",
            "fuse_lms_revocation",
            "fuse_soc_stepping_id",
            ["internal_obf_key[0]":"internal_obf_key[7]"]: begin
                // Handled in callbacks via reg predictor
                `uvm_info("PRED_APB", $sformatf("Handling access to fuse/key/secret register %s. Nothing to do.", axs_reg.get_name()), UVM_DEBUG)
            end
            "internal_iccm_lock": begin
                // Handled in callbacks via reg predictor
                `uvm_info("PRED_APB", $sformatf("Handling access to register %s. Nothing to do.", axs_reg.get_name()), UVM_DEBUG)
            end
            "global_intr_en_r",
            "error_intr_en_r",
            "notif_intr_en_r",
            "error_intr_trig_r",
            "notif_intr_trig_r",
            "error_global_intr_r",
            "notif_global_intr_r",
            "error_internal_intr_r",
            "notif_internal_intr_r",
            "error_internal_intr_count_r",
            "error_inv_dev_intr_count_r",
            "error_cmd_fail_intr_count_r",
            "error_bad_fuse_intr_count_r",
            "error_iccm_blocked_intr_count_r",
            "error_mbox_ecc_unc_intr_count_r",
            "error_wdt_timer1_timeout_intr_count_r",
            "error_wdt_timer2_timeout_intr_count_r",
            "notif_cmd_avail_intr_count_r",
            "notif_mbox_ecc_cor_intr_count_r",
            "notif_debug_locked_intr_count_r",
            "notif_scan_mode_intr_count_r",
            "notif_soc_req_lock_intr_count_r",
            "notif_gen_in_toggle_intr_count_r",
            "error_internal_intr_count_incr_r",
            "error_inv_dev_intr_count_incr_r",
            "error_cmd_fail_intr_count_incr_r",
            "error_bad_fuse_intr_count_incr_r",
            "error_iccm_blocked_intr_count_incr_r",
            "error_mbox_ecc_unc_intr_count_incr_r",
            "error_wdt_timer1_timeout_intr_count_incr_r",
            "error_wdt_timer2_timeout_intr_count_incr_r",
            "notif_cmd_avail_intr_count_incr_r",
            "notif_mbox_ecc_cor_intr_count_incr_r",
            "notif_debug_locked_intr_count_incr_r",
            "notif_scan_mode_intr_count_incr_r",
            "notif_soc_req_lock_intr_count_incr_r",
            "notif_gen_in_toggle_intr_count_incr_r",
            "error0_intr_count_r",
            "error1_intr_count_r",
            "error2_intr_count_r",
            "error3_intr_count_r",
            "notif_cmd_done_intr_count_r",
            "error0_intr_count_incr_r",
            "error1_intr_count_incr_r",
            "error2_intr_count_incr_r",
            "error3_intr_count_incr_r",
            "notif_cmd_done_intr_count_incr_r": begin
                if (apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    `uvm_info("PRED_APB", {"Write to interrupt register ", axs_reg.get_name(), " is unsupported via APB interface and will be dropped"}, UVM_HIGH)
                end
                else begin
                    `uvm_info("PRED_APB", {"Read access to interrupt register ", axs_reg.get_name(), " will have no effect on system"}, UVM_HIGH)
                end
            end
            default: begin
                if (apb_txn.read_or_write == APB3_TRANS_WRITE) begin
                    `uvm_warning("PRED_APB", $sformatf("Prediction for writes to register '%s' unimplemented! Fix soc_ifc_predictor", axs_reg.get_name()))
                end
                else begin
                    `uvm_info("PRED_APB", $sformatf("Prediction for reads to register '%s' unimplemented! Fix soc_ifc_predictor", axs_reg.get_name()), UVM_LOW)
                end
            end
        endcase
    end

    fork
        begin
        // This allows coverage subscriber to observe both prev_step and next_step before the transition
        uvm_wait_for_nba_region();
        prev_step = next_step;
        end
    join_none

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
        soc_ifc_sb_apb_ap.write(soc_ifc_sb_apb_ap_output_transaction);
        `uvm_info("PRED_APB", "Transaction submitted through soc_ifc_sb_apb_ap", UVM_MEDIUM)
    end
    // pragma uvmf custom apb5_slave_0_ae_predictor end
  endfunction


endclass

// pragma uvmf custom external begin

// After delay jobs run and update the mailbox model state, calculate
// any transactions that are newly expected and send to the scoreboard.
function void soc_ifc_predictor::send_delayed_expected_transactions();
    bit send_soc_ifc_sts_txn = 0;
    bit send_cptra_sts_txn = 0;

    //////////////////////////////////////////////////
    // Construct one of each output transaction type.
    //
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");
    cptra_sb_ap_output_transaction = cptra_sb_ap_output_transaction_t::type_id::create("cptra_sb_ap_output_transaction");

    //////////////////////////////////////////////////
    // Check for any updates that may occur as a result of delayed jobs
    // from the mailbox model
    //
    // === mailbox_data_avail ===
    if (!mailbox_data_avail && p_soc_ifc_rm.mbox_csr_rm.mbox_execute.execute.get_mirrored_value() && p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_receive_stage) begin
        `uvm_info("PRED_DLY", "Observed mbox_execute being set after delay job, triggering mailbox_data_avail transition", UVM_HIGH)
        send_soc_ifc_sts_txn = 1'b1;
        mailbox_data_avail = p_soc_ifc_rm.mbox_csr_rm.mbox_execute.execute.get_mirrored_value();
    end
    // Clearing 'execute' - Expect sts pin change
    // Force unlock will also reset mailbox_data_avail, if set, but
    // will not reset any pending interrupts to uC because those
    // are sticky
    else if (mailbox_data_avail && !p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_receive_stage && !p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_done_stage) begin
        `uvm_info("PRED_DLY", $sformatf("Resetting mailbox_data_avail"), UVM_HIGH)
        send_soc_ifc_sts_txn = 1'b1;
        mailbox_data_avail = 1'b0;
    end
    // Write to mbox_status hands control back to SOC
    // if the status field is updated, the mbox flow has not been
    // interrupted by an unlock, and system is in
    // the expected state
    else if (!mailbox_data_avail && p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_done_stage &&
        p_soc_ifc_rm.mbox_csr_rm.mbox_status.status.get_mirrored_value() != CMD_BUSY &&
        !p_soc_ifc_rm.mbox_csr_rm.mbox_unlock.unlock.get_mirrored_value() && p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value()) begin
        `uvm_info("PRED_DLY", "Observed transition to soc_done_stage after delay job, triggering mailbox_data_avail transition", UVM_HIGH)
        mailbox_data_avail = 1'b1;
        send_soc_ifc_sts_txn = 1'b1;
    end
    // Write to mbox_status hands control back to uC
    else if (mailbox_data_avail && p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.uc_done_stage &&
             p_soc_ifc_rm.mbox_csr_rm.mbox_status.status.get_mirrored_value() != CMD_BUSY &&
             !p_soc_ifc_rm.mbox_csr_rm.mbox_unlock.unlock.get_mirrored_value() && p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value()) begin
        `uvm_info("PRED_DLY", "Observed transition to uc_done_stage after delay job, triggering mailbox_data_avail deassertion", UVM_HIGH)
        mailbox_data_avail = 1'b0;
        send_soc_ifc_sts_txn = 1'b1;
    end
    // === soc_ifc_notif_intr_pending ===
    // Setting 'execute' - Expect a uC interrupt if enabled
    if (!soc_ifc_notif_intr_pending && p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_mirrored_value()) begin
        `uvm_info("PRED_DLY", "Delay job triggers soc_ifc notification interrupt output", UVM_HIGH)
        soc_ifc_notif_intr_pending = 1'b1;
        send_cptra_sts_txn = 1'b1;
    end
    else if (soc_ifc_notif_intr_pending && !(p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_mirrored_value())) begin
        `uvm_info("PRED_DLY", "Delay job causes soc_ifc notification interrupt deassertion", UVM_HIGH)
        soc_ifc_notif_intr_pending = 1'b0;
    end

    // mbox protocol violations TODO
    if (!cptra_error_fatal && |p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_HW_ERROR_FATAL.get_mirrored_value()) begin
        `uvm_info("PRED_DLY", "Delay job triggers cptra_error_fatal output", UVM_HIGH)
        cptra_error_fatal = 1;
        send_soc_ifc_sts_txn = 1'b1;
    end
    if (!cptra_error_non_fatal && |p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_HW_ERROR_NON_FATAL.get_mirrored_value()) begin
        `uvm_info("PRED_DLY", "Delay job triggers cptra_error_non_fatal output", UVM_HIGH)
        cptra_error_non_fatal = 1;
        send_soc_ifc_sts_txn = 1'b1;
    end

    // Check for any Error Interrupt
    if (!soc_ifc_error_intr_pending && p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.error_en.get_mirrored_value()) begin
        `uvm_info("PRED_DLY", "Delay job triggers soc_ifc error_intr output", UVM_HIGH)
        soc_ifc_error_intr_pending = 1'b1;
        send_cptra_sts_txn = 1'b1;
    end
    else if (soc_ifc_error_intr_pending && !(p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.error_en.get_mirrored_value())) begin
        `uvm_info("PRED_DLY", "Delay job causes soc_ifc error_intr deassertion", UVM_HIGH)
        soc_ifc_error_intr_pending = 1'b0;
    end

    // Check for Timer Interrupt
    if (timer_intr_pending && mtime_lt_mtimecmp()) begin
        `uvm_info("PRED_DLY", $sformatf("Detected deassertion of timer interrupt"), UVM_HIGH)
        timer_intr_pending = 0;
//        send_cptra_sts_txn = 1; // No transaction captured on deassertion
    end
    else if (!timer_intr_pending && !mtime_lt_mtimecmp()) begin
        `uvm_info("PRED_DLY", $sformatf("Detected assertion of timer interrupt"), UVM_HIGH)
        timer_intr_pending = 1;
        send_cptra_sts_txn = 1;
    end

    // // Check for NMI Interrupt
    // if (!nmi_intr_pending && p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_HW_ERROR_FATAL.nmi_pin.get_mirrored_value()) begin
    //     `uvm_info("PRED_DLY", "Delay job triggers nmi interrupt output", UVM_MEDIUM)
    //     nmi_intr_pending = 1'b1;
    //     send_cptra_sts_txn = 1'b1;
    // end

    // SHA Accel Notification Interrupt
    // Expect a status transition on sha_notif_intr_pending
    // whenever a write changes the value of SHA Accelerator Execute
    // and triggers a delayed prediction job resulting in interrupt firing
    if (!sha_notif_intr_pending && p_soc_ifc_rm.sha512_acc_csr_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.sha512_acc_csr_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_mirrored_value()) begin
        sha_notif_intr_pending = 1;
        if (sha_notif_intr_pending) begin
            `uvm_info("PRED_DLY", "Delay job triggers sha_notif_intr_pending transition", UVM_HIGH)
            send_cptra_sts_txn = 1'b1;
        end
    end
    else if (sha_notif_intr_pending && !(p_soc_ifc_rm.sha512_acc_csr_rm.intr_block_rf_ext.notif_global_intr_r.agg_sts.get_mirrored_value() && p_soc_ifc_rm.sha512_acc_csr_rm.intr_block_rf_ext.global_intr_en_r.notif_en.get_mirrored_value())) begin
        `uvm_info("PRED_DLY", "Delay job causes sha512_acc notification interrupt deassertion", UVM_HIGH)
        sha_notif_intr_pending = 1'b0;
    end

    ///////////////// ORDERING MUST BE PRESERVED FOR THESE ASSIGNMENTS /////////////////
    // Check for uC reset changes (both transitions due to delay job
    // scheduled from internal_fw_update_reset callback)
    if (p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs.boot_wait && !uc_rst_out_asserted) begin
        uc_rst_out_asserted = 1;
        send_cptra_sts_txn = 1;
    end
    // uC reset deassertion is delayed from iccm_lock and fw_update_rst_window transitions
    else if (p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs.boot_done && !iccm_locked && !fw_update_rst_window && uc_rst_out_asserted) begin
        uc_rst_out_asserted = 0;
        send_cptra_sts_txn = 1;
    end

    if ((p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs.boot_fw_rst || p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs.boot_wait) && !fw_update_rst_window) begin
        fw_update_rst_window = 1;
        send_cptra_sts_txn = 1;
    end
    else if (p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs.boot_done && fw_update_rst_window) begin
        fw_update_rst_window = 0;
        send_cptra_sts_txn = 1;
    end

    // Check for iccm unlock change
    if (iccm_locked && ~|p_soc_ifc_rm.soc_ifc_reg_rm.internal_iccm_lock.lock.get_mirrored_value()) begin
        `uvm_info("PRED_DLY", $sformatf("Detected de-assertion of ICCM LOCK"), UVM_LOW)
        iccm_locked = 0;
        send_cptra_sts_txn = 1;
    end
    /////////////////            END ORDERED ASSIGNMENTS            /////////////////

    //////////////////////////////////////////////////
    // Send expected transactions to Scoreboard
    //
    if (send_soc_ifc_sts_txn) begin
        populate_expected_soc_ifc_status_txn(soc_ifc_sb_ap_output_transaction);
        soc_ifc_sb_ap.write(soc_ifc_sb_ap_output_transaction);
        `uvm_info("PRED_DLY", "Transaction submitted through soc_ifc_sb_ap", UVM_MEDIUM)
    end
    if (send_cptra_sts_txn) begin
        populate_expected_cptra_status_txn(cptra_sb_ap_output_transaction);
        cptra_sb_ap.write(cptra_sb_ap_output_transaction);
        `uvm_info("PRED_DLY", "Transaction submitted through cptra_sb_ap", UVM_MEDIUM)
    end
endfunction

// Time-delay jobs may be scheduled in the register model by a callback if
// it requires some time to elapse before e.g. updating mirror values.
// This task detects those scheduled jobs and runs them after waiting for
// the specified delay.
task soc_ifc_predictor::poll_and_run_delay_jobs();
    // FIXME reset!
    forever begin
        while (p_soc_ifc_rm.delay_jobs.size() > 0) begin
            fork
                soc_ifc_reg_delay_job job = p_soc_ifc_rm.delay_jobs.pop_front();
                begin
                    // delay cycles reported as 0's based value, since 1-cycle delay
                    // is inherent to this forever loop
                    if (job.get_delay_cycles()) configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(job.get_delay_cycles());
                    uvm_wait_for_nba_region();
                    job.do_job();
//                    p_soc_ifc_rm.sample_values(); /* Sample coverage after completing any delayed prediction/mirror updates */ // NOTE: Added sample post_predict callback to reg fields instead
                    send_delayed_expected_transactions();
                end
            join_none
        end
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(1);
    end
endtask

function bit soc_ifc_predictor::check_mbox_no_lock_error(soc_ifc_sb_apb_ap_output_transaction_t txn, uvm_reg axs_reg);
    soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error error_job;
    uvm_reg_field fld;
    bit is_error = 0;
    if (!p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value() && txn.addr_user inside mbox_valid_users) begin
        case (axs_reg.get_name()) inside
            "mbox_lock": begin
                fld = axs_reg.get_field_by_name("lock");
                is_error = txn.read_or_write == APB3_TRANS_WRITE;
            end
            "mbox_user": begin
                fld = axs_reg.get_field_by_name("user");
                is_error = txn.read_or_write == APB3_TRANS_WRITE;
            end
            "mbox_cmd": begin
                fld = axs_reg.get_field_by_name("command");
                is_error = txn.read_or_write == APB3_TRANS_WRITE;
            end
            "mbox_dlen": begin
                fld = axs_reg.get_field_by_name("length");
                is_error = txn.read_or_write == APB3_TRANS_WRITE;
            end
            "mbox_datain": begin
                fld = axs_reg.get_field_by_name("datain");
                is_error = txn.read_or_write == APB3_TRANS_WRITE;
            end
            "mbox_dataout": begin
                fld = axs_reg.get_field_by_name("dataout");
                is_error = 1;
            end
            "mbox_execute": begin
                fld = axs_reg.get_field_by_name("execute");
                is_error = txn.read_or_write == APB3_TRANS_WRITE;
            end
            "mbox_status": begin
                fld = axs_reg.get_field_by_name("status");
                is_error = txn.read_or_write == APB3_TRANS_WRITE;
            end
            "mbox_unlock": begin
                fld = axs_reg.get_field_by_name("unlock");
                is_error = txn.read_or_write == APB3_TRANS_WRITE;
            end
            default: begin
                `uvm_error("MBOX_NO_LOCK_CHK", "This function should not be called for access to non-mailbox regs")
            end
        endcase
    end
    if (is_error) begin
        error_job = soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error::type_id::create("error_job");
        error_job.rm = p_soc_ifc_rm.mbox_csr_rm;
        error_job.map = p_soc_ifc_APB_map;
        error_job.fld = fld;
        error_job.set_delay_cycles(0);
        error_job.state_nxt = MBOX_IDLE;
        error_job.error = '{axs_without_lock: 1'b1, default: 1'b0};
        p_soc_ifc_rm.delay_jobs.push_back(error_job);
        `uvm_info("MBOX_NO_LOCK_CHK", $sformatf("%s to %s on map [%s] with value [%x] causes a mbox no_lock protocol violation. Delay job is queued to update DUT model.", txn.read_or_write.name(), fld.get_name(), p_soc_ifc_APB_map.get_name(), txn.read_or_write == APB3_TRANS_WRITE ? txn.wr_data : txn.rd_data), UVM_HIGH)
    end
    return is_error;
endfunction

function bit soc_ifc_predictor::check_mbox_ooo_error(soc_ifc_sb_apb_ap_output_transaction_t txn, uvm_reg axs_reg);
    soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error error_job;
    uvm_reg_field fld;
    bit is_error = 0;
    // Only check for access-out-of-order errors here that will not be caught
    // by reg prediction callbacks.
    // That means that register accesses where valid_requester/valid_receiver is false
    // (as applicable to the register in question) might trigger an error if the inverse
    // is true (valid_receiver/valid_requester).
    // When !soc_has_lock, valid_receiver must be true for any writes made,
    // but not necessarily valid_requester.
    // Since valid_requester may be false, the reg_prediction is not done, and
    // thus the callback can't catch this scenario).
    if (txn.addr_user inside mbox_valid_users) begin
        case (axs_reg.get_name()) inside
            "mbox_lock": begin
                fld = axs_reg.get_field_by_name("lock");
                is_error = txn.read_or_write == APB3_TRANS_WRITE && !p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.mbox_idle;
            end
            "mbox_user": begin
                fld = axs_reg.get_field_by_name("user");
                is_error = txn.read_or_write == APB3_TRANS_WRITE && !p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.mbox_idle;
            end
            "mbox_cmd": begin
                fld = axs_reg.get_field_by_name("command");
                is_error = txn.read_or_write == APB3_TRANS_WRITE &&  valid_receiver(txn) && !valid_requester(txn);
            end
            "mbox_dlen": begin
                fld = axs_reg.get_field_by_name("length");
                is_error = txn.read_or_write == APB3_TRANS_WRITE &&  valid_receiver(txn) && !valid_requester(txn);
            end
            "mbox_datain": begin
                fld = axs_reg.get_field_by_name("datain");
                is_error = txn.read_or_write == APB3_TRANS_WRITE &&  valid_receiver(txn) && !valid_requester(txn);
            end
            "mbox_dataout": begin
                fld = axs_reg.get_field_by_name("dataout");
                is_error =                                          !valid_receiver(txn) &&  valid_requester(txn);
            end
            "mbox_execute": begin
                fld = axs_reg.get_field_by_name("execute");
                is_error = txn.read_or_write == APB3_TRANS_WRITE &&  valid_receiver(txn) && !valid_requester(txn);
            end
            "mbox_status": begin
                fld = axs_reg.get_field_by_name("status");
                is_error = txn.read_or_write == APB3_TRANS_WRITE && !valid_receiver(txn) &&  valid_requester(txn);
            end
            "mbox_unlock": begin
                fld = axs_reg.get_field_by_name("unlock");
                is_error = txn.read_or_write == APB3_TRANS_WRITE && !p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.mbox_idle;
            end
            default: begin
                `uvm_error("MBOX_OOO_CHK", "This function should not be called for access to non-mailbox regs")
            end
        endcase
    end
    if (is_error) begin
        error_job = soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error::type_id::create("error_job");
        error_job.rm = p_soc_ifc_rm.mbox_csr_rm;
        error_job.map = p_soc_ifc_APB_map;
        error_job.fld = fld;
        error_job.set_delay_cycles(0);
        error_job.state_nxt = MBOX_ERROR;
        error_job.error = '{axs_incorrect_order: 1'b1, default: 1'b0};
        p_soc_ifc_rm.delay_jobs.push_back(error_job);
        `uvm_info("MBOX_OOO_CHK", $sformatf("%s to %s on map [%s] with value [%x] causes a mbox out_of_order protocol violation. Delay job is queued to update DUT model.", txn.read_or_write.name(), fld.get_name(), p_soc_ifc_APB_map.get_name(), txn.read_or_write == APB3_TRANS_WRITE ? txn.wr_data : txn.rd_data), UVM_HIGH)
        p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs = '{mbox_error: 1'b1, default: 1'b0};
    end
    return is_error;
endfunction

function bit soc_ifc_predictor::check_mbox_inv_user_error(soc_ifc_sb_apb_ap_output_transaction_t txn, uvm_reg axs_reg);
    bit is_error = 0;
    // The invalid PAUSER error is only flagged for write attempts by an agent
    // that is considered 'valid', but which currently doesn't have lock
    // (exception: reads to mbox_dataout while not holding lock also flagged)
    if (txn.addr_user inside mbox_valid_users) begin
        case (axs_reg.get_name()) inside
            "mbox_lock":    is_error = txn.read_or_write == APB3_TRANS_WRITE && !(valid_requester(txn)                       );
            "mbox_user":    is_error = txn.read_or_write == APB3_TRANS_WRITE && !(valid_requester(txn)                       );
            "mbox_cmd":     is_error = txn.read_or_write == APB3_TRANS_WRITE && !(valid_requester(txn)                       );
            "mbox_dlen":    is_error = txn.read_or_write == APB3_TRANS_WRITE && !(valid_requester(txn) || valid_receiver(txn));
            "mbox_datain":  is_error = txn.read_or_write == APB3_TRANS_WRITE && !(valid_requester(txn)                       );
            "mbox_dataout": is_error =                                          !(valid_requester(txn) || valid_receiver(txn));
            "mbox_execute": is_error = txn.read_or_write == APB3_TRANS_WRITE && !(valid_requester(txn)                       );
            "mbox_status":  is_error = txn.read_or_write == APB3_TRANS_WRITE && !(valid_requester(txn) || valid_receiver(txn));
            // Unwriteable via APB, but writes still don't flag a PAUSER invalid error
            "mbox_unlock":  is_error = txn.read_or_write == APB3_TRANS_WRITE && !(valid_requester(txn)                       );
            default: `uvm_error("MBOX_INV_USER_CHK", "This function should not be called for access to non-mailbox regs")
        endcase
    end
    if (is_error) begin
        p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.error_inv_dev_sts.predict(1'b1, -1, UVM_PREDICT_READ, UVM_PREDICT, p_soc_ifc_AHB_map); /* AHB-access only, use AHB map*/
        `uvm_info("MBOX_INV_USER_CHK", $sformatf("%s to %s on map [%s] with user [0x%x] causes a mbox invalid PAUSER detection.", txn.read_or_write.name(), axs_reg.get_name(), p_soc_ifc_APB_map.get_name(), txn.addr_user), UVM_LOW)
    end
    return is_error;
endfunction

task soc_ifc_predictor::update_mtime_mirrors();
    typedef longint unsigned mtime_type;
    mtime_type mtime;
    mtime_type new_mtime;

    mtime = p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_l.count_l.get_mirrored_value() |
            p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_h.count_h.get_mirrored_value() << 32;
    new_mtime = mtime + 1; // In clock cycles

    fork
        if (p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_l.is_busy()) begin
            uvm_wait_for_nba_region();
            // If mtime_l transitions from busy to not busy on the current clock edge, leave the mirror at the value it just acquired instead of overwriting
            // (unless the value was not updated by the recent transfer, e.g. because it was an APB transfer)
            // Else, predict a new value (which will be overwritten later when the active transfer completes)
            if (p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_l.is_busy() || (mtime[31:00] == p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_l.count_l.get_mirrored_value())) begin
                p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_l.count_l.predict(new_mtime[31:00], .kind(UVM_PREDICT_WRITE), .path(UVM_PREDICT), .map(p_soc_ifc_AHB_map));
            end
            new_mtime[31:00] = p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_l.count_l.get_mirrored_value();
        end
        else begin
            p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_l.count_l.predict(new_mtime[31:00]);
        end
        if (p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_h.is_busy()) begin
            uvm_wait_for_nba_region();
            // If mtime_h transitions from busy to not busy on the current clock edge, leave the mirror at the value it just acquired instead of overwriting
            // (unless the value was not updated by the recent transfer, e.g. because it was an APB transfer)
            // Else, predict a new value (which will be overwritten later when the active transfer completes)
            if (p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_h.is_busy() || (mtime[63:32] == p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_h.count_h.get_mirrored_value())) begin
                p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_h.count_h.predict(new_mtime[63:32], .kind(UVM_PREDICT_WRITE), .path(UVM_PREDICT), .map(p_soc_ifc_AHB_map));
            end
            new_mtime[63:32] = p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_h.count_h.get_mirrored_value();
        end
        else begin
            p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_h.count_h.predict(new_mtime[63:32]);
        end
    join

    `uvm_info("PRED", $sformatf("Updated mtime register mirrors to 0x%x", new_mtime), UVM_DEBUG)
endtask

// Increment mtime every clock cycle
task soc_ifc_predictor::mtime_counter_task();
    forever begin
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(1);
        if (cptra_pwrgood_asserted) begin
            update_mtime_mirrors();
            send_delayed_expected_transactions();
        end
    end
endtask

function bit soc_ifc_predictor::mtime_lt_mtimecmp();
    longint unsigned mtime;
    longint unsigned mtimecmp;

    mtime = p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_l.count_l.get_mirrored_value() |
            p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtime_h.count_h.get_mirrored_value() << 32;
    mtimecmp = p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtimecmp_l.compare_l.get_mirrored_value() |
               p_soc_ifc_rm.soc_ifc_reg_rm.internal_rv_mtimecmp_h.compare_h.get_mirrored_value() << 32;

    return mtime < mtimecmp;
endfunction

//If WDT is enabled via reg write, emulate behavior here
task soc_ifc_predictor::wdt_counter_task();
    bit timer1_debug_flag, timer2_debug_flag;
    forever begin
        uvm_reg_data_t wdt_reg_data;
        logic wdt_t1_en;
        logic wdt_t2_en;
        logic cascade, independent;
        logic [63:0] wdt_t1_period, wdt_t2_period;
        bit wdt_t1_restart_temp;

        cptra_sb_ap_output_transaction_t local_cptra_sb_ap_txn;
        local_cptra_sb_ap_txn = cptra_sb_ap_output_transaction_t::type_id::create("local_cptra_sb_ap_txn");

        //Poll for WDT enable bits
        wdt_reg_data = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER1_EN.timer1_en.get(); //_mirrored_value();
        wdt_t1_en = wdt_reg_data[0];

        wdt_reg_data = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER2_EN.timer2_en.get(); //_mirrored_value();
        wdt_t2_en = wdt_reg_data[0];
    
        cascade = (wdt_t1_en && !wdt_t2_en);
        independent = wdt_t2_en;

        wdt_reg_data = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[0].timer1_timeout_period.get();
        wdt_t1_period[31:0] = wdt_reg_data[31:0];
        wdt_reg_data = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[1].timer1_timeout_period.get();
        wdt_t1_period[63:32] = wdt_reg_data[31:0];

        wdt_reg_data = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[0].timer2_timeout_period.get();
        wdt_t2_period[31:0] = wdt_reg_data[31:0];
        wdt_reg_data = p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[1].timer2_timeout_period.get();
        wdt_t2_period[63:32] = wdt_reg_data[31:0];

        //Reset event
        if (this.reset_wdt_count) begin
            `uvm_info("PRED_WDT", "Resetting WDT t1 and t2 counts due to a reset event", UVM_HIGH)
            this.t1_count = 'h0;
            this.t2_count = 'h0;
            this.wdt_error_intr_sent = 1'b0;
            this.wdt_t2_error_intr_sent = 1'b0;
            this.wdt_nmi_intr_sent = 1'b0;
        end

        //Cascade mode
        if (cascade) begin
            if (this.wdt_t1_restart) begin
                this.t1_count = 'h0;
                `uvm_info("PRED_WDT", "Cascade mode, received t1 pet - restarting t1 count", UVM_MEDIUM)
                this.wdt_t1_restart = 1'b0; //Reset flag so we can capture another restart event
            end
            else if (this.t1_count != wdt_t1_period) begin
                this.t1_count++;
                if (!($time % 500))
                    `uvm_info("PRED_WDT", $sformatf("In cascade mode. t1_count increments to 0x%x, wdt_to_period is 0x%x", this.t1_count, wdt_t1_period), UVM_DEBUG)
            end
            else begin
                //T1 expired, so send out soc error intr, and start t2 counter
                if (!this.wdt_error_intr_sent) begin
                    `uvm_info("PRED_WDT", "Timer1 expired in cascade mode. Starting timer2", UVM_MEDIUM)
                    p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.error_wdt_timer1_timeout_sts.predict(1'b1, -1, UVM_PREDICT_READ, UVM_PREDICT, p_soc_ifc_AHB_map);
                    
                    //Set a flag so we don't keep sending transactions while the timer holds value until interrupt
                    //is serviced or reset
                    this.wdt_error_intr_sent = 1'b1;
                end

                if (this.wdt_t2_restart) begin
                    `uvm_error("PRED_WDT", "Cascade mode, received t2 pet - unexpected t2 pet!")
                end
                else if (this.t2_count != wdt_t2_period) begin
                    this.t2_count++;
                    if (!($time % 500))
                        `uvm_info("PRED_WDT", $sformatf("In cascade mode. t2_count increments to 0x%x, wdt_to_period is 0x%x", this.t2_count, wdt_t2_period), UVM_DEBUG)
                end
                else begin
                    if (!this.wdt_nmi_intr_sent) begin
                        `uvm_info("PRED_WDT", "Timer2 expired in cascade mode. Expecting NMI to be handled", UVM_MEDIUM);
                        p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_HW_ERROR_FATAL.nmi_pin.predict(1'b1, -1, UVM_PREDICT_READ, UVM_PREDICT, p_soc_ifc_AHB_map); //TODO: use default map?
                        
                        //Sending cptra_status_txn in the same clock as NMI
                        nmi_intr_pending = 1'b1;
                        populate_expected_cptra_status_txn(local_cptra_sb_ap_txn);
                        cptra_sb_ap.write(local_cptra_sb_ap_txn);

                        //Set a flag so we don't keep sending transactions while the timer holds value until interrupt
                        //is serviced or reset
                        this.wdt_nmi_intr_sent = 1'b1;
                    end
                end
            end
        end //Cascade mode
        else if (independent) begin
            if (this.wdt_t1_restart) begin
                this.t1_count = 'h0;
                `uvm_info("PRED_WDT", "Independent mode, received t1 pet - restarting t1 count", UVM_MEDIUM)
                this.wdt_t1_restart = 1'b0; //Reset flag so we can capture another restart event
            end
            else if (this.t1_count != wdt_t1_period) begin
                this.t1_count++;
                if (!($time % 500))
                    `uvm_info("PRED_WDT", $sformatf("In independent mode. t1_count increments to 0x%x, wdt_to_period is 0x%x", this.t1_count, wdt_t1_period), UVM_DEBUG)
            end
            else begin
                //T1 expired, so send out soc error intr
                if (!this.wdt_error_intr_sent) begin
                    `uvm_info("PRED_WDT", "Independent mode, T1 expired", UVM_MEDIUM)
                    p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.error_wdt_timer1_timeout_sts.predict(1'b1, -1, UVM_PREDICT_READ, UVM_PREDICT, p_soc_ifc_AHB_map);
                    
                    //Set a flag so we don't keep sending transactions while the timer holds value until interrupt
                    //is serviced or reset
                    this.wdt_error_intr_sent = 1'b1;
                    timer1_debug_flag = 0;
                end
                else if (!timer1_debug_flag) begin
                    `uvm_info("PRED_WDT", "Independent mode, T1 expired, but wdt_error_intr_sent is already set!", UVM_DEBUG)
                    timer1_debug_flag = 1;
                end
            end
            //-------------------------------------------------
            //Timer 2
            //-------------------------------------------------
            if (this.wdt_t2_restart) begin
                this.t2_count = 'h0;
                `uvm_info("PRED_WDT", "Independent mode, received t2 pet - restarting t2 count", UVM_MEDIUM)
                this.wdt_t2_restart = 1'b0; //Reset flag so we can capture another restart event
            end
            else if (this.t2_count != wdt_t2_period) begin
                this.t2_count++;
                if (!($time % 500))
                    `uvm_info("PRED_WDT", $sformatf("In independent mode. t2_count increments to 0x%x, wdt_to_period is 0x%x", this.t2_count, wdt_t2_period), UVM_DEBUG)
            end
            else begin
                //T2 expired, so send out soc error intr
                if (!this.wdt_t2_error_intr_sent) begin
                    `uvm_info("PRED_WDT", "Independent mode, T2 expired", UVM_MEDIUM)
                    p_soc_ifc_rm.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.error_wdt_timer2_timeout_sts.predict(1'b1, -1, UVM_PREDICT_READ, UVM_PREDICT, p_soc_ifc_AHB_map);
                    
                    //Set a flag so we don't keep sending transactions while the timer holds value until interrupt
                    //is serviced or reset
                    this.wdt_t2_error_intr_sent = 1'b1;
                    timer2_debug_flag = 0;
                end
                else if (!timer2_debug_flag) begin
                    `uvm_info("PRED_WDT", "Independent mode, T2 expired, but wdt_t2_error_intr_sent is already set!", UVM_DEBUG)
                    timer2_debug_flag = 1;
                end
            end

        end //Independent mode

        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(1);
        // Hit an issue where this task would make predictions and schedule delay jobs before poll_and_run_delay_jobs() had
        // kicked off the current cycle's jobs - so delay jobs (to intr pins) were not being delayed.
        // Stall until after the task poll_and_run_delay_jobs has already forked delay jobs before reentering wdt loop and predicting new updates
        uvm_wait_for_nba_region();

    end //forever
endtask


function bit soc_ifc_predictor::soc_ifc_status_txn_expected_after_noncore_reset();
    /* FIXME calculate all of these from the reg-model somehow? */
    return ready_for_fw_push || ready_for_runtime || mailbox_data_avail || |generic_output_wires /*|| trng_req_pending*/; /* only expect a soc_ifc_status_transaction if some signal will transition */
endfunction

function bit soc_ifc_predictor::cptra_status_txn_expected_after_noncore_reset();
    /* FIXME calculate this from the reg-model somehow? */
    // NOTE: Interrupt signals deasserting (due to reset) will not result in a
    //       status transaction, because only interrupt rising edges are detected
    return !noncore_rst_out_asserted ||
           !uc_rst_out_asserted      ||
           iccm_locked               ||
           |nmi_vector;
endfunction

function bit soc_ifc_predictor::soc_ifc_status_txn_expected_after_warm_reset();
    // Most soc_ifc_status signals are actually reset by the noncore reset assertion (later)
    // instead of the cptra_rst_b
    return p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_fuses.get_mirrored_value();
endfunction

function bit soc_ifc_predictor::cptra_status_txn_expected_after_warm_reset();
    // NOTE: Almost all (maybe all?) cptra_status signals persists across warm reset
    //       until it cascades into the assertion of noncore reset.
    return 0;
endfunction

function bit soc_ifc_predictor::soc_ifc_status_txn_expected_after_cold_reset();
    return soc_ifc_status_txn_expected_after_warm_reset() || soc_ifc_status_txn_expected_after_noncore_reset(); /* all resets are expected in conjunction with cold */
endfunction

function bit soc_ifc_predictor::cptra_status_txn_expected_after_cold_reset();
    return cptra_status_txn_expected_after_warm_reset() || cptra_status_txn_expected_after_noncore_reset(); /* all resets are expected in conjunction with cold */
endfunction

function bit soc_ifc_predictor::valid_requester(input uvm_transaction txn);
    soc_ifc_sb_ahb_ap_output_transaction_t ahb_txn;
    soc_ifc_sb_apb_ap_output_transaction_t apb_txn;
    if ($cast(ahb_txn,txn)) begin
        valid_requester = p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value() &&
                          (!p_soc_ifc_rm.mbox_csr_rm.mbox_status.soc_has_lock.get_mirrored_value() ||
                           (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.uc_receive_stage));
        if (!valid_requester) begin
            string msg = $sformatf("valid_requester is false!\nmbox_lock: %d\nmbox_status.soc_has_lock: %d\nmbox_fn_state_sigs: %p",
                                   p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value(),
                                   p_soc_ifc_rm.mbox_csr_rm.mbox_status.soc_has_lock.get_mirrored_value(),
                                   p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs);
            `uvm_info("PRED_VALID_REQ", msg, UVM_FULL)
        end
        else begin
            `uvm_info("PRED_VALID_REQ", "valid_requester is true", UVM_DEBUG)
        end
        return valid_requester;
    end
    else if ($cast(apb_txn,txn)) begin
        valid_requester = p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value() &&
                          p_soc_ifc_rm.mbox_csr_rm.mbox_status.soc_has_lock.get_mirrored_value() &&
                          p_soc_ifc_rm.mbox_csr_rm.mbox_user.get_mirrored_value() == apb_txn.addr_user;
        if (!valid_requester) begin
            string msg = $sformatf("valid_requester is false!\nmbox_lock: %d\nmbox_status.soc_has_lock: %d\naddr_user: 0x%x\nmbox_user: 0x%x",
                                   p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value(),
                                   p_soc_ifc_rm.mbox_csr_rm.mbox_status.soc_has_lock.get_mirrored_value(),
                                   apb_txn.addr_user,
                                   p_soc_ifc_rm.mbox_csr_rm.mbox_user.get_mirrored_value());
            `uvm_info("PRED_VALID_REQ", msg, UVM_FULL)
        end
        else begin
            `uvm_info("PRED_VALID_REQ", "valid_requester is true", UVM_DEBUG)
        end
        return valid_requester;
    end
    else begin
        `uvm_error("PRED_VALID_REQ", "valid_requester received invalid transaction - cannot cast as AHB or APB!")
        valid_requester = 0;
        return valid_requester;
    end
endfunction

function bit soc_ifc_predictor::valid_receiver(input uvm_transaction txn);
    soc_ifc_sb_ahb_ap_output_transaction_t ahb_txn;
    soc_ifc_sb_apb_ap_output_transaction_t apb_txn;
    if ($cast(ahb_txn,txn)) begin
        valid_receiver = p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value() &&
                         p_soc_ifc_rm.mbox_csr_rm.mbox_status.soc_has_lock.get_mirrored_value() &&
                         p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.uc_receive_stage;
        if (!valid_receiver) begin
            string msg = $sformatf("valid_receiver is false!\nmbox_lock: %d\nmbox_status.soc_has_lock: %d\nmbox_fn_state_sigs: %p",
                                   p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value(),
                                   p_soc_ifc_rm.mbox_csr_rm.mbox_status.soc_has_lock.get_mirrored_value(),
                                   p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs);
            `uvm_info("PRED_VALID_RCV", msg, UVM_FULL)
        end
        else begin
            `uvm_info("PRED_VALID_RCV", "valid_receiver is true", UVM_DEBUG)
        end
        return valid_receiver;
    end
    else if ($cast(apb_txn,txn)) begin
        if (!p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value())
            valid_receiver = 0;
        else if (p_soc_ifc_rm.mbox_csr_rm.mbox_status.soc_has_lock.get_mirrored_value())
            valid_receiver = p_soc_ifc_rm.mbox_csr_rm.mbox_user.get_mirrored_value() == apb_txn.addr_user &&
                             p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_done_stage;
        else
            valid_receiver = apb_txn.addr_user inside {mbox_valid_users} &&
                             p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.soc_receive_stage;
        if (!valid_receiver) begin
            string msg = $sformatf("valid_receiver is false!\nmbox_lock: %d\nmbox_status.soc_has_lock: %d\nmbox_fn_state_sigs: %p\naddr_user: 0x%x\nvalid_users: %p",
                                   p_soc_ifc_rm.mbox_csr_rm.mbox_lock.lock.get_mirrored_value(),
                                   p_soc_ifc_rm.mbox_csr_rm.mbox_status.soc_has_lock.get_mirrored_value(),
                                   p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs,
                                   apb_txn.addr_user,
                                   mbox_valid_users);
            `uvm_info("PRED_VALID_RCV", msg, UVM_FULL)
        end
        else begin
            `uvm_info("PRED_VALID_RCV", "valid_receiver is true", UVM_DEBUG)
        end
        return valid_receiver;
    end
    else begin
        `uvm_error("PRED_VALID_RCV", "valid_receiver received invalid transaction - cannot cast as AHB or APB!")
        valid_receiver = 0;
        return valid_receiver;
    end
endfunction

function bit soc_ifc_predictor::sha_valid_user(input uvm_transaction txn);
    soc_ifc_sb_ahb_ap_output_transaction_t ahb_txn;
    soc_ifc_sb_apb_ap_output_transaction_t apb_txn;
    if ($cast(ahb_txn,txn)) begin
        sha_valid_user = p_soc_ifc_rm.sha512_acc_csr_rm.LOCK.LOCK.get_mirrored_value() &&
                        !p_soc_ifc_rm.sha512_acc_csr_rm.STATUS.SOC_HAS_LOCK.get_mirrored_value();
        if (!sha_valid_user) begin
            string msg = $sformatf("sha_valid_user is false!\nsha_lock: %d\nsha_accel_status.soc_has_lock: %d",
                                   p_soc_ifc_rm.sha512_acc_csr_rm.LOCK.LOCK.get_mirrored_value(),
                                   p_soc_ifc_rm.sha512_acc_csr_rm.STATUS.SOC_HAS_LOCK.get_mirrored_value());
            `uvm_info("PRED_VALID_SHA", msg, UVM_HIGH)
        end
        else begin
            `uvm_info("PRED_VALID_SHA", "sha_valid_user is true", UVM_DEBUG)
        end
        return sha_valid_user;
    end
    else if ($cast(apb_txn,txn)) begin
        sha_valid_user = p_soc_ifc_rm.sha512_acc_csr_rm.LOCK.LOCK.get_mirrored_value() &&
                         p_soc_ifc_rm.sha512_acc_csr_rm.STATUS.SOC_HAS_LOCK.get_mirrored_value() &&
                         p_soc_ifc_rm.sha512_acc_csr_rm.USER.get_mirrored_value() == apb_txn.addr_user;
        if (!sha_valid_user) begin
            string msg = $sformatf("sha_valid_user is false!\nsha_lock: %d\nsha_status.soc_has_lock: %d\naddr_user: 0x%x\nsha_user: 0x%x",
                                   p_soc_ifc_rm.sha512_acc_csr_rm.LOCK.LOCK.get_mirrored_value(),
                                   p_soc_ifc_rm.sha512_acc_csr_rm.STATUS.SOC_HAS_LOCK.get_mirrored_value(),
                                   apb_txn.addr_user,
                                   p_soc_ifc_rm.sha512_acc_csr_rm.USER.get_mirrored_value());
            `uvm_info("PRED_VALID_SHA", msg, UVM_HIGH)
        end
        else begin
            `uvm_info("PRED_VALID_SHA", "sha_valid_user is true", UVM_DEBUG)
        end
        return sha_valid_user;
    end
    else begin
        `uvm_error("PRED_VALID_SHA", "sha_valid_user received invalid transaction - cannot cast as AHB or APB!")
        sha_valid_user = 0;
        return sha_valid_user;
    end
endfunction

function void soc_ifc_predictor::predict_boot_wait_boot_done();
    cptra_sb_ap_output_transaction_t local_cptra_sb_ap_txn;

    p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs = '{boot_done: 1'b1, default: 1'b0};
    fw_update_rst_window                           = 1'b0;

    fork
        begin
            configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(1);
            if (uc_rst_out_asserted) begin
                uc_rst_out_asserted   = 1'b0;
                local_cptra_sb_ap_txn = cptra_sb_ap_output_transaction_t::type_id::create("local_cptra_sb_ap_txn");
                populate_expected_cptra_status_txn(local_cptra_sb_ap_txn);
                cptra_sb_ap.write(local_cptra_sb_ap_txn);
                `uvm_info("PRED_BOOT", "Transaction submitted through cptra_sb_ap", UVM_MEDIUM)
            end
        end
    join_none

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
        `uvm_fatal("PRED_HANDLE_RESET", "Failed to retrieve triggered reset_flag")
    if (kind_handled != kind_predicted)
        `uvm_error("PRED_HANDLE_RESET", $sformatf("handle_reset called with different reset type [%s] than was processed in predictor [%s]!", kind_handled.get_name(), kind_predicted.get_name()))
endtask

function void soc_ifc_predictor::predict_reset(input string kind = "HARD");
    uvm_reg all_regs[$];
    reset_flag last_predicted_kind = null;

    `uvm_info("PRED_RESET", $sformatf("Predicting reset of kind: %p", kind), UVM_LOW)

    // Monitor the assertion of internal resets, which assert instantly for HARD reset
    // but are delayed slightly from SOFT resets
    if (kind == "HARD") begin: IMMEDIATE_INTERNAL_RESET_ASSERTION
        `uvm_info("PRED_RESET", $sformatf("Reset prediction of kind: %p results in immediate assertion of internal resets", kind), UVM_MEDIUM)
        noncore_rst_out_asserted = 1'b1;
        uc_rst_out_asserted = 1'b1;
        rdc_clk_gate_active = 1'b1;
    end
    else if (kind == "SOFT") begin
        fork
            begin: DELAY_INTERNAL_RESET_ASSERTION
            cptra_sb_ap_output_transaction_t local_cptra_sb_ap_txn;
            soc_ifc_sb_ap_output_transaction_t local_soc_ifc_sb_ap_txn;
            bit send_soc_ifc_sts_txn = soc_ifc_status_txn_expected_after_noncore_reset();

            // Do the noncore reset
            `uvm_info("PRED_RESET", $sformatf("Reset prediction of kind: %p results in assertion of internal resets after a delay", kind), UVM_MEDIUM)
            configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(3); // FIXME, correct delay value?
            predict_reset("NONCORE");

            // Send predicted transactions
            if (1) begin
                local_cptra_sb_ap_txn = cptra_sb_ap_output_transaction_t::type_id::create("local_cptra_sb_ap_txn");
                populate_expected_cptra_status_txn(local_cptra_sb_ap_txn);
                cptra_sb_ap.write(local_cptra_sb_ap_txn);
                `uvm_info("PRED_RESET", "Transaction submitted through cptra_sb_ap", UVM_MEDIUM)
            end
            if (send_soc_ifc_sts_txn) begin
                local_soc_ifc_sb_ap_txn = soc_ifc_sb_ap_output_transaction_t::type_id::create("local_soc_ifc_sb_ap_txn");
                populate_expected_soc_ifc_status_txn(local_soc_ifc_sb_ap_txn);
                soc_ifc_sb_ap.write(local_soc_ifc_sb_ap_txn);
                `uvm_info("PRED_RESET", "Transaction submitted through soc_ifc_sb_ap", UVM_MEDIUM)
            end
            end: DELAY_INTERNAL_RESET_ASSERTION
        join_none
    end
    else if (kind == "NONCORE") begin: IMMEDIATE_INTERNAL_RESET_DEASSERTION
        `uvm_info("PRED_RESET", $sformatf("Reset prediction of kind: %p results in assertion of internal resets", kind), UVM_MEDIUM)
        noncore_rst_out_asserted = 1'b1;
        uc_rst_out_asserted = 1'b1;
        rdc_clk_gate_active = 1'b1;
    end

    // Track the BOOT FSM internally
    if (kind inside {"HARD", "SOFT"}) begin: BOOT_FSM_THREAD
        p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs = '{boot_idle: 1'b1, default: 1'b0};
        // schedule the delayed transition to next state
        // Wait for the reset deassertion transactions to be detected, indicating
        // BOOT FSM can progress and subsequent
        fork
            begin
                cptra_sb_ap_output_transaction_t local_cptra_sb_ap_txn;
                `uvm_info("PRED_RESET", $sformatf("Reset prediction of kind: %p will result in state change after reset deasserts. Wait for cptra_rst_b==1...", kind), UVM_MEDIUM)
                while (last_predicted_kind != soft_reset_flag) begin
                    uvm_object obj_predicted;
                    reset_predicted.wait_ptrigger_data(obj_predicted);
                    reset_predicted.wait_off();
                    $cast(last_predicted_kind,obj_predicted);
                    `uvm_info("PRED_RESET", $sformatf("After reset_predicted was cleared, last predicted kind was: %s", last_predicted_kind.get_name()), UVM_MEDIUM)
                end
                p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs = '{boot_fuse: 1'b1, default: 1'b0};
                `uvm_info("PRED_RESET", $sformatf("After detecting warm reset deassertion, boot FSM state change predicted: [%p]", p_soc_ifc_rm.soc_ifc_reg_rm.boot_fn_state_sigs), UVM_MEDIUM)
                // NOTE: Next state progression is triggered by write to CPTRA_FUSE_WR_DONE

                // Now, deassertion of noncore reset is delayed from state transition by 2 cycles
                configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(2); // FIXME, correct delay value?
                noncore_rst_out_asserted = 1'b0;

                // Send predicted transactions
                if (1) begin
                    local_cptra_sb_ap_txn = cptra_sb_ap_output_transaction_t::type_id::create("local_cptra_sb_ap_txn");
                    populate_expected_cptra_status_txn(local_cptra_sb_ap_txn);
                    cptra_sb_ap.write(local_cptra_sb_ap_txn);
                    `uvm_info("PRED_RESET", "Transaction submitted through cptra_sb_ap", UVM_MEDIUM)
                end
            end
        join_none
    end

    // Predict value changes due to reset
    fw_update_wait_count = 0;

    if (kind inside {"HARD", "SOFT"}) begin: RESET_VAL_CHANGES_HARD_SOFT
        soc_ifc_rst_in_asserted = 1'b1;
        p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_FLOW_STATUS.ready_for_fuses.predict(1'b0);

        cptra_error_fatal = 1'b0;
        cptra_error_non_fatal = 1'b0;
    end: RESET_VAL_CHANGES_HARD_SOFT

    // Signals that are tied to reg values are not reset by warm reset until it
    // propagates to the internal resets
    // FIXME: Do a reg-model reset and then extract these from the reg_model???
    if (kind inside {"HARD", "NONCORE"}) begin: RESET_VAL_CHANGES_HARD_NONCORE
        ready_for_fw_push = 1'b0;
        ready_for_runtime = 1'b0;
        nmi_vector = '0;
        iccm_locked = 1'b0;
        mailbox_data_avail = 1'b0;
        soc_ifc_error_intr_pending = 1'b0;
        soc_ifc_notif_intr_pending = 1'b0;
        sha_err_intr_pending = 1'b0;
        sha_notif_intr_pending = 1'b0;

        generic_output_wires = '0;

        //WDT
        nmi_intr_pending = 1'b0; //Reset nmi_intr on reset assertion
        reset_wdt_count = 1'b1;

        // FIXME get rid of this variable?
        mbox_valid_users        = '{p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[0].PAUSER.get_reset(kind),
                                    p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[1].PAUSER.get_reset(kind),
                                    p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[2].PAUSER.get_reset(kind),
                                    p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[3].PAUSER.get_reset(kind),
                                    p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[4].PAUSER.get_reset(kind),
                                    p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[0].PAUSER.get_reset(kind)/*This entry is for the non-programmable default value */};
        mbox_valid_users_locked =  {p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[0].LOCK.get_reset(kind),
                                    p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[1].LOCK.get_reset(kind),
                                    p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[2].LOCK.get_reset(kind),
                                    p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[3].LOCK.get_reset(kind),
                                    p_soc_ifc_rm.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[4].LOCK.get_reset(kind)};

        trng_data_req = 1'b0;

        // Mailbox 'step' represents how the current transaction affects the mailbox
        // flow, and is used for coverage.
        if (p_soc_ifc_rm.mbox_csr_rm.mbox_fn_state_sigs.mbox_idle)
            next_step = '{null_action: 1'b1, default: 1'b0};
        else
            next_step = '{reset: 1'b1, default: 1'b0};
        fork
            begin
            // This allows coverage subscriber to observe both prev_step and next_step before the transition
            uvm_wait_for_nba_region();
            prev_step = next_step;
            end
        join_none

        datain_count = 0;
        dataout_count = 0;

    end: RESET_VAL_CHANGES_HARD_NONCORE

    if (kind == "HARD") begin: RESET_VAL_CHANGES_HARD
        cptra_pwrgood_asserted = 1'b0;
        timer_intr_pending = 1'b1;
        fuse_update_enabled = 1'b1; // Fuses only latch new values from APB write after a cold-reset (which clears CPTRA_FUSE_WR_DONE)
    end: RESET_VAL_CHANGES_HARD

    // TODO clear the delay_jobs queue?

    // HARD reset is the default for a reg-model
    // FIXME SOFT reset is not fully defined for our reg-model yet
    // FIXME move this to env?
    p_soc_ifc_rm.reset(kind);

    if (kind inside {"HARD","NONCORE"}) begin: RESET_REG_BUSY_NONCORE_HARD
        // If any reg access was in progress when reset occurred, clear the busy
        // flag (since the APB/AHB sequencers and any mailbox sequences were killed).
        // We don't run this for warm/soft resets because cptra_rst_b doesn't immediately
        // reset the AHB interface, so pending transactions might still complete.
        p_soc_ifc_rm.get_registers(all_regs, UVM_HIER);
        foreach (all_regs[ii]) begin
            if (all_regs[ii].is_busy()) begin
                `uvm_info("PRED_RESET", $sformatf("After resetting the reg-model, found a busy reg: [%s]. Resetting the busy bit.", all_regs[ii].get_full_name()), UVM_FULL)
                // TODO: This is not in the official API, and the 'reset' function doesn't
                //       automatically clear busy. Not sure how to do this properly
                all_regs[ii].Xset_busyX(0);
            end
        end
    end: RESET_REG_BUSY_NONCORE_HARD

    // TODO skip key reset for SOFT reset type?
    soc_ifc_status_txn_key = 0;
    cptra_status_txn_key = 0;
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
    txn.cptra_error_fatal_intr_pending     = this.cptra_error_fatal;
    txn.cptra_error_non_fatal_intr_pending = this.cptra_error_non_fatal;
    txn.trng_req_pending                   = this.trng_data_req;
    txn.generic_output_val                 = this.generic_output_wires;
    txn.set_key(soc_ifc_status_txn_key++);
endfunction

function void soc_ifc_predictor::populate_expected_cptra_status_txn(ref cptra_sb_ap_output_transaction_t txn);
    txn.noncore_rst_asserted       = this.noncore_rst_out_asserted;
    txn.uc_rst_asserted            = this.uc_rst_out_asserted;
    txn.fw_update_rst_window       = this.fw_update_rst_window;
    txn.soc_ifc_err_intr_pending   = this.soc_ifc_error_intr_pending;
    txn.soc_ifc_notif_intr_pending = this.soc_ifc_notif_intr_pending;
    txn.sha_err_intr_pending       = this.sha_err_intr_pending;
    txn.sha_notif_intr_pending     = this.sha_notif_intr_pending;
    txn.timer_intr_pending         = this.timer_intr_pending;
    txn.cptra_obf_key_reg          = this.cptra_obf_key_reg;
    txn.obf_field_entropy          = this.get_expected_obf_field_entropy();
    txn.obf_uds_seed               = this.get_expected_obf_uds_seed();
    txn.nmi_vector                 = this.nmi_vector;
    txn.nmi_intr_pending           = this.nmi_intr_pending;
    txn.iccm_locked                = this.iccm_locked;
    txn.set_key(cptra_status_txn_key++);
endfunction

// pragma uvmf custom external end
