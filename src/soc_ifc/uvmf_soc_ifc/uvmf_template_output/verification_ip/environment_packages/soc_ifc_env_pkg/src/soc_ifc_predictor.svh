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
  bit soc_ifc_err_intr_pending = 1'b0;
  bit soc_ifc_notif_intr_pending = 1'b0;
  bit sha_err_intr_pending = 1'b0;
  bit sha_notif_intr_pending = 1'b0;
  bit ready_for_fuses = 1'b0;
  bit [31:0] nmi_vector = 32'h0;
  soc_ifc_reg_model_top  p_soc_ifc_rm;
  uvm_reg_map p_soc_ifc_APB_map; // Block map
  uvm_reg_map p_soc_ifc_AHB_map; // Block map

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


    if (!t.assert_rst) begin // No Status transaction expected if the latest control transaction still asserted SoC reset
        if (soc_ifc_rst_in_asserted) begin
            soc_ifc_rst_in_asserted = 1'b0;
            ready_for_fuses = 1'b1;
            noncore_rst_out_asserted = 1'b1;
            uc_rst_out_asserted = 1'b1;
            send_soc_ifc_sts_txn = 1;
        end
        else begin
            //TODO beyond detecting uc_rst_asserted, this block needs more logic
            noncore_rst_out_asserted = 1'b0; // <-- all status transactions after the first one should reflect Caliptra reset deasserted
            uc_rst_out_asserted = 1'b1; // FIXME
            send_cptra_sts_txn = 1;
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
    `uvm_info("PRED", "Transaction Received through cptra_ctrl_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");
    cptra_sb_ap_output_transaction = cptra_sb_ap_output_transaction_t::type_id::create("cptra_sb_ap_output_transaction");
    soc_ifc_sb_ahb_ap_output_transaction = soc_ifc_sb_ahb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ahb_ap_output_transaction");
    soc_ifc_sb_apb_ap_output_transaction = soc_ifc_sb_apb_ap_output_transaction_t::type_id::create("soc_ifc_sb_apb_ap_output_transaction");

    if (t.iccm_axs_blocked) begin
        soc_ifc_err_intr_pending = 1'b1; // <-- Error caused by blocked ICCM write
        send_cptra_sts_txn = 1;
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
    axs_reg = p_soc_ifc_AHB_map.get_reg_by_offset(ahb_txn.address);

    if (axs_reg == null) begin
        `uvm_error("PRED_AHB", $sformatf("AHB transaction to address: 0x%x decodes to null from soc_ifc_AHB_map", ahb_txn.address))
    end
    else if (uvm_reg_data_t'(ahb_txn.data[0]) != axs_reg.get() && ahb_txn.RnW == AHB_WRITE) begin
        `uvm_error("PRED_AHB", $sformatf("AHB transaction to register %s with data: 0x%x, write: %p, may not match reg model value: %x", axs_reg.get_name(), ahb_txn.data[0], ahb_txn.RnW, axs_reg.get()))
    end
    else begin
        case (axs_reg.get_name()) inside
            "fuse_done": begin
                `uvm_error("PRED_AHB", "Unexpected write to fuse_done register on AHB interface")
            end
            "nmi_vector": begin
                if (ahb_txn.RnW == AHB_WRITE) begin
                    send_cptra_sts_txn = 1;
                    nmi_vector = ahb_txn.data[0][31:0];
                end
            end
            default: begin
                `uvm_warning("PRED_AHB", $sformatf("Prediction for accesses to register '%s' unimplemented! Fix soc_ifc_predictor", axs_reg.get_name()))
            end
        endcase
    end

    `uvm_info("INCOMPLETE_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The soc_ifc_predictor::write_ahb_slave_0_ae function needs to be completed with DUT prediction model",UVM_NONE)

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
        case (axs_reg.get_name()) inside
            "fuse_done": begin
                if (apb_txn.wr_data != axs_reg.get() && apb_txn.read_or_write == APB3_TRANS_WRITE)
                    `uvm_error("PRED_APB", $sformatf("APB transaction with data: 0x%x, write: %p, may not match reg model value: %x", apb_txn.wr_data, apb_txn.read_or_write, axs_reg.get()))
                // Only expect a status transaction if this fuse download is occuring during boot sequence // FIXME
                if (noncore_rst_out_asserted && (apb_txn.wr_data == 1/*FIXME hardcoded*/)) begin
                    noncore_rst_out_asserted = 1'b0; // FIXME get this from a status analysis port?
                    send_cptra_sts_txn = 1'b1;
                    ready_for_fuses = 1'b0;
                    send_soc_ifc_sts_txn = 1'b1;
                end
            end
            ["uds_seed[0]" :"uds_seed[9]" ],
            ["uds_seed[10]":"uds_seed[11]"]: begin
                `uvm_info("PRED_APB", {"Detected access to register: ", axs_reg.get_name()}, UVM_MEDIUM)
            end
            ["field_entropy[0]" :"field_entropy[9]" ],
            ["field_entropy[10]":"field_entropy[19]"],
            ["field_entropy[20]":"field_entropy[29]"],
            ["field_entropy[30]":"field_entropy[31]"]: begin
                `uvm_info("PRED_APB", {"Detected access to register: ", axs_reg.get_name()}, UVM_MEDIUM)
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
function void soc_ifc_predictor::populate_expected_soc_ifc_status_txn(ref soc_ifc_sb_ap_output_transaction_t txn);
    txn.ready_for_fuses    = this.ready_for_fuses;
    txn.ready_for_fw_push  = 1'b0; // FIXME
    txn.ready_for_runtime  = 1'b0; // FIXME
    txn.mailbox_data_avail = 1'b0; // FIXME
    txn.mailbox_flow_done  = 1'b0; // FIXME
    txn.generic_output_val = 64'b0; // FIXME
endfunction

function void soc_ifc_predictor::populate_expected_cptra_status_txn(ref cptra_sb_ap_output_transaction_t txn);
    txn.noncore_rst_asserted       = this.noncore_rst_out_asserted;
    txn.uc_rst_asserted            = this.uc_rst_out_asserted;
    txn.soc_ifc_err_intr_pending   = this.soc_ifc_err_intr_pending;
    txn.soc_ifc_notif_intr_pending = this.soc_ifc_notif_intr_pending;
    txn.sha_err_intr_pending       = this.sha_err_intr_pending;
    txn.sha_notif_intr_pending     = this.sha_notif_intr_pending;
    txn.cptra_obf_key_reg          = '0; // TODO
    txn.obf_field_entropy          = '0; // TODO
    txn.obf_uds_seed               = '0; // TODO
    txn.nmi_vector                 = nmi_vector;
    txn.iccm_locked                = '0; // TODO
endfunction
// pragma uvmf custom external end

