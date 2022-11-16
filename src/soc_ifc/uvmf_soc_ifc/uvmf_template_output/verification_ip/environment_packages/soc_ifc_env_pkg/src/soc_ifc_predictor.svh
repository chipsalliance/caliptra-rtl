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
//   ahb_slave_0_ae receives transactions of type  mvc_sequence_item_base
//   apb5_slave_0_ae receives transactions of type  mvc_sequence_item_base
//
//   This analysis component has the following analysis_ports that can broadcast
//   the listed transaction type.
//
//  soc_ifc_sb_ap broadcasts transactions of type soc_ifc_status_transaction
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


  // Transaction variable for predicted values to be sent out soc_ifc_sb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction.
  typedef soc_ifc_status_transaction soc_ifc_sb_ap_output_transaction_t;
  soc_ifc_sb_ap_output_transaction_t soc_ifc_sb_ap_output_transaction;
  // Code for sending output transaction out through soc_ifc_sb_ap
  // soc_ifc_sb_ap.write(soc_ifc_sb_ap_output_transaction);

  // Define transaction handles for debug visibility
  soc_ifc_ctrl_transaction soc_ifc_ctrl_agent_ae_debug;
  mvc_sequence_item_base ahb_slave_0_ae_debug;
  mvc_sequence_item_base apb5_slave_0_ae_debug;


  // pragma uvmf custom class_item_additional begin
  bit soc_ifc_rst_in_asserted = 1'b1;
  bit soc_ifc_rst_out_asserted = 1'b1;
  soc_ifc_reg_model_top  p_soc_ifc_rm;
  uvm_reg_map p_soc_ifc_APB_map; // Block map
  uvm_reg_map p_soc_ifc_AHB_map; // Block map
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
    ahb_slave_0_ae = new("ahb_slave_0_ae", this);
    apb5_slave_0_ae = new("apb5_slave_0_ae", this);
    soc_ifc_sb_ap =new("soc_ifc_sb_ap", this );
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
    soc_ifc_ctrl_agent_ae_debug = t;
    `uvm_info("CTRL_PRED", "Transaction Received through soc_ifc_ctrl_agent_ae", UVM_MEDIUM)
    `uvm_info("CTRL_PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");
    if (!t.assert_rst) begin // No Status transaction expected if the latest control transaction still asserted SoC reset
        if (soc_ifc_rst_in_asserted) begin
            soc_ifc_rst_in_asserted = 1'b0;
            soc_ifc_sb_ap_output_transaction.ready_for_fuses = 1'b1; // <-- this is what we expect to change
            soc_ifc_sb_ap_output_transaction.uc_rst_asserted = 1'b1;
            soc_ifc_sb_ap_output_transaction.err_intr_pending = 1'b0;
            soc_ifc_sb_ap_output_transaction.notif_intr_pending = 1'b0;
            soc_ifc_sb_ap_output_transaction.ready_for_fw_push = 1'b0;
            soc_ifc_sb_ap_output_transaction.ready_for_runtime = 1'b0;
            soc_ifc_sb_ap_output_transaction.mailbox_data_avail = 1'b0;
            soc_ifc_sb_ap_output_transaction.mailbox_flow_done = 1'b0;
            soc_ifc_sb_ap_output_transaction.generic_output_val = 1'b0;
            soc_ifc_sb_ap_output_transaction.cptra_obf_key_reg = 1'b0;
            soc_ifc_sb_ap_output_transaction.obf_field_entropy = 1'b0;
            soc_ifc_sb_ap_output_transaction.obf_uds_seed = 1'b0;
        end
        else begin
            //TODO beyond detecting uc_rst_asserted, this block needs more logic
            soc_ifc_sb_ap_output_transaction.ready_for_fuses = 1'b0;
            soc_ifc_sb_ap_output_transaction.uc_rst_asserted = 1'b0; // <-- all status transactions after the first one should reflect Caliptra reset deasserted
            soc_ifc_sb_ap_output_transaction.err_intr_pending = 1'b0;
            soc_ifc_sb_ap_output_transaction.notif_intr_pending = 1'b0;
            soc_ifc_sb_ap_output_transaction.ready_for_fw_push = 1'b0;
            soc_ifc_sb_ap_output_transaction.ready_for_runtime = 1'b0;
            soc_ifc_sb_ap_output_transaction.mailbox_data_avail = 1'b0;
            soc_ifc_sb_ap_output_transaction.mailbox_flow_done = 1'b0;
            soc_ifc_sb_ap_output_transaction.generic_output_val = 1'b0;
            soc_ifc_sb_ap_output_transaction.cptra_obf_key_reg = 1'b0;
            soc_ifc_sb_ap_output_transaction.obf_field_entropy = 1'b0;
            soc_ifc_sb_ap_output_transaction.obf_uds_seed = 1'b0;
        end

        // Code for sending output transaction out through soc_ifc_sb_ap
        // Please note that each broadcasted transaction should be a different object than previously
        // broadcasted transactions.  Creation of a different object is done by constructing the transaction
        // using either new() or create().  Broadcasting a transaction object more than once to either the
        // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
        soc_ifc_sb_ap.write(soc_ifc_sb_ap_output_transaction);
        `uvm_info("CTRL_PRED", "Transaction submitted through soc_ifc_sb_ap", UVM_MEDIUM)
    end
    // pragma uvmf custom soc_ifc_ctrl_agent_ae_predictor end
  endfunction

  // FUNCTION: write_ahb_slave_0_ae
  // Transactions received through ahb_slave_0_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_ahb_slave_0_ae(mvc_sequence_item_base t);
    // pragma uvmf custom ahb_slave_0_ae_predictor begin
    ahb_slave_0_ae_debug = t;
    `uvm_info("AHB_PRED", "Transaction Received through ahb_slave_0_ae", UVM_MEDIUM)
    `uvm_info("AHB_PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.
    // TODO cast t as:
    //   ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH)

    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The soc_ifc_predictor::write_ahb_slave_0_ae function needs to be completed with DUT prediction model",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)

    // Code for sending output transaction out through soc_ifc_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction
    // using either new() or create().  Broadcasting a transaction object more than once to either the
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    soc_ifc_sb_ap.write(soc_ifc_sb_ap_output_transaction);
    `uvm_info("AHB_PRED", "Transaction submitted through soc_ifc_sb_ap", UVM_MEDIUM)
    // pragma uvmf custom ahb_slave_0_ae_predictor end
  endfunction

  // FUNCTION: write_apb5_slave_0_ae
  // Transactions received through apb5_slave_0_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_apb5_slave_0_ae(mvc_sequence_item_base t);
    // pragma uvmf custom apb5_slave_0_ae_predictor begin
    apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT, apb5_master_0_params::APB3_PADDR_BIT_WIDTH, apb5_master_0_params::APB3_PWDATA_BIT_WIDTH, apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_txn;
    uvm_reg            axs_reg;
    bit send_sts_txn = 1'b0;
    apb5_slave_0_ae_debug = t;

    `uvm_info("APB_PRED", "Transaction Received through apb5_slave_0_ae", UVM_MEDIUM)
    `uvm_info("APB_PRED", {"            Data: ",t.convert2string()}, UVM_FULL)

    // Construct one of each output transaction type.
    soc_ifc_sb_ap_output_transaction = soc_ifc_sb_ap_output_transaction_t::type_id::create("soc_ifc_sb_ap_output_transaction");

    $cast(apb_txn, t);
    axs_reg = p_soc_ifc_APB_map.get_reg_by_offset(apb_txn.addr);

    if (axs_reg == null) begin
        `uvm_error("APB_PRED", $sformatf("APB transaction to address: 0x%x decodes to null from soc_ifc_APB_map", apb_txn.addr))
    end
    else begin
        case (axs_reg.get_name()) inside
            "fuse_done": begin
                if (apb_txn.wr_data != axs_reg.get() || apb_txn.read_or_write == APB3_TRANS_READ)
                    `uvm_error("APB_PRED", $sformatf("APB transaction with data: 0x%x, write: %p, may not match reg model value: %x", apb_txn.wr_data, apb_txn.read_or_write, axs_reg.get()))
                // Only expect a status transaction if this fuse download is occuring during boot sequence // FIXME
                if (soc_ifc_rst_out_asserted && (apb_txn.wr_data == 1/*FIXME hardcoded*/)) begin
                    soc_ifc_rst_out_asserted = 1'b0; // FIXME get this from a status analysis port?
                    send_sts_txn = 1'b1;
                end
            end
            default: begin
                `uvm_warning("APB_PRED", $sformatf("Prediction for accesses to register '%s' unimplemented! Fix soc_ifc_predictor", axs_reg.get_name()))
            end
        endcase
    end

    // Code for sending output transaction out through soc_ifc_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction
    // using either new() or create().  Broadcasting a transaction object more than once to either the
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    if (send_sts_txn) begin
        soc_ifc_sb_ap_output_transaction.ready_for_fuses = 1'b0; // <-- no APB access should result in ready_for_fuses being set to 1 // FIXME
        soc_ifc_sb_ap_output_transaction.uc_rst_asserted = soc_ifc_rst_out_asserted;
        soc_ifc_sb_ap_output_transaction.err_intr_pending = 1'b0;
        soc_ifc_sb_ap_output_transaction.notif_intr_pending = 1'b0;
        soc_ifc_sb_ap_output_transaction.ready_for_fw_push = 1'b0; // FIXME
        soc_ifc_sb_ap_output_transaction.ready_for_runtime = 1'b0; // FIXME
        soc_ifc_sb_ap_output_transaction.mailbox_data_avail = 1'b0; // FIXME
        soc_ifc_sb_ap_output_transaction.mailbox_flow_done = 1'b0; // FIXME
        soc_ifc_sb_ap_output_transaction.generic_output_val = 1'b0; // FIXME
        soc_ifc_sb_ap_output_transaction.cptra_obf_key_reg = 1'b0; // FIXME
        soc_ifc_sb_ap_output_transaction.obf_field_entropy = 1'b0; // FIXME
        soc_ifc_sb_ap_output_transaction.obf_uds_seed = 1'b0; // FIXME
        soc_ifc_sb_ap.write(soc_ifc_sb_ap_output_transaction);
        `uvm_info("APB_PRED", "Transaction submitted through soc_ifc_sb_ap", UVM_MEDIUM)
    end
    // pragma uvmf custom apb5_slave_0_ae_predictor end
  endfunction


endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

