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

  //Local lock shadow — avoids UVM RAL mirror race where reg.write() frontdoor
  //updates the mirror before the AHB monitor broadcasts to this predictor.
  //RTL swwel uses the PREVIOUS cycle's lock value, so we need to track it ourselves.
  bit [PV_NUM_PCR-1:0] ctrl_lock_shadow;
  logic [7:0] ctrl_data_shadow[PV_NUM_PCR];
  bit [PV_NUM_PCR-1:0] clear_pending;
  string pv_dut_path = "hdl_top.dut";
  logic [PV_DATA_W-1:0] pcr_word[PV_NUM_PCR][PV_NUM_DWORDS];
  bit word_dirty[PV_NUM_PCR][PV_NUM_DWORDS];
  int mirror_jobs[$];
  typedef struct packed {
    logic [PV_ADDR_W-1:0] addr;
    logic [PV_DATA_W-1:0] data;
  } ahb_read_snapshot_t;
  ahb_read_snapshot_t ahb_read_snapshots[$];
  pv_sb_ahb_ap_output_transaction_t completed_ahb_reads[$];

  function void update_word(int entry, int offset, logic [PV_DATA_W-1:0] data);
    pcr_word[entry][offset] = data;
    if (!word_dirty[entry][offset]) mirror_jobs.push_back(entry*PV_NUM_DWORDS+offset);
    word_dirty[entry][offset] = 1;
  endfunction

  // RAL can be busy during a crypto frontdoor write. Retain the accepted WORD
  // independently and defer only its mirror update, never its expected value.
  function void flush_word_mirrors();
    int index, entry, offset, count;
    uvm_reg r;
    count = mirror_jobs.size();
    repeat (count) begin
      index = mirror_jobs.pop_front();
      entry = index / PV_NUM_DWORDS;
      offset = index % PV_NUM_DWORDS;
      r = p_pv_rm.pv_reg_rm.PCR_ENTRY[entry][offset];
      if (r.is_busy()) mirror_jobs.push_back(index);
      else begin
        if (!r.predict(pcr_word[entry][offset]))
          `uvm_fatal("PV_MIRROR", "Idle PCR mirror prediction failed")
        r.set(pcr_word[entry][offset]);
        word_dirty[entry][offset] = 0;
      end
    end
  endfunction

  function void publish_ahb_reads();
    ahb_read_snapshot_t snapshot;
    pv_sb_ahb_ap_output_transaction_t completed;
    while (ahb_read_snapshots.size() && completed_ahb_reads.size()) begin
      snapshot = ahb_read_snapshots.pop_front();
      completed = completed_ahb_reads.pop_front();
      if (PV_ADDR_W'(completed.address) !== snapshot.addr)
        `uvm_fatal("PV_AHB_ORDER", "AHB callback address differs from sampled request")
      completed.data[0] = ahb_lite_slave_0_params::AHB_RDATA_WIDTH'(snapshot.data) <<
        (8*((snapshot.addr & ~(PV_DATA_W/8-1)) %
            (ahb_lite_slave_0_params::AHB_RDATA_WIDTH/8)));
      pv_sb_ahb_ap.write(completed);
    end
  endfunction

  // The change-triggered write monitor reports a beat one clock late and does
  // not report every beat of a constant stream. Sample SHA and actual raw
  // CPU requests before NBA, not AHB completion callbacks. uc_req.wdata already
  // has the AHB lane selected by ahb_slv_sif. No RTL storage/output is sampled.
  virtual task run_phase(uvm_phase phase);
    pv_write_t write_req;
    pv_uc_req_t cpu_req;
    uvm_hdl_data_t pin_value;
    ahb_read_snapshot_t snapshot;
    bit [PV_NUM_PCR-1:0] clear_before;
    bit pwrgood_before, rst_before, core_before, window_before;
    bit cpu_dv, cpu_reg_dv, permitted, hard_reset_seen = 0;
    logic [PV_ENTRY_ADDR_W-1:0] read_entry;
    logic [PV_ENTRY_SIZE_WIDTH-1:0] read_offset;
    int entry, offset;
    super.run_phase(phase);
    fork
      begin
        forever begin
          @(negedge configuration.pv_rst_agent_config.monitor_bfm.cptra_pwrgood_i);
          // Storage resets asynchronously, before the next read-monitor callback.
          foreach (pcr_word[e, w]) update_word(e, w, 0);
        end
      end
    join_none
    forever begin
      @(posedge configuration.pv_sha512_write_agent_config.monitor_bfm.clk_i);
      write_req = pv_write_t'(configuration.pv_sha512_write_agent_config.monitor_bfm.pv_write_i);
      clear_before = clear_pending;
      pwrgood_before = configuration.pv_rst_agent_config.monitor_bfm.cptra_pwrgood_i;
      rst_before = configuration.pv_rst_agent_config.monitor_bfm.rst_b_i;
      core_before = configuration.pv_rst_agent_config.monitor_bfm.core_only_rst_b_i;
      window_before = configuration.pv_rst_agent_config.monitor_bfm.fw_update_rst_window_i;
      if (!uvm_hdl_read({pv_dut_path, ".uc_req_dv"}, pin_value))
        `uvm_fatal("PV_INPUT_PATH", "Cannot read PV request pins; build with -debug_access+all")
      cpu_dv = pin_value[0];
      cpu_reg_dv = 0;
      cpu_req = '0;
      if (cpu_dv) begin
        if (!uvm_hdl_read({pv_dut_path, ".uc_req"}, pin_value))
          `uvm_fatal("PV_INPUT_PATH", "Cannot read PV CPU request")
        cpu_req = pv_uc_req_t'(pin_value);
        cpu_reg_dv = (cpu_req.addr[PV_ADDR_W-1:pv_reg_pkg::PV_REG_ADDR_WIDTH] == 0);
      end
      // Freeze the pre-edge read result. Callback delivery can be before or
      // after this worker; queues preserve ordering without a tolerance window.
      if (cpu_dv && !cpu_req.write) begin
        snapshot.addr = cpu_req.addr;
        if (!cpu_reg_dv)
          snapshot.data = 0;
        else if (cpu_req.addr < PV_NUM_PCR*4 && cpu_req.addr[1:0] == 0)
          snapshot.data = ctrl_data_shadow[cpu_req.addr/4];
        else if (cpu_req.addr >= `PV_REG_PCR_ENTRY_0_0 &&
                 cpu_req.addr < `PV_REG_PCR_ENTRY_0_0 + PV_NUM_PCR*PV_NUM_DWORDS*4 &&
                 cpu_req.addr[1:0] == 0) begin
          {read_offset, read_entry} = convert_addr_to_pv(cpu_req.addr);
          snapshot.data = pcr_word[read_entry][read_offset];
        end
        else snapshot.data = 0; // Unmapped/unaligned read mux default in pv_reg.
        ahb_read_snapshots.push_back(snapshot);
        publish_ahb_reads();
      end
      uvm_wait_for_nba_region();
      if (!configuration.pv_rst_agent_config.monitor_bfm.cptra_pwrgood_i) begin
        if (!hard_reset_seen)
          foreach (pcr_word[e, w]) update_word(e, w, 0);
        hard_reset_seen = 1;
      end
      else if (pwrgood_before) begin
        hard_reset_seen = 0;
        if (rst_before) begin
          for (int e = 0; e < PV_NUM_PCR; e++) begin
            if (clear_before[e]) begin
              for (int w = 0; w < PV_NUM_DWORDS; w++) update_word(e, w, 0);
            end
          end
        end
        permitted = 1;
`ifdef CALIPTRA_MODE_SUBSYSTEM
        permitted = write_req.write_entry != PV_PCR_CUR &&
                    write_req.write_entry != PV_PCR_JRN;
`endif
        if (write_req.write_en && permitted &&
            write_req.write_entry < PV_NUM_PCR && write_req.write_offset < PV_NUM_DWORDS) begin
          update_word(write_req.write_entry, write_req.write_offset, write_req.write_data);
        end
        else if (write_req.write_en && !permitted &&
                 write_req.write_entry < PV_NUM_PCR && write_req.write_offset < PV_NUM_DWORDS) begin
          // A denied SHA frontdoor write can still auto-predict the RAL mirror.
          update_word(write_req.write_entry, write_req.write_offset,
                      pcr_word[write_req.write_entry][write_req.write_offset]);
        end
      end
      clear_pending = '0;
      if (cpu_dv && cpu_reg_dv && cpu_req.write && cpu_req.addr < PV_NUM_PCR*4 &&
          cpu_req.addr[1:0] == 0) begin
        entry = cpu_req.addr/4;
        if (rst_before) ctrl_data_shadow[entry][7:2] = cpu_req.wdata[7:2];
        // Both CSR fields see the OLD lock, even for a combined lock+clear.
        if (!ctrl_lock_shadow[entry] || window_before) begin
          if (rst_before) clear_pending[entry] = cpu_req.wdata[1];
          if (core_before) ctrl_lock_shadow[entry] = cpu_req.wdata[0];
        end
      end
      for (int entry = 0; entry < PV_NUM_PCR; entry++) begin
        // Main reset clears pulse/reserved fields; core reset clears only lock.
        if (!configuration.pv_rst_agent_config.monitor_bfm.rst_b_i) begin
          ctrl_data_shadow[entry][7:1] = 0;
          clear_pending[entry] = 0;
        end
        if (!configuration.pv_rst_agent_config.monitor_bfm.core_only_rst_b_i)
          ctrl_lock_shadow[entry] = 0;
        ctrl_data_shadow[entry][0] = ctrl_lock_shadow[entry];
        ctrl_data_shadow[entry][1] = clear_pending[entry];
        if (!p_pv_rm.pv_reg_rm.PCR_CTRL[entry].is_busy() &&
            p_pv_rm.pv_reg_rm.PCR_CTRL[entry].get_mirrored_value() !==
            uvm_reg_data_t'(ctrl_data_shadow[entry])) begin
          if (!p_pv_rm.pv_reg_rm.PCR_CTRL[entry].predict(ctrl_data_shadow[entry]))
            `uvm_fatal("PV_MIRROR", "Idle CTRL mirror prediction failed")
          p_pv_rm.pv_reg_rm.PCR_CTRL[entry].set(ctrl_data_shadow[entry]);
        end
      end
      flush_word_mirrors();
      publish_ahb_reads();
    end
  endtask

  virtual function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    if (ahb_read_snapshots.size() || completed_ahb_reads.size() || mirror_jobs.size())
      `uvm_error("PV_PENDING", "Unconsumed AHB read snapshots/callbacks or PCR mirror jobs")
  endfunction

  extern function void populate_expected_pv_read_txn(ref pv_sha512_block_read_sb_ap_output_transaction_t t_expected, pv_read_transaction t_received);
  extern function void populate_expected_pv_write_txn(ref pv_sha512_write_sb_ap_output_transaction_t t_expected, pv_write_transaction t_received);

  // pragma uvmf custom class_item_additional end

  // FUNCTION: new
  function new(string name, uvm_component parent);
     super.new(name,parent);
  // pragma uvmf custom new begin
    foreach (ctrl_data_shadow[entry]) ctrl_data_shadow[entry] = 0;
    foreach (pcr_word[entry, offset]) pcr_word[entry][offset] = 0;
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
    void'(uvm_config_db#(string)::get(null, configuration.get_full_name(),
                                    "pv_dut_path", pv_dut_path));

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

    // Delayed reset notifications remain checked, but only actual reset pins in
    // run_phase change storage/CSR state; callbacks must not rewind later beats.
    
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

    ahb_slave_0_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through ahb_slave_0_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    pv_sb_ahb_ap_output_transaction = pv_sb_ahb_ap_output_transaction_t::type_id::create("pv_sb_ahb_ap_output_transaction");
    $cast(ahb_txn, t);

    pv_sb_ahb_ap_output_transaction.copy(ahb_txn);
    if (ahb_txn.RnW == AHB_READ) begin
      completed_ahb_reads.push_back(pv_sb_ahb_ap_output_transaction);
      publish_ahb_reads();
    end
    else
      pv_sb_ahb_ap.write(pv_sb_ahb_ap_output_transaction);
    // Code for sending output transaction out through pv_sha512_write_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    // pragma uvmf custom ahb_slave_0_ae_predictor end
  endfunction


endclass 

// pragma uvmf custom external begin
  function void pv_predictor::populate_expected_pv_read_txn (ref pv_sha512_block_read_sb_ap_output_transaction_t t_expected, pv_read_transaction t_received);

    uvm_reg pv_reg;
    uvm_reg_data_t pv_reg_data;


    pv_reg = p_pv_rm.get_reg_by_name($sformatf("PCR_ENTRY[%0d][%0d]",t_received.read_entry,t_received.read_offset));
    pv_reg_data = pcr_word[t_received.read_entry][t_received.read_offset];

    t_expected.read_data = pv_reg_data[31:0];
    t_expected.error = 'b0; //Currently no error logic in PCR
    t_expected.last = t_received.last; //TODO fix last flag logic
    t_expected.read_entry = t_received.read_entry;
    t_expected.read_offset = t_received.read_offset;

  endfunction

  function void pv_predictor::populate_expected_pv_write_txn (ref pv_sha512_write_sb_ap_output_transaction_t t_expected, pv_write_transaction t_received);
    
    t_expected.copy(t_received);
    t_expected.error = 'b0; //Currently no error logic in PCR
    // Storage is committed by run_phase at the actual request edge, not by
    // this delayed response packet. error=0 also applies to SS SHA PCR4/5 DROP.

  endfunction
// pragma uvmf custom external end
