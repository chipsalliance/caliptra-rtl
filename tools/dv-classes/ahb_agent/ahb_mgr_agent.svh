// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ahb_mgr_agent extends uvm_agent;
  `uvm_component_utils(ahb_mgr_agent)

  typedef uvm_sequencer #(ahb_reg_op_item) layered_reg_sequencer_t;

  // Analysis ports for requests, responses and complete transactions
  uvm_analysis_port #(ahb_txn_request_item)  m_request_port;
  uvm_analysis_port #(ahb_txn_response_item) m_response_port;
  uvm_analysis_port #(ahb_txn_item)          m_transaction_port;

  // The virtual interface. This can either be set by calling set_vif() before the build phase, or
  // provided through uvm_config_db.
  local virtual ahb_if m_vif;

  // The monitor for the interface
  local ahb_monitor m_monitor;

  // The driver that can send read and write transactions
  local ahb_mgr_driver m_driver;

  // A sequencer that supplies m_driver
  local ahb_txn_sequencer_t m_sequencer;

  // A reg adapter. This is stateless, so gets created in build_phase whenever the agent is active.
  local ahb_mgr_reg_adapter m_reg_adapter;

  // A sequencer that can control access to an instance of ahb_mgr_register_layer_vseq (if there is
  // one)
  local layered_reg_sequencer_t m_layered_reg_sequencer;

  // A flag that shows there is an instance of ahb_mgr_register_layer_vseq running (started by
  // run_layered_register_vseq)
  local bit m_layer_vseq_running;

  // An array of known mappings from address range to subordinate index. Add entries with the
  // add_subordinate_mapping function.
  local sub_addr_range_t m_subordinate_ranges[$];

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);

  // Set m_vif to the provided interface
  extern function void set_vif(virtual ahb_if vif);

  // Get the sequencer. Can only be called after build_phase, and the agent must be active.
  extern function ahb_txn_sequencer_t get_sequencer();

  // Get the reg adapter. Can only be called after build_phase, and the agent must be active.
  extern function ahb_mgr_reg_adapter get_reg_adapter();

  // Add a mapping to m_subordinate_ranges that is covers all the items accessible through reg_map.
  // The single range that is added includes all the accessible addresses (so this won't work well
  // if there are gaps)
  //
  // This can be called multiple times before starting the layered register vseq (which will use the
  // information) but cannot be used after that point.
  extern function void register_subordinate_for_map(uvm_reg_map  reg_map,
                                                    int unsigned subordinate_idx);

  // Run the layered register vseq, which shouldn't already be running.
  //
  // This sequence will run forever and its layering sequencer can be retrieved with
  // get_register_layering_sequencer(). If the sequence is already running for some reason, this
  // generates a uvm_error and hangs.
  extern task run_layered_register_vseq();

  // Get a handle to the sequencer that can be used to access a layered register vseq if it is
  // started.
  //
  // Can only be called after build_phase, and the agent must be active.
  extern function layered_reg_sequencer_t get_register_layering_sequencer();
endclass

function ahb_mgr_agent::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void ahb_mgr_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);

  m_request_port = new("m_request_port", this);
  m_response_port = new("m_response_port", this);
  m_transaction_port = new("m_transaction_port", this);

  if (m_vif == null && !uvm_config_db#(virtual ahb_if)::get(this, "", "vif", m_vif)) begin
    `uvm_fatal(get_full_name(), "failed to get vif from uvm_config_db")
  end
  if (m_vif == null) begin
    `uvm_fatal(get_full_name(), "No non-null m_vif provided.")
  end

  m_monitor = ahb_monitor::type_id::create("m_monitor", this);
  m_monitor.set_vif(m_vif);

  if (get_is_active() == UVM_ACTIVE) begin
    // Generate a driver, sequencer and reg adapter
    m_driver = ahb_mgr_driver::type_id::create("m_driver", this);
    m_sequencer = ahb_txn_sequencer_t::type_id::create("m_sequencer", this);
    m_reg_adapter = ahb_mgr_reg_adapter::type_id::create("m_reg_adapter");
    m_layered_reg_sequencer = layered_reg_sequencer_t::type_id::create("m_layered_reg_sequencer",
                                                                       this);
  end
endfunction

function void ahb_mgr_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);

  m_monitor.m_request_port.connect(m_request_port);
  m_monitor.m_response_port.connect(m_response_port);
  m_monitor.m_transaction_port.connect(m_transaction_port);

  // If the agent is active, connect drivers to interfaces and sequencers
  if (get_is_active() == UVM_ACTIVE) begin
    m_driver.set_vif(m_vif);
    m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
  end
endfunction

function void ahb_mgr_agent::set_vif(virtual ahb_if vif);
  if (m_vif != null) `uvm_fatal(get_full_name(), "Cannot set vif: m_vif is already non-null.")
  m_vif = vif;
endfunction

function ahb_txn_sequencer_t ahb_mgr_agent::get_sequencer();
  if (m_sequencer == null) `uvm_fatal(get_full_name(), "m_sequencer is null.")
  return m_sequencer;
endfunction

function ahb_mgr_reg_adapter ahb_mgr_agent::get_reg_adapter();
  if (m_reg_adapter == null) `uvm_fatal(get_full_name(), "m_reg_adapter is null.")
  return m_reg_adapter;
endfunction

function void ahb_mgr_agent::register_subordinate_for_map(uvm_reg_map   reg_map,
                                                          int unsigned  subordinate_idx);
  uvm_reg        regs[$];
  uvm_reg_addr_t addr_min = '1, addr_max = 0;

  if (m_layer_vseq_running) begin
    `uvm_error(get_full_name(),
               {"Adding a subordinate mapping will have no effect: ",
                "the layered vseq is already running."})
  end

  // Update addr_min, addr_max so that the range addr_min..addr_max contains every register
  // accessible through reg_map.
  reg_map.get_registers(regs);
  foreach (regs[i]) begin
    uvm_reg_addr_t addr = regs[i].get_address(reg_map);
    if (addr < addr_min) addr_min = addr;
    if (addr_max < addr) addr_max = addr;
  end

  if (addr_min <= addr_max) begin
    sub_addr_range_t rng;

    rng.addr_min = addr_min;
    rng.addr_max = addr_max;
    rng.subordinate_idx = subordinate_idx;
    m_subordinate_ranges.push_front(rng);
  end
endfunction

task ahb_mgr_agent::run_layered_register_vseq();
  ahb_mgr_register_layer_vseq layer_vseq;

  if (m_layer_vseq_running) begin
    `uvm_error(get_full_name(), "Layered vseq already running.")
    wait(0);
  end
  m_layer_vseq_running = 1;

  layer_vseq = ahb_mgr_register_layer_vseq::type_id::create("layer_vseq");

  layer_vseq.set_sequencers(m_layered_reg_sequencer, m_sequencer);
  layer_vseq.set_subordinates(m_subordinate_ranges);

  layer_vseq.start(null);

  // Because layer_vseq never completes, we don't expect to get here.
  `uvm_fatal(get_full_name(), "Instance of ahb_mgr_register_layer_vseq ran to completion.")
endtask

function ahb_mgr_agent::layered_reg_sequencer_t ahb_mgr_agent::get_register_layering_sequencer();
  if (m_layered_reg_sequencer == null)
    `uvm_fatal(get_full_name(), "m_layered_reg_sequencer is null.")

  return m_layered_reg_sequencer;
endfunction
