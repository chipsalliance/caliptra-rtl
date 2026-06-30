// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A monitor that watches an AHB interface

class ahb_monitor extends uvm_monitor;
  `uvm_component_utils(ahb_monitor)

  // The interface being tracked. Set this with set_vif().
  local virtual ahb_if m_vif;

  // This event gets triggered when the monitor sees a reset. Structuring it like this (instead of
  // waiting on m_vif.rst_ni in watch_until_reset) simulates dramatically more quickly.
  local uvm_event saw_reset;

  // The analysis ports for requests, responses and complete transactions.
  uvm_analysis_port #(ahb_txn_request_item)  m_request_port;
  uvm_analysis_port #(ahb_txn_response_item) m_response_port;
  uvm_analysis_port #(ahb_txn_item)          m_transaction_port;

  extern function new(string name, uvm_component parent);
  extern function void build_phase (uvm_phase phase);
  extern task run_phase(uvm_phase phase);

  // Set the interface that is being tracked
  extern function void set_vif(virtual ahb_if vif);

  // Track requests and responses on m_vif
  extern local task watch_interface();

  // Track requests and responses on m_vif, leaving early if reset is asserted
  extern local task watch_until_reset();
endclass

function ahb_monitor::new(string name, uvm_component parent);
  super.new(name, parent);
  saw_reset = new("saw_reset");
endfunction

function void ahb_monitor::build_phase(uvm_phase phase);
  super.build_phase(phase);

  m_request_port = new("m_request_port", this);
  m_response_port = new("m_response_port", this);
  m_transaction_port = new("m_transaction_port", this);

  if (m_vif == null && !uvm_config_db#(virtual ahb_if)::get(this, "", "vif", m_vif)) begin
    `uvm_fatal(get_full_name(), "Interface neither supplied with set_vif nor with uvm_config_db.")
  end
endfunction

task ahb_monitor::run_phase(uvm_phase phase);
  fork
    super.run_phase(phase);
    watch_interface();
    forever begin
      wait(m_vif.rst_ni === 1'b1);
      wait(m_vif.rst_ni !== 1'b1);
      saw_reset.trigger();
    end
  join
endtask

function void ahb_monitor::set_vif(virtual ahb_if vif);
  m_vif = vif;
endfunction

task ahb_monitor::watch_interface();
  forever begin
    wait(m_vif.rst_ni === 1'b1);
    watch_until_reset();

    // Check that there really has been a reset (to ensure the loop iterations take a positive
    // amount of time)
    if (m_vif.rst_ni === 1'b1) `uvm_fatal(get_full_name(), "watch_until_reset exited early")
  end
endtask

task ahb_monitor::watch_until_reset();
  // A non-Idle request that has been seen. This is generated when we see a request being sent
  // (because there is no back pressure from the response side).
  ahb_txn_request_item req_item;

  forever begin
    // Wait until the observed region of a time slot where there is a positive clock edge, or drop
    // out early if there is a reset asserted.
    fork begin : isolation_fork
      fork
        @(m_vif.mon_cb);
        saw_reset.wait_ptrigger();
      join_any
      disable fork;
    end join

    if (m_vif.rst_ni !== 1'b1) begin
      // If req_item is not null, there was a transaction in flight that didn't get a response. Send
      // the partial transaction.
      if (req_item != null) begin
        ahb_txn_item txn_item = ahb_txn_item::type_id::create("txn_item");
        txn_item.m_request = req_item;
        m_transaction_port.write(txn_item);
      end
      return;
    end

    // Has a request been sent? If so, the subordinate has the opportunity to generate a response.
    if (req_item != null) begin
      ahb_txn_response_item rsp_item;
      ahb_txn_item          txn_item;

      // Infer an appropriate hwstrb value to use for the item if m_vif.has_write_strobes is false.
      int unsigned addr_mod_data_width  = req_item.m_addr % (m_vif.data_width / 8);
      bit [127:0]  wstrb_from_size0     = (1 << (1 << req_item.m_size)) - 1;
      bit [127:0]  wstrb_from_size_addr = wstrb_from_size0 << addr_mod_data_width;

      int unsigned selected_idx;

      // It should be possible to find the selected subordinate by looking at hsel. That signal must
      // be one-hot (to allow the multiplexor to select responses).
      if (!$onehot(m_vif.mon_cb.hsel)) begin
        `uvm_error(get_full_name(),
                   $sformatf("hsel signal after a request is not one-hot (hsel = 0x%0h)",
                             m_vif.mon_cb.hsel))
        continue;
      end

      selected_idx = $clog2(m_vif.mon_cb.hsel);

      // If the appropriate hreadyout signal is low, the subordinate is applying back pressure and
      // there is no transfer on this cycle. Go round the loop again.
      if (m_vif.mon_cb.hreadyout[selected_idx] !== 1'b1) continue;

      // If the transfer is a write, the data phase will have write data from the manager. Add this
      // to req_item.
      //
      // The wstrb value might not actually be reflected on the bus if m_vif.has_write_strobes is
      // false. In that case, infer a write strobe from hsize.
      req_item.m_wdata = m_vif.mon_cb.hwdata >> (8 * addr_mod_data_width);
      req_item.m_wstrb = (m_vif.has_write_strobes ?
                          (m_vif.mon_cb.hwstrb >> addr_mod_data_width) :
                          wstrb_from_size_addr);

      // Make a response item, then pair it up with the request, sending the response and the pair
      // on their respective analysis ports.
      rsp_item = ahb_txn_response_item::type_id::create("rsp_item");
      rsp_item.m_rdata = m_vif.mon_cb.hrdata[selected_idx] >> (8 * addr_mod_data_width);
      rsp_item.m_resp  = m_vif.mon_cb.hresp[selected_idx];
      m_response_port.write(rsp_item);

      txn_item = ahb_txn_item::type_id::create("txn_item");
      txn_item.m_request = req_item;
      txn_item.m_response = rsp_item;
      m_transaction_port.write(txn_item);

      req_item = null;
    end

    // If we get here then there was either no pending request or there was a request that has had a
    // response. If the manager is asserting a NONSEQ or SEQ request for some subordinate now,
    // create an item to represent it.
    if (|m_vif.mon_cb.hsel &&
        m_vif.mon_cb.htrans inside {TransNonSequential, TransSequential}) begin
      if (!$onehot(m_vif.mon_cb.hsel)) begin
        `uvm_error(get_full_name(),
                   $sformatf("hsel signal for a request is not one-hot (hsel = 0x%0h)",
                             m_vif.mon_cb.hsel))
        continue;
      end

      req_item = ahb_txn_request_item::type_id::create("req_item");

      req_item.m_subordinate_idx = $clog2(m_vif.mon_cb.hsel);
      req_item.m_addr = m_vif.mon_cb.haddr;
      req_item.m_burst = burst_e'(m_vif.mon_cb.hburst);
      req_item.m_lock = m_vif.mon_cb.hmastlock;
      req_item.m_prot = m_vif.mon_cb.hprot;
      req_item.m_size = m_vif.mon_cb.hsize;
      req_item.m_trans = trans_e'(m_vif.mon_cb.htrans);
      req_item.m_write = m_vif.mon_cb.hwrite;
      m_request_port.write(req_item);
    end
  end
endtask
