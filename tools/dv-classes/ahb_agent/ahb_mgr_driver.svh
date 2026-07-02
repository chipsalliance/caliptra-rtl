// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A driver for ahb_write_request_if, used when the testbench is acting as an AHB Manager that is
// requesting transactions.
//
// The driver sends a response to every item, sending an ahb_status_item (with m_sending_complete=0)
// if the transfer was interrupted by a reset and sending an ahb_txn_response_item with the bus
// response otherwise.

class ahb_mgr_driver extends uvm_driver#(ahb_txn_request_item, uvm_sequence_item);
  `uvm_component_utils(ahb_mgr_driver)

  local virtual ahb_if m_vif;

  // True if the interface is currently in reset. Maintained by monitor_reset().
  //
  // At the very start of the simulation, rst_ni might be 'x or 'z. This isn't considered a "proper"
  // reset: in_reset can only be asserted by seeing rst_ni === 0 (and then cleared by seeing it
  // become 1).
  local bit m_in_reset;

  // If not null, cur_addr_phase is an item whose address phase was driven on the last clock edge.
  local ahb_txn_request_item m_cur_addr_phase;

  // If not null, cur_data_phase is an item whose data phase was driven on the last clock edge.
  local ahb_txn_request_item m_cur_data_phase;

  extern function new(string name, uvm_component parent);
  extern virtual task run_phase(uvm_phase phase);

  // Set m_vif. This must be called before run_phase.
  extern function void set_vif(virtual ahb_if vif);

  // Run forever, consuming and driving items from seq_item_port
  extern local task get_and_drive();

  // Run forever, tracking rst_ni and maintaining an in_reset class variable. Calls clear_data when
  // reset becomes asserted.
  extern local task monitor_reset();

  // Wait for one clock edge in host_cb, but stop early on a reset
  extern local task wait_cb_or_reset();

  // Handle interface updates on a clock edge
  //
  // If not null, next_item is an item whose address phase might be driven on the next clock edge
  // (assuming there was not back-presure exerted on the last cycle).
  //
  // The took_next_item output argument is asserted if the next_item argument has been taken as
  // m_cur_addr_phase.
  //
  // This task will consume no simulated time (but needs to be a task because it calls set_hsel,
  // set_address_phase_signals and set_data_phase_signals which, in turn, must be tasks because they
  // set clocking block drives.
  extern local task at_clock_edge(ahb_txn_request_item next_item, output bit took_next_item);

  // Set the HSEL signal to match the set of items in m_cur_addr_phase and m_cur_data_phase.
  extern local task set_hsel();

  // Set the signals for the address phase for m_cur_addr_phase. If that is null, there is no
  // address phase to send on this cycle (and the signals should be cleared).
  //
  // This task runs in zero time, but uses clocking block drives so cannot be a function.
  //
  // The task also checks any address against the ADDR_WIDTH property configured in the interface.
  extern local task set_address_phase_signals();

  // Set the signals for the data phase for m_cur_data_phase. If item is null, there is no data
  // phase to send on this cycle (and the signals should be cleared).
  //
  // This task runs in zero time, but uses clocking block drives so cannot be a function.
  //
  // The task also checks data and strb fields against the DATA_WIDTH property configured in the
  // interface.
  extern local task set_data_phase_signals();

  // A task that is called at the start of a reset and also at the end of driving an item.
  extern local task clear_data();

  // Send a status item response to the given request item
  //
  // Because this driver only sends ahb_status_item items when a transaction has been aborted, this
  // function knows enough to create the item as well.
  extern local function void send_status_item_rsp(ahb_txn_request_item req_item);

  // Send a status item response (using send_status_item_rsp) for any of m_cur_data_phase,
  // m_cur_addr_phase and next_item that is ot null, then clear both class variables to null.
  extern local function void send_status_item_rsp_triple(ahb_txn_request_item next_item);

  // Create and send an ahb_txn_response_item based on the signals on the interface if there is an
  // item currently running its data phase (and thus m_cur_data_phase is not null).
  //
  // If there was an item that got a response, this also clears m_cur_data_phase.
  extern local function void read_and_send_response();
endclass

function ahb_mgr_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void ahb_mgr_driver::set_vif(virtual ahb_if vif);
  if (m_vif != null) begin
    `uvm_fatal(get_full_name(), "Cannot call set_vif: there is already an interface.")
    return;
  end
  m_vif = vif;
endfunction

task ahb_mgr_driver::run_phase(uvm_phase phase);
  if (m_vif == null) begin
    `uvm_fatal(get_full_name(), "Cannot drive interface: vif is null.")
    return;
  end

  if (m_vif.if_mode != dv_utils_pkg::Host) begin
    `uvm_warning(get_full_name(),
                 $sformatf("Driving interface will have no effect: if_mode is %0s",
                           m_vif.if_mode.name()))
  end

  // Start by clearing the data (and, importantly, setting m_vif.host_cb.hsel = '0). From now, hsel
  // will be zero unless $isunknown on all the other fields is false.
  clear_data();

  fork
    get_and_drive();
    monitor_reset();
  join
endtask

task ahb_mgr_driver::at_clock_edge(ahb_txn_request_item next_item,
                                   output bit           took_next_item);
  bit paused;

  if (m_cur_data_phase != null) begin
    // If cur_data_phase is not null, that item was being driven on the last clock edge. Was it
    // accepted by the subordinate?
    if (!m_vif.host_cb.hready) begin
      // Because the subordinate was not ready, the item wasn't accepted by the subordinate and no
      // transaction happened.
      paused = 1;
    end else begin
      // Because the subordinate *was* ready, the item was accepted. Call read_and_send_response,
      // which will read a response to the non-null m_cur_data_phase item, then clear that variable.
      read_and_send_response();
    end
  end

  // If paused is true, nothing happened. Leave the signals driven as before and return, setting
  // took_next_item=0 to tell the caller that it wasn't taken.
  if (paused) begin
    took_next_item = 0;
    return;
  end

  // At this point m_cur_data_phase is null. Move m_cur_addr_phase into m_cur_data_phase.
  m_cur_data_phase = m_cur_addr_phase;
  m_cur_addr_phase = null;

  // Can we drive the addr phase of next_item? We can only do so if next_item is not null and either
  // m_cur_data_phase is null or has it the same m_subordinate_idx as next_item. If so, set
  // m_cur_addr_phase to be next_item and set took_next_item = 1. If not, set took_next_item=0.
  if (next_item != null &&
      (m_cur_data_phase == null ||
       m_cur_data_phase.m_subordinate_idx == next_item.m_subordinate_idx)) begin
    m_cur_addr_phase = next_item;
    took_next_item = 1;
  end else begin
    took_next_item = 0;
  end

  // Set hsel to match any items that are currently being driven (which will have the same
  // m_subordinate_idx) and drive the address and data signals for the next clock edge
  set_hsel();
  set_address_phase_signals();
  set_data_phase_signals();
endtask


task ahb_mgr_driver::get_and_drive();
  ahb_txn_request_item next_item;

  forever begin
    // This flag is set by at_clock_edge if it consumed the item that was passed in its next_item
    // argument (which will now be in m_cur_addr_phase). If that happens, we should clear next_item
    // here.
    bit took_next_item;

    // This infinite loop always runs from one clock edge to the next, stopping an iteration early
    // on a reset.
    //
    // At the start of the loop, we are at a clock edge, where we have just set the
    // address/data signals for either of m_cur_addr_phase and m_cur_data_phase that is not null.
    //
    // Wait until the next clock edge, stopping early if a reset is asserted.
    wait_cb_or_reset();

    // If we are in reset, call send_status_item_rsp_triple to send an empty response for any item
    // that is currently non-nil and clear it. Then wait until there is something available in
    // seq_item_port. Consume it and put it in next_item, then go around the loop again.
    if (m_in_reset) begin
      send_status_item_rsp_triple(next_item);
      seq_item_port.get(next_item);
      continue;
    end

    // At this point, we are at a clock edge. If one or both m_cur_addr_phase or m_cur_data_phase
    // are non-null, they are items whose address or data phase signals were asserted on the last
    // clock edge.
    //
    // If next_item is null, peek at the sequencer to see whether there is an item available to have
    // its address phase driven from this clock edge.
    if (next_item == null) begin
      if (seq_item_port.has_do_available()) begin
        seq_item_port.get(next_item);
      end
    end

    // If next_item is null and m_cur_addr_phase and m_cur_data_phase are also null, we have no
    // items at the moment. Wait until there is something in seq_item_port and then jump back to the
    // start of the loop to align to the next clock edge.
    if (next_item == null && m_cur_addr_phase == null && m_cur_data_phase == null) begin
      seq_item_port.wait_for_sequences();
      continue;
    end

    at_clock_edge(next_item, took_next_item);

    if (took_next_item) begin
      // If took_next_item is true then next_item will have just been copied to m_cur_addr_phase.
      // Clear the next_item variable.
      next_item = null;
    end
  end
endtask

task ahb_mgr_driver::monitor_reset();
  wait(!$isunknown(m_vif.rst_ni));
  m_in_reset = !m_vif.rst_ni;
  forever begin
    wait (m_vif.rst_ni);
    m_in_reset = 0;
    wait (!m_vif.rst_ni);
    m_in_reset = 1;
    clear_data();
  end    
endtask

task ahb_mgr_driver::wait_cb_or_reset();
  fork : isolation_fork begin
    fork
      @(m_vif.host_cb);
      wait(m_in_reset);
    join_any
    disable fork;
  end join
endtask

task ahb_mgr_driver::set_hsel();
  bit [7:0] hsel;

  // If there is an item to send in the address phase, check that m_subordinate_idx less than the
  // num_subordinates value from the interface and then set hsel to match.
  if (m_cur_addr_phase != null) begin
    if (m_cur_addr_phase.m_subordinate_idx >= m_vif.num_subordinates) begin
      `uvm_error(get_full_name(),
                 $sformatf({"Cannot set hsel for m_subordinate_idx = %0d: ",
                            "there are only %0d subordinates."},
                           m_cur_addr_phase.m_subordinate_idx, m_vif.num_subordinates))
    end
    hsel = (8'd1 << m_cur_addr_phase.m_subordinate_idx);
  end

  // If there is an item to send in the data phase, check that it matches any existing non-zero
  // hsel. (If it doesn't this will be a bug in the logic of at_clock_edge, but it probably makes
  // sense to check here too). Set hsel to match the item.
  if (m_cur_data_phase != null) begin
    bit [7:0] data_hsel = (8'd1 << m_cur_data_phase.m_subordinate_idx);
    if (|hsel && hsel != data_hsel) begin
      `uvm_error(get_full_name(),
                 $sformatf({"hsel mismatch. addr phase item gave hsel = 0x%0h but data ",
                            "phase item gave hsel = 0x%0h."},
                           hsel, data_hsel))
    end
    hsel = data_hsel;
  end

  // At this point, hsel will be onehot0. Set the signal in the interface to match.
  m_vif.host_cb.hsel <= hsel;
endtask

task ahb_mgr_driver::set_address_phase_signals();
  if (m_cur_addr_phase == null) begin
    m_vif.host_cb.haddr     <= 'x;
    m_vif.host_cb.hburst    <= 'x;
    m_vif.host_cb.hmastlock <= 'x;
    m_vif.host_cb.hprot     <= 'x;
    m_vif.host_cb.hsize     <= 'x;
    m_vif.host_cb.htrans    <= TransIdle;
    m_vif.host_cb.hwrite    <= 'x;
  end else begin
    if (|(m_cur_addr_phase.m_addr >> m_vif.addr_width)) begin
      `uvm_error(get_full_name(),
                 $sformatf("Cannot represent m_addr = 0x%0h. The interface ADDR_WIDTH is %0d.",
                           m_cur_addr_phase.m_addr, m_vif.addr_width))
    end

    m_vif.host_cb.haddr     <= m_cur_addr_phase.m_addr;
    m_vif.host_cb.hburst    <= m_cur_addr_phase.m_burst;
    m_vif.host_cb.hmastlock <= m_cur_addr_phase.m_lock;
    m_vif.host_cb.hprot     <= m_cur_addr_phase.m_prot;
    m_vif.host_cb.hsize     <= m_cur_addr_phase.m_size;
    m_vif.host_cb.htrans    <= m_cur_addr_phase.m_trans;
    m_vif.host_cb.hwrite    <= m_cur_addr_phase.m_write;
  end
endtask

task ahb_mgr_driver::set_data_phase_signals();
  if (m_cur_data_phase == null) begin
    m_vif.host_cb.hwstrb <= 'x;
    m_vif.host_cb.hwdata <= 'x;
  end else begin
    if (m_cur_data_phase.m_write) begin
      if (|(m_cur_data_phase.m_wdata >> m_vif.data_width)) begin
        `uvm_error(get_full_name(),
                   $sformatf("Cannot represent m_wdata = 0x%0h. The interface DATA_WIDTH is %0d.",
                             m_cur_data_phase.m_wdata, m_vif.data_width))
      end

      if (|(m_cur_data_phase.m_wstrb >> ((m_vif.data_width + 7) / 8))) begin
        `uvm_error(get_full_name(),
                   $sformatf({"Cannot represent m_wstrb = 0x%0h. ",
                              "The interface DATA_WIDTH is %0d, giving %0d strobe bits."},
                             m_cur_data_phase.m_wstrb, m_vif.data_width,
                             (m_vif.data_width + 7) / 8))
      end

      // If the interface has no HWSTRB signal, we want to generate an error if there is a
      // complicated m_wstrb value. We don't want to require the value be constant though, because
      // some code on the sequence side is easier to write if it calculates it from m_size. Check
      // that the portion of wstrb corresponding to the bytes from m_size is constant.
      if (!m_vif.has_write_strobes) begin
        bit [127:0] strb_mask_from_size = (1 << (1 << m_cur_data_phase.m_size)) - 1;
        if (m_cur_data_phase.m_wstrb != '0 &&
            m_cur_data_phase.m_wstrb != strb_mask_from_size) begin
          `uvm_error(get_full_name(),
                     $sformatf({"Cannot represent m_wstrb = 0x%0h on this interface. ",
                                "Because Write_Strobes is false, there is no hwstrb signal and ",
                                "m_size for this item gives a relevant 'true' strobe mask of ",
                                "0x%0h. m_wstrb is neither than nor zero."},
                               m_cur_data_phase.m_wstrb,
                               strb_mask_from_size))
        end
      end
    end

    m_vif.host_cb.hwstrb <= m_cur_data_phase.m_wstrb;
    m_vif.host_cb.hwdata <= m_cur_data_phase.m_wdata;
  end
endtask

task ahb_mgr_driver::clear_data();
  m_vif.host_cb.hsel      <= '0;
  m_vif.host_cb.haddr     <= 'x;
  m_vif.host_cb.hburst    <= 'x;
  m_vif.host_cb.hmastlock <= 'x;
  m_vif.host_cb.hprot     <= 'x;
  m_vif.host_cb.hsize     <= 'x;
  m_vif.host_cb.htrans    <= 'x;
  m_vif.host_cb.hwdata    <= 'x;
  m_vif.host_cb.hwstrb    <= 'x;
  m_vif.host_cb.hwrite    <= 'x;
endtask

function void ahb_mgr_driver::send_status_item_rsp(ahb_txn_request_item req_item);
  ahb_status_item status_rsp = ahb_status_item::type_id::create("status_rsp");

  status_rsp.set_id_info(req_item);
  status_rsp.m_sending_complete = 0;

  seq_item_port.put_response(status_rsp);
endfunction

function void ahb_mgr_driver::send_status_item_rsp_triple(ahb_txn_request_item next_item);
  if (m_cur_data_phase != null) begin
    send_status_item_rsp(m_cur_data_phase);
    m_cur_data_phase = null;
  end

  if (m_cur_addr_phase != null) begin
    send_status_item_rsp(m_cur_addr_phase);
    m_cur_addr_phase = null;
  end

  if (next_item != null) begin
    send_status_item_rsp(next_item);
  end
endfunction

function void ahb_mgr_driver::read_and_send_response();
  ahb_txn_response_item rsp_item;

  if (m_cur_data_phase == null) return;

  rsp_item = ahb_txn_response_item::type_id::create("rsp_item");
  rsp_item.set_id_info(m_cur_data_phase);

  rsp_item.m_rdata = m_vif.host_cb.hrdata_muxed;
  rsp_item.m_resp  = m_vif.host_cb.hresp_muxed;

  seq_item_port.put_response(rsp_item);

  m_cur_data_phase = null;
endfunction
