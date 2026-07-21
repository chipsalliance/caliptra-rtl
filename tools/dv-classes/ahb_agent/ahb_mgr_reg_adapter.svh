// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An extremely simple uvm_reg_adapter that wraps a uvm_reg_op in an ahb_reg_op_item or copies the
// response fields back from that item.

class ahb_mgr_reg_adapter extends uvm_reg_adapter;
  `uvm_object_utils(ahb_mgr_reg_adapter)

  extern function new(string name="");
  extern function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
  extern function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);

  // The bus2reg function, specialised for ahb_reg_op_item items. This is used by the reg_map when
  // making sense of responses from the layering virtual sequence.
  extern local function void bus2reg_reg_op(ahb_reg_op_item bus_item, ref uvm_reg_bus_op rw);

  // The bus2reg function, specialised for ahb_txn_item items. This is used by a uvm_reg_predictor
  // when making sense of bus transactions from the monitor.
  extern local function void bus2reg_txn(ahb_txn_item bus_item, ref uvm_reg_bus_op rw);
endclass

function ahb_mgr_reg_adapter::new(string name="");
  super.new(name);
  supports_byte_enable = 1;

  // Setting this to true means that the "bus driver" (here, ahb_mgr_register_layer_vseq) sends a
  // response to the sequencer.
  provides_responses   = 1;
endfunction

function uvm_sequence_item ahb_mgr_reg_adapter::reg2bus(const ref uvm_reg_bus_op rw);
  ahb_reg_op_item bus_item = ahb_reg_op_item::type_id::create("bus_item");

  // Take a copy of the uvm_reg_bus_op (which will be a deep copy because uvm_reg_bus_op is a
  // struct)
  bus_item.m_rw = rw;

  return bus_item;
endfunction

function void ahb_mgr_reg_adapter::bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
  ahb_reg_op_item reg_op_bus_item;
  ahb_txn_item    txn_item;

  if ($cast(reg_op_bus_item, bus_item)) begin
    bus2reg_reg_op(reg_op_bus_item, rw);
  end else if ($cast(txn_item, bus_item)) begin
    bus2reg_txn(txn_item, rw);
  end else begin
    `uvm_fatal(get_name(), "Cannot convert bus item to an ahb_reg_op_item or ahb_txn_item.")
  end
endfunction

function void ahb_mgr_reg_adapter::bus2reg_reg_op(ahb_reg_op_item bus_item, ref uvm_reg_bus_op rw);
  // Replace all the fields in rw that bus2reg would normally populate (kind, addr, data and status)
  rw.kind = bus_item.m_rw.kind;
  rw.addr = bus_item.m_rw.addr;
  rw.data = bus_item.m_rw.data;
  rw.status = bus_item.m_rw.status;
endfunction

function void ahb_mgr_reg_adapter::bus2reg_txn(ahb_txn_item bus_item, ref uvm_reg_bus_op rw);
  // We only need to understand read vs. write, but it probably makes sense to do this extra sanity
  // check: the ahb_monitor shouldn't have created an ahb_txn_item if the manager sent HTRANS that
  // was TransIdle or TransBusy.
  if (! (bus_item.m_request.m_trans inside {TransNonSequential, TransSequential})) begin
    `uvm_error("bus2reg_txn",
               $sformatf({"Unexpected m_trans for bus item: ",
                          "%0d is not TransNonSequential or TransSequential."},
                         bus_item.m_request.m_trans))
  end

  rw.kind   = bus_item.m_request.m_write ? UVM_WRITE : UVM_READ;
  rw.addr   = bus_item.m_request.m_addr;
  rw.n_bits = (8 << bus_item.m_request.m_size);

  if (bus_item.m_request.m_write) begin
    rw.byte_en = bus_item.m_request.m_wstrb;
    rw.data    = bus_item.m_request.m_wdata;
  end else begin
    // AHB doesn't define a read strobe, so set it equal to all bytes available for a transaction of
    // width 1 << HSIZE bytes.
    rw.byte_en = (128'd1 << (1 << bus_item.m_request.m_size)) - 1;

    if (bus_item.m_response == null) rw.data = 0;
    else rw.data = bus_item.m_response.m_rdata;
  end

  rw.status = (bus_item.m_response == null || bus_item.m_response.m_resp) ? UVM_NOT_OK : UVM_IS_OK;
endfunction
