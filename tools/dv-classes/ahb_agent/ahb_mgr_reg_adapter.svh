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
  ahb_reg_op_item ahb_bus_item;
  if (!$cast(ahb_bus_item, bus_item)) begin
    `uvm_fatal(get_name(), "Cannot convert bus item to an ahb_reg_op_item.")
  end

  // Replace all the fields in rw that bus2reg would normally populate (kind, addr, data and status)
  rw.kind = ahb_bus_item.m_rw.kind;
  rw.addr = ahb_bus_item.m_rw.addr;
  rw.data = ahb_bus_item.m_rw.data;
  rw.status = ahb_bus_item.m_rw.status;
endfunction
