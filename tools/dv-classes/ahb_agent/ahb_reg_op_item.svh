// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A simple uvm_sequence_item that holds a uvm_reg_bus_op and can be passed to the sequencer in
// ahb_mgr_register_layer_vseq.

class ahb_reg_op_item extends uvm_sequence_item;
  `uvm_object_utils(ahb_reg_op_item)

  // The wrapped uvm_reg_bus_op
  uvm_reg_bus_op m_rw;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
endclass

function ahb_reg_op_item::new(string name="");
  super.new(name);
endfunction

function void ahb_reg_op_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_string("m_rw.kind", m_rw.kind.name());
  printer.print_field("m_rw.addr", m_rw.addr, `UVM_REG_ADDR_WIDTH, UVM_HEX);
  printer.print_field("m_rw.data", m_rw.data, `UVM_REG_DATA_WIDTH, UVM_HEX);
  printer.print_field_int("m_rw.n_bits", m_rw.n_bits, 32, UVM_DEC);
  printer.print_field("m_rw.byte_en", m_rw.byte_en, `UVM_REG_BYTENABLE_WIDTH, UVM_HEX);
  printer.print_string("m_rw.status", m_rw.status.name());
endfunction

function void ahb_reg_op_item::do_copy(uvm_object rhs);
  ahb_reg_op_item rhs_;

  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  m_rw = rhs_.m_rw;
endfunction

function bit ahb_reg_op_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  ahb_reg_op_item rhs_;

  // These items are only equivalent if rhs is actually an ahb_reg_op_item.
  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not an ahb_reg_op_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_field_int("m_rw.kind", m_rw.kind, rhs_.m_rw.kind,
                                     $bits(m_rw.kind), UVM_HEX) &
          comparer.compare_field("m_rw.addr", m_rw.addr, rhs_.m_rw.addr,
                                 `UVM_REG_ADDR_WIDTH, UVM_HEX) &
          comparer.compare_field("m_rw.data", m_rw.data, rhs_.m_rw.data,
                                 `UVM_REG_DATA_WIDTH, UVM_HEX) &
          comparer.compare_field_int("m_rw.n_bits", m_rw.n_bits, rhs_.m_rw.n_bits, 32, UVM_DEC) &
          comparer.compare_field("m_rw.byte_en", m_rw.byte_en, rhs_.m_rw.byte_en,
                                 `UVM_REG_BYTENABLE_WIDTH, UVM_HEX) &
          comparer.compare_field_int("m_rw.status", m_rw.status, rhs_.m_rw.status,
                                     $bits(m_rw.status), UVM_HEX));
endfunction
