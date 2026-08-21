// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item that represents a message sent by an AHB Subordinate to respond to a read or
// write transaction.

class ahb_txn_response_item extends uvm_sequence_item;
  `uvm_object_utils(ahb_txn_response_item)

  // Read data (used when responding to a read)
  //
  // Note that (unlike the HRDATA signal), the bottom bit of the access is in the LSB of this field.
  // The driver and monitor are responsible for shifting to the correct byte lane for DATA_WIDTH.
  // For example, if 0x12 is being read from address 0x1, m_rdata will be 0x12 rather than 0x1200.
  //
  // This is sent over the HRDATA signal, whose width is configurable based on the DATA_WIDTH
  // property. The representation in the item uses a max footprint approach, supporting up to 1024
  // bits: the maximum size from the AHB specification (issue C). The driver will fail with an error
  // if bits above the configured width are nonzero.
  rand bit [1023:0] m_rdata;

  // Transfer response
  //
  // This bit is high if the transfer status is ERROR.
  rand bit          m_resp;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
endclass

function ahb_txn_response_item::new(string name = "");
  super.new(name);
endfunction

function void ahb_txn_response_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field("m_rdata", m_rdata, 1024, UVM_HEX);
  printer.print_field_int("m_resp", m_resp, 1, UVM_BIN);
endfunction

function void ahb_txn_response_item::do_copy(uvm_object rhs);
  ahb_txn_response_item rhs_;
  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  this.m_rdata = rhs_.m_rdata;
  this.m_resp  = rhs_.m_resp;
endfunction

function bit ahb_txn_response_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  ahb_txn_response_item rhs_;

  // These items are only equivalent if rhs is actually an ahb_txn_response_item.
  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not an ahb_txn_response_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_field("m_rdata", m_rdata, rhs_.m_rdata, 1024, UVM_HEX) &
          comparer.compare_field_int("m_resp", m_resp, rhs_.m_resp, 1, UVM_BIN));
endfunction
