// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item is sent back by drivers to show whether an item has actually been sent

class ahb_status_item extends uvm_sequence_item;
  `uvm_object_utils(ahb_status_item)

  // If this bit is set then the driver that was sending an item (and is responding with this one)
  // has finished sending the item.
  //
  // If the driver was interrupted by a reset, this bit will be clear.
  bit m_sending_complete;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
endclass

function ahb_status_item::new(string name = "");
  super.new(name);
endfunction

function void ahb_status_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_sending_complete", m_sending_complete, 1, UVM_BIN);
endfunction

function void ahb_status_item::do_copy(uvm_object rhs);
  ahb_status_item rhs_;

  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);

  m_sending_complete = rhs_.m_sending_complete;
endfunction

function bit ahb_status_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  ahb_status_item rhs_;

  // These items are only equivalent if rhs is actually an ahb_status_item.
  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not an ahb_status_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_field_int("m_sending_complete",
                                     m_sending_complete, rhs_.m_sending_complete, 1, UVM_BIN));
endfunction
