// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item that represents an entire transaction (with a request and then a response)

class ahb_txn_item extends uvm_sequence_item;
  `uvm_object_utils(ahb_txn_item)

  // The request in the transaction.
  ahb_txn_request_item  m_request;

  // The response in the transaction. This might be null, if the monitor saw a reset before a
  // response had come back.
  ahb_txn_response_item m_response;

  extern function new(string name="");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
endclass

function ahb_txn_item::new(string name="");
  super.new(name);
endfunction

function void ahb_txn_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_object("m_request", m_request);
  printer.print_object("m_response", m_response);
endfunction

function void ahb_txn_item::do_copy(uvm_object rhs);
  ahb_txn_item rhs_;

  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);

  if (rhs_.m_request == null) m_request = null;
  else if (!$cast(m_request, rhs_.m_request.clone())) begin
    `uvm_fatal("do_copy", "Failed to clone m_request.")
  end
  
  if (rhs_.m_response == null) m_response = null;
  else if (!$cast(m_response, rhs_.m_response.clone())) begin
    `uvm_fatal("do_copy", "Failed to clone m_response.")
  end
endfunction

function bit ahb_txn_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  ahb_txn_item rhs_;

  // These items are only equivalent if rhs is actually an ahb_txn_item.
  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not an ahb_txn_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_object("m_request", m_request, rhs_.m_request) &
          comparer.compare_object("m_response", m_response, rhs_.m_response));
endfunction
