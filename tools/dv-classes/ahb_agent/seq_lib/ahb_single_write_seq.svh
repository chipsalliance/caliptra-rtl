// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that sends a BurstSingle, writing a value to an address

class ahb_single_write_seq extends ahb_transfer_seq;
  `uvm_object_utils(ahb_single_write_seq)

  // The wdata to send with the one and only data phase item that sends write data
  rand bit [1023:0] m_wdata;

  // The wstrb to send with the one and only data phase item that sends write data
  rand bit [127:0]  m_wstrb;

  extern function new(string name="");

  // Randomise the first item. This extends a function in ahb_transfer_seq.
  extern protected function void randomize_first_item(ahb_txn_request_item item);

  // This should use BurstSingle
  extern constraint single_c;

  // The address transfer should request a write
  extern constraint write_c;

  // Mirror m_wdata / m_wstrb to the protected m_fixed_wdata / m_fixed_wstrb fields
  extern constraint fixed_data_strb_c;
endclass

function ahb_single_write_seq::new(string name="");
  super.new(name);
endfunction

function void ahb_single_write_seq::randomize_first_item(ahb_txn_request_item item);
  bit [1:0] old_flags = {m_constrain_wdata, m_constrain_wstrb};

  // Set m_constrain_wdata / m_constrain_wstrb for while the item is being randomised, meaning that
  // it gets the values in m_wdata / m_wstrb (which have been mirrored in m_fixed_wdata /
  // m_fixed_wstrb).
  m_constrain_wdata = 1;
  m_constrain_wstrb = 1;

  super.randomize_first_item(item);

  m_constrain_wdata = old_flags[1];
  m_constrain_wstrb = old_flags[0];
endfunction


constraint ahb_single_write_seq::single_c {
  m_burst == BurstSingle;
}

constraint ahb_single_write_seq::write_c {
  m_write;
}

constraint ahb_single_write_seq::fixed_data_strb_c {
  m_fixed_wdata == m_wdata;
  m_fixed_wstrb == m_wstrb;
}
