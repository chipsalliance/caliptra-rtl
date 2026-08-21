// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that sends a BurstSingle burst, reading a value from an address

class ahb_single_read_seq extends ahb_transfer_seq;
  `uvm_object_utils(ahb_single_read_seq)

  extern function new(string name="");

  // This should use BurstSingle
  extern constraint single_c;

  // The address transfer should request a read
  extern constraint read_c;
endclass

function ahb_single_read_seq::new(string name="");
  super.new(name);
endfunction

constraint ahb_single_read_seq::single_c {
  m_burst == BurstSingle;
}

constraint ahb_single_read_seq::read_c {
  !m_write;
}
