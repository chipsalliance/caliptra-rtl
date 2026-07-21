// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item that represents a message sent by an AHB Manager to request a read or write
// transaction.
//
// This is a single transfer (sent in the address phase of one cycle). A burst will contain multiple
// transfers, represented by multiple items of this class.

class ahb_txn_request_item extends uvm_sequence_item;
  `uvm_object_utils(ahb_txn_request_item)

  // The index of the subordinate to select
  //
  // This will be sent over the HSEL signal and the maximum value is configurable, based on the
  // num_subordinates parameter in the interface. The driver will fail with an error if the index is
  // too high.
  rand int unsigned m_subordinate_idx;

  // Transaction address
  //
  // This is sent over the HADDR signal, whose width is configurable, based on the ADDR_WIDTH
  // property. The representation in the item uses a max footprint approach (based on the
  // recommended 10..64 range from the AHB specification, issue C) but the driver will fail with an
  // error if bits above the configured width are nonzero.
  rand bit [63:0]   m_addr;

  // Burst attribute
  rand burst_e      m_burst;

  // Request exclusive access
  rand bit          m_lock;

  // Protection control
  //
  // This is sent over the HPROT signal, whose width is configurable, based on the HPROT_WIDTH
  // property, which the AHB specification (issue C) requires to be 0, 4 or 7. The driver will fail
  // with an error if bits above the configured width are nonzero.
  rand bit [6:0]    m_prot;

  // The size of each data transfer (encoded as log2(byte_size))
  //
  // The resulting byte size must be compatible with the width of the HWDATA signal, which is based
  // on the DATA_WIDTH property. If this value is too large for the interface's DATA_WIDTH, the
  // transfer might not work properly (but the driver will accept it: HSIZE will still be
  // representable).
  rand bit [2:0]    m_size;

  // Transfer type
  rand trans_e      m_trans;

  // Write data (used when m_write is true)
  //
  // Note that (unlike the HWDATA signal), the bottom bit of the access is in the LSB of this field.
  // The driver and monitor are responsible for shifting to the correct byte lane for DATA_WIDTH.
  // For example, if 0x12 is being written to address 0x1, m_wdata will be 0x12 rather than 0x1200.
  //
  // This is sent over the HWDATA signal, whose width is configurable based on the DATA_WIDTH
  // property. The representation in the item uses a max footprint approach, supporting up to 1024
  // bits: the maximum size from the AHB specification (issue C). The driver will fail with an error
  // if bits above the configured width are nonzero.
  rand bit [1023:0] m_wdata;

  // Write strobe (used when m_write is true)
  //
  // Note that (unlike the HWSTRB signal), the bottom bit of the access is in the LSB of this field.
  // The driver and monitor are responsible for shifting to the correct byte lane for DATA_WIDTH.
  // For example, if 0x12 is being written to address 0x1 and only a single strobe bit is asserted,
  // m_wstrb will be 'b1 rather than 'b10.
  //
  // This is sent over the HWSTRB signal, which is only present in the interface if the
  // Write_Strobes property is true and (if so) whose whose width is configurable based on the
  // DATA_WIDTH property. The representation in the item uses a max footprint approach, supporting
  // up to 128 strobe bits: the maximum size from the AHB specification (issue C). The driver will
  // fail with an error if bits above the configured width are nonzero.
  rand bit [127:0]  m_wstrb;

  // Transfer direction (true if this is a write)
  rand bit          m_write;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);

  // Confine m_subordinate_idx to be bounded by the biggest value supported by the driver. The
  // constraint might be tighter (depending on num_subordinates in the interface), but this
  // constraint definitely applies.
  extern constraint max_subordinate_idx_c;

  // The transfer must be naturally aligned
  extern constraint naturally_aligned_c;

  // If this is a write, m_wdata must be representable with 1 << m_size bytes.
  extern constraint write_size_c;

  // If this is a write, m_wstrb must be representable with 1 << m_size bits.
  extern constraint strb_size_c;
endclass

function ahb_txn_request_item::new(string name = "");
  super.new(name);
endfunction

function void ahb_txn_request_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_subordinate_idx", m_subordinate_idx, 32, UVM_DEC);
  printer.print_field("m_addr", m_addr, 64, UVM_HEX);
  printer.print_string("m_burst", m_burst.name());
  printer.print_field_int("m_lock", m_lock, 1, UVM_BIN);
  printer.print_field_int("m_prot", m_prot, 7, UVM_DEC);
  printer.print_field_int("m_size", m_size, 3, UVM_DEC);
  printer.print_string("m_trans", m_trans.name());
  if (m_write) begin
    printer.print_field("m_wdata", m_wdata, 1024, UVM_HEX);
    printer.print_field("m_wstrb", m_wstrb, 128, UVM_HEX);
  end
  printer.print_field_int("m_write", m_write, 1, UVM_BIN);
endfunction

function void ahb_txn_request_item::do_copy(uvm_object rhs);
  ahb_txn_request_item rhs_;
  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  this.m_subordinate_idx = rhs_.m_subordinate_idx;
  this.m_addr            = rhs_.m_addr;
  this.m_burst           = rhs_.m_burst;
  this.m_lock            = rhs_.m_lock;
  this.m_prot            = rhs_.m_prot;
  this.m_size            = rhs_.m_size;
  this.m_trans           = rhs_.m_trans;
  this.m_wdata           = rhs_.m_wdata;
  this.m_wstrb           = rhs_.m_wstrb;
  this.m_write           = rhs_.m_write;
endfunction

function bit ahb_txn_request_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  ahb_txn_request_item rhs_;
  bit all_match;

  // These items are only equivalent if rhs is actually an ahb_txn_request_item.
  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not an ahb_txn_request_item.");
    return 0;
  end

  // Note: The rather imperative code structure for the rest of this function ensures we only
  // compare fields that matter (so don't compare wdata for reads) and that we do the comparisons in
  // the order in the specification. This means that mismatches will be listed in the same order as
  // that document.

  all_match = super.do_compare(rhs, comparer);
  all_match &= comparer.compare_field_int("m_subordinate_idx",
                                          m_subordinate_idx, rhs_.m_subordinate_idx,
                                          32, UVM_DEC);
  all_match &= comparer.compare_field("m_addr", m_addr, rhs_.m_addr, 64, UVM_HEX);
  all_match &= comparer.compare_field_int("m_burst", m_burst, rhs_.m_burst, 3, UVM_ENUM);
  all_match &= comparer.compare_field_int("m_lock", m_lock, rhs_.m_lock, 1, UVM_BIN);
  all_match &= comparer.compare_field_int("m_prot", m_prot, rhs_.m_prot, 7, UVM_DEC);
  all_match &= comparer.compare_field_int("m_size", m_size, rhs_.m_size, 3, UVM_DEC);
  all_match &= comparer.compare_field_int("m_trans", m_trans, rhs_.m_trans, 2, UVM_ENUM);

  if (m_write || rhs_.m_write) begin
    all_match &= comparer.compare_field("m_wdata", m_wdata, rhs_.m_wdata, 1024, UVM_HEX);
    all_match &= comparer.compare_field("m_wstrb", m_wstrb, rhs_.m_wstrb, 128, UVM_HEX);
  end

  all_match &= comparer.compare_field_int("m_write", m_write, rhs_.m_write, 1, UVM_BIN);

  return all_match;
endfunction

constraint ahb_txn_request_item::max_subordinate_idx_c {
  m_subordinate_idx < 8;
}

constraint ahb_txn_request_item::naturally_aligned_c {
  (m_addr & ((1 << m_size) - 1)) == 0;
}

constraint ahb_txn_request_item::write_size_c {
  if (m_write) {
    (m_wdata >> (8 << m_size)) == '0;
  }
}

constraint ahb_txn_request_item::strb_size_c {
  if (m_write) {
    (m_wstrb >> (1 << m_size)) == '0;
  }
}
