// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is a register layering virtual sequence. It consumes ahb_reg_op_item objects from a
// sequencer and uses each to trigger a sequence on the AHB channel.
//
// It is designed to be used with ahb_mgr_reg_adapter with provides_responses=1, so calls put() on
// m_layered_sequencer to provide responses to the operations.

class ahb_mgr_register_layer_vseq extends uvm_sequence;
  `uvm_object_utils(ahb_mgr_register_layer_vseq)

  // A sequencer used as a source of register transactions that can be run, and the sequencer for
  // the AHB channel.
  //
  // These can be provided by calling set_sequencers, which must be done before
  // starting this sequence.
  local uvm_sequencer #(ahb_reg_op_item) m_layered_sequencer;
  local ahb_txn_sequencer_t              m_ahb_sequencer;

  // An array of known mappings from address range to subordinate index. Set this with
  // set_sub_mappings.
  local sub_addr_range_t m_subordinate_mappings[$];

  extern function new(string name="");
  extern task body();

  extern function void set_sequencers(ahb_reg_op_sequencer_t layered_sequencer,
                                      ahb_txn_sequencer_t    ahb_sequencer);

  // Set the subordinate mapping array
  //
  // Call this to configure the sequence before starting it.
  extern function void set_subordinates(const ref sub_addr_range_t mappings[$]);

  // Return the subordinate most recently associated with a range containing addr.
  extern local function int unsigned get_subordinate_for_addr(bit [63:0] addr);

  // Send the request item through a layered sequence, passing any information back by modifying the
  // item argument (by modifying its m_rw field).
  extern local task send_op_item(ahb_reg_op_item item);
endclass

function ahb_mgr_register_layer_vseq::new(string name="");
  super.new(name);
endfunction

task ahb_mgr_register_layer_vseq::body();
  if (m_layered_sequencer == null || m_ahb_sequencer == null) begin
    `uvm_fatal(get_full_name(), "Cannot run sequence because at least one sequencer is null.")
  end

  fork : isolation_fork begin
    forever begin
      ahb_reg_op_item item;
      m_layered_sequencer.get(item);

      // Run the item in the background. The send_op_item task completes when the generated virtual
      // sequence runs to completion, modifying the item in its item argument to represent the
      // response.
      //
      // At that point, we call m_layered_sequencer.put(item). The item will have originally come
      // from an ahb_mgr_reg_adapter and the response will now be passed back to that adapter's
      // bus2reg, which will be able to update a uvm_reg_bus_op in a uvm_reg_map, completing the
      // operation handshake.
      fork begin
        send_op_item(item);
        m_layered_sequencer.put(item);
      end join_none
    end
  end join
endtask

function void
  ahb_mgr_register_layer_vseq::set_sequencers(ahb_reg_op_sequencer_t layered_sequencer,
                                              ahb_txn_sequencer_t    ahb_sequencer);
  if (layered_sequencer == null) `uvm_fatal(get_full_name(), "No layered sequencer")
  if (ahb_sequencer == null)     `uvm_fatal(get_full_name(), "No ahb sequencer")

  m_layered_sequencer = layered_sequencer;
  m_ahb_sequencer     = ahb_sequencer;
endfunction

function void ahb_mgr_register_layer_vseq::set_subordinates(const ref sub_addr_range_t mappings[$]);
  m_subordinate_mappings.delete();
  foreach (mappings[i]) begin
    m_subordinate_mappings.push_back(mappings[i]);
  end
endfunction

function int unsigned ahb_mgr_register_layer_vseq::get_subordinate_for_addr(bit [63:0] addr);
  foreach (m_subordinate_mappings[i]) begin
    if (m_subordinate_mappings[i].addr_min <= addr &&
        addr <= m_subordinate_mappings[i].addr_max) begin
      return m_subordinate_mappings[i].subordinate_idx;
    end
  end

  `uvm_error(get_full_name(), $sformatf("No subordinate is associated with address 0x%0h", addr))
  return 0;
endfunction

task ahb_mgr_register_layer_vseq::send_op_item(ahb_reg_op_item item);
  // This task handles the bulk of the work that would normally be done by a uvm_reg_adapter's
  // reg2bus and bus2reg functions.

  int unsigned subordinate_idx = get_subordinate_for_addr(item.m_rw.addr);

  // item.m_rw.n_bits gives the number of bits that are being accessed. Since we don't support burst
  // accesses, round this up to the next value for HSIZE by dividing down to bytes (and taking the
  // ceiling), then taking clog2.
  int unsigned hsize = $clog2((item.m_rw.n_bits + 7) / 8);

  // This is the maximum strb value possible, given hsize. If byte_en is not maximal, the strb value
  // to actually use might not have all of the bits set.
  bit [127:0] strb_from_size = (128'd1 << (1 << hsize)) - 1;

  // The strb value to send on a write transaction, or the byte mask to use with rdata in an read
  // response. This takes size and byte_en into account.
  bit [127:0] byte_mask = strb_from_size & item.m_rw.byte_en;

  if (hsize > 7) begin
    `uvm_error(get_full_name(),
               $sformatf({"Cannot generate a sequence to represent an access with n_bits = %d: ",
                          "for a single transfer, this would need an HSIZE of %0d."},
                         item.m_rw.n_bits, hsize))
    item.m_rw.status = UVM_NOT_OK;
    return;
  end

  case (item.m_rw.kind)
    UVM_READ: begin
      // Single read
      ahb_transfer_seq read_seq = ahb_transfer_seq::type_id::create("read_seq");

      if (!read_seq.randomize() with {
            m_subordinate_idx == local::subordinate_idx;
            m_burst           == BurstSingle;
            m_size            == local::hsize;
            m_write           == 0;
            m_addr            == local::item.m_rw.addr;
          }) begin
        `uvm_fatal(get_full_name(), "Failed to randomise read_seq.")
      end

      // Run read_seq to completion
      read_seq.start(m_ahb_sequencer);

      // Has the sequence sent the complete transaction?
      if (!read_seq.has_full_transaction()) begin
        item.m_rw.status = UVM_NOT_OK;
      end else begin
        // If we have seen a complete transaction, we only really have to look at the last response,
        // which will be the response to the one and only non-busy data transfer that we sent.
        ahb_txn_response_item last_rsp = read_seq.m_responses[read_seq.m_responses.size() - 1];

        item.m_rw.data   = last_rsp.m_rdata;
        item.m_rw.status = last_rsp.m_resp ? UVM_NOT_OK : UVM_IS_OK;
      end
    end

    UVM_WRITE: begin
      // Single write
      ahb_single_write_seq write_seq = ahb_single_write_seq::type_id::create("write_seq");

      if (!write_seq.randomize() with {
            m_subordinate_idx == local::subordinate_idx;
            m_size            == local::hsize;
            m_addr            == local::item.m_rw.addr;
            m_wdata           == local::item.m_rw.data;
            m_wstrb           == local::byte_mask;
          }) begin
        `uvm_fatal(get_full_name(), "Failed to randomise seq.")
      end

      // Run seq to completion
      write_seq.start(m_ahb_sequencer);

      // Has the sequence sent the complete transaction?
      if (!write_seq.has_full_transaction()) begin
        item.m_rw.status = UVM_NOT_OK;
      end else begin
        // If we have seen a complete transaction, we only really have to look at the last response,
        // which will be the response to the one and only non-busy data transfer that we sent.
        ahb_txn_response_item last_rsp = write_seq.m_responses[write_seq.m_responses.size() - 1];

        item.m_rw.status = last_rsp.m_resp ? UVM_NOT_OK : UVM_IS_OK;
      end
    end

    default: begin
      // Something else (a burst read or write). Not yet supported.
      `uvm_error(get_full_name(),
                 $sformatf("Cannot send this uvm_reg_op. kind is %0s, which is not supported.",
                           item.m_rw.kind.name()))
      item.m_rw.status = UVM_NOT_OK;
      return;
    end
  endcase
endtask
