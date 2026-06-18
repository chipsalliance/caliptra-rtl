// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that sends a sequence of ahb_txn_request_item items, representing a single burst.

class ahb_transfer_seq extends uvm_sequence #(ahb_txn_request_item, uvm_sequence_item);
  `uvm_object_utils(ahb_transfer_seq)

  // The percentage of transfers within the burst that should be TransBusy (so no data are sent)
  int unsigned m_busy_within_burst_pct = 50;

  // The subordinate that is being accessed by this burst.
  rand int unsigned m_subordinate_idx;

  // The HBURST value to send for items in the sequence.
  rand burst_e m_burst;

  // The number of transfers to perform in the burst. Note the sequence may contain some items with
  // a transfer type of TransBusy, so might have more than m_length items.
  rand int unsigned m_length;

  // The size of each data transfer (encoded as log2(byte_size))
  rand bit [2:0]    m_size;

  // Is this a sequence of writes?
  rand bit          m_write;

  // The address of the first data transfer (randomised with the sequence because it makes it easier
  // to avoid crossing boundaries)
  rand bit [63:0]   m_addr;

  // The set of requests that were sent. This will be at least as long as m_responses, but might be
  // longer if the sequence ended after a reset.
  ahb_txn_request_item  m_requests[$];

  // The responses that were seen to the requests in m_requests.
  ahb_txn_response_item m_responses[$];

  extern function new(string name="");
  extern task body();

  // Does this sequence show a full transaction?
  //
  // Call this after the sequence has run to completion. Then the sequence has seen a full
  // transaction iff there are the same number of responses as requests (so we haven't seen a
  // reset).
  extern function bit has_full_transaction();

  // Consume a response from the driver. If have_seen_reset is true, we have already seen a reset.
  //
  // Return true if we have now seen a reset.
  extern local function bit consume_response(uvm_sequence_item base_response, bit have_seen_reset);

  // Constrain m_length to be compatible with m_burst
  extern constraint length_burst_compat_c;

  // Alignment constraint for m_addr
  //
  // This constraint is a duplicate of ahb_txn_request_item::naturally_aligned_c and ensures that we
  // will pick a starting address that means the items in the sequence are aligned.
  extern constraint naturally_aligned_c;

  // No incrementing burst may cross a 1kb address boundary
  extern constraint increment_1kb_boundary_c;
endclass

function ahb_transfer_seq::new(string name="");
  super.new(name);
endfunction

task ahb_transfer_seq::body();
  ahb_txn_request_item item0  = ahb_txn_request_item::type_id::create("item0");

  // We might send more transfers than m_length because we sometimes add "busy" transfers, which act
  // as bubbles in the stream of data transfers. words_done is the count of items that have been
  // sent and had an m_trans other than TransBusy. We expect this to count up to m_length.
  int unsigned         words_done = 0;

  // Because the driver is designed to allow items to overlap (because the data phase of transfer N
  // overlaps with the address phase of transfer N+1), it marks items done immediately and we have
  // to explicitly consume responses. responses_seen is the number of responses that we have
  // consumed. This will never be larger than m_requests.size() but might be larger than words_done,
  // because we will also see responses to TransBusy requests.
  int unsigned         responses_seen = 0;

  // When the driver sees a reset being asserted, it sends a response that is an ahb_status_item.
  // Once that happens, we need to consume some extra responses (until responses_seen matches
  // m_requests.size())
  bit                  have_seen_reset = 0;

  // The size (in bytes) of the entire burst, inferred from the number of words and the number of
  // bytes in each word.
  bit [63:0]           total_size_bytes = m_length * (1 << m_size);

  // Wrapping bursts wrap their addresses, based on the total size of the burst (against which,
  // m_addr might not be naturally aligned). This variable is only used for wrapping bursts, where
  // m_length will be 4, 8 or 16. In that situation, total_size_bytes will be a power of 2 and
  // wrap_addr_base is the greatest multiple of total_size_bytes that is not larger than m_addr.
  bit [63:0]           wrap_addr_base = m_addr & ~(total_size_bytes - 1);

  // Randomise the first item that will be sent. This is also used as a template for later transfers
  // (which will use the same m_subordinate_idx, m_burst, m_size, m_write etc.)
  if (!item0.randomize() with {
        m_subordinate_idx == local::m_subordinate_idx;
        m_burst           == local::m_burst;
        m_size            == local::m_size;
        m_write           == local::m_write;
        m_addr            == local::m_addr;
        m_trans           == TransNonSequential;
        if (local::m_constrain_wdata && m_trans != TransBusy) {
          m_wdata == local::m_fixed_wdata;
        }
        if (local::m_constrain_wstrb && m_trans != TransBusy) {
          m_wstrb == local::m_fixed_wstrb;
        }
      }) begin
    `uvm_fatal(get_full_name(), "Failed to randomise item0.")
  end

  start_item(item0);
  finish_item(item0);
  m_requests.push_back(item0);
  words_done++;

  // Send items for the rest of the burst, possibly with occasional TransBusy items (which will end
  // up in m_requests and m_responses, but aren't counted in words_done). If we see a reset, stop
  // sending new items.
  while (words_done < m_length && !have_seen_reset) begin
    ahb_txn_request_item item = ahb_txn_request_item::type_id::create("item");
    bit [63:0] item_addr;
    trans_e    item_trans;

    if (m_burst inside {BurstWrap4, BurstWrap8, BurstWrap16}) begin
      // Offsets are measured from the start of the wrap window
      bit [63:0] linear_offset = (m_addr - wrap_addr_base) + words_done * (64'h1 << m_size);
      bit [63:0] wrapped_offset = linear_offset % total_size_bytes;

      item_addr = wrap_addr_base + wrapped_offset;
    end else begin
      // Non-wrapping offsets are measured from m_addr, which was the address of the first access.
      item_addr = m_addr + words_done * (64'h1 << m_size);
    end

    start_item(item);

    // Pick a value for m_trans. This should be either TransSequential or TransBusy (using
    // m_busy_within_burst_pct as a weighting).
    item_trans = ($urandom_range(99) < m_busy_within_burst_pct) ? TransBusy : TransSequential;

    if (!item.randomize() with {
          m_subordinate_idx == local::item0.m_subordinate_idx;
          m_addr            == local::item_addr;
          m_burst           == local::item0.m_burst;
          m_lock            == local::item0.m_lock;
          m_prot            == local::item0.m_prot;
          m_size            == local::item0.m_size;
          m_trans           == local::item_trans;
          m_write           == local::item0.m_write;
        }) begin
      `uvm_fatal(get_full_name(), "Failed to randomise item.")
    end

    finish_item(item);

    // Add item to m_requests to show that we've started trying to send this item.
    m_requests.push_back(item);

    // Look to see whether there have been any responses. If so consume them (in order). Add any
    // transaction responses to m_responses
    while (response_queue.size()) begin
      uvm_sequence_item base_response;
      get_base_response(base_response);
      responses_seen++;

      have_seen_reset = consume_response(base_response, have_seen_reset);
    end

    if (item.m_trans != TransBusy) begin
      words_done++;
    end
  end

  // At this point, we have stopped sending items (either because we have sent enough or because we
  // have seen a reset). The last few requests that were sent may not yet have a response. Consume
  // responses until we have caught up again.
  while (responses_seen < m_requests.size()) begin
    uvm_sequence_item base_response;
    get_base_response(base_response);
    responses_seen++;

    have_seen_reset = consume_response(base_response, have_seen_reset);
  end
endtask

function bit ahb_transfer_seq::has_full_transaction();
  return (m_requests.size() == m_responses.size());
endfunction

function bit ahb_transfer_seq::consume_response(uvm_sequence_item base_response,
                                                bit               have_seen_reset);
  ahb_txn_response_item txn_response;
  ahb_status_item       status_response;

  if ($cast(txn_response, base_response)) begin
    if (!have_seen_reset) m_responses.push_back(txn_response);
  end else if ($cast(status_response, base_response)) begin
    if (status_response.m_sending_complete) begin
      `uvm_error(get_full_name(), "Status response item sent with m_sending_complete=1.")
    end
    have_seen_reset = 1;
  end else begin
    `uvm_error(get_full_name(),
               {"Transaction sent a response that was neither an ",
                "ahb_txn_response_item nor an ahb_status_item."})
  end

  return have_seen_reset;
endfunction

constraint ahb_transfer_seq::length_burst_compat_c {
  m_length > 0;

  (m_burst == BurstSingle)                    -> m_length == 1;
  (m_burst inside {BurstWrap4, BurstIncr4})   -> m_length == 4;
  (m_burst inside {BurstWrap8, BurstIncr8})   -> m_length == 8;
  (m_burst inside {BurstWrap16, BurstIncr16}) -> m_length == 16;
}

constraint ahb_transfer_seq::naturally_aligned_c {
  (m_addr & ((1 << m_size) - 1)) == 0;
}

constraint ahb_transfer_seq::increment_1kb_boundary_c {
  if (m_burst inside {BurstIncr, BurstIncr4, BurstIncr8, BurstIncr16}) {
    ((m_addr + m_length * (1 << m_size) - 1) >> 10) == (m_addr >> 10);
  }
}
