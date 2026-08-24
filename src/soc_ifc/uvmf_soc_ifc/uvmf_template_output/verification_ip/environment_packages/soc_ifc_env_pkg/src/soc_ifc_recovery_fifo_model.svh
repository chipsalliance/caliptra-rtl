// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Owns storage and accounting for the testbench implementation of the streaming
// recovery data buffer. AXI readers see a finite Avery FIFO at one address,
// while the DUT also sees recovery_data_avail and recovery_image_activated.
// Tests load a complete image through the recovery command sequencer. This
// model bridges those views with:
//   * backing_image_q for image words not yet exposed to AXI, and
//   * Avery's fifo_data_Q for the currently exposed front chunk.
//
// The model performs immediate state transitions only. The enclosing agent owns
// clocked handshake observation and refill-delay scheduling, while the recovery
// callback invokes pre-RVALID commit handling.
class soc_ifc_recovery_fifo_model extends uvm_object;

  `uvm_object_utils(soc_ifc_recovery_fifo_model)

  soc_ifc_recovery_fifo_config configuration; // Endpoint geometry and policies.
  aaxi_device_class bfm; // Recovery subordinate and its registered front FIFO.
  // Backing storage holds all words not yet exposed to AXI. It is intentionally
  // independent of front FIFO depth for test-sized recovery images.
  bit [31:0] backing_image_q[$];
  int unsigned front_fifo_dwords_available; // Staged words not handshaken.
  int unsigned image_dwords_consumed;       // Accepted DUT read beats.
  int unsigned total_image_dwords;          // Size of the current loaded image.
  int unsigned block_size_bytes;            // Requested staging block size.
  int unsigned block_size_dwords;           // Staging granularity.
  int unsigned generation; // Invalidates refill state after load/clear/reset.
  bit final_chunk_staged;   // No backing data remains after current chunk.
  bit last_staged_beat_committed; // Availability dropped before last R beat.
  bit underflow_reported;   // Suppresses duplicate errors for one generation.

  // Construct an empty recovery FIFO model.
  function new(string name = "soc_ifc_recovery_fifo_model");
    super.new(name);
    generation = 0;
  endfunction

  // Assign configuration and clear all image state.
  function void configure(soc_ifc_recovery_fifo_config configuration);
    if (configuration == null)
      `uvm_fatal("RECOVERY_FIFO", "Recovery FIFO configuration is null")
    this.configuration = configuration;
    clear();
  endfunction

  // Register the finite AXI-visible queue with the recovery subordinate. The
  // environment calls this after Avery has built the BFM but before any test
  // command can stage data.
  function void bind_bfm(aaxi_device_class bfm);
    if (bfm == null)
      `uvm_fatal("RECOVERY_FIFO", "Cannot bind a null Avery BFM")
    this.bfm = bfm;
    bfm.add_fifo(configuration.fifo_data_addr,
                 configuration.depth_dwords);
  endfunction

  // Resolve the queue by address instead of retaining an index that could
  // become stale if Avery or another callback adds FIFO entries.
  protected function int find_fifo();
    if (bfm == null)
      `uvm_fatal("RECOVERY_FIFO", "Avery BFM is not bound")
    foreach (bfm.fifo_address_Q[i])
      if (bfm.fifo_address_Q[i].addr == configuration.fifo_data_addr)
        return i;
    `uvm_fatal("RECOVERY_FIFO",
      $sformatf("Avery FIFO at address 0x%0h is not registered",
                configuration.fifo_data_addr))
    return -1;
  endfunction

  // Drive the streaming-boot sidebands observed by the DUT. Image activation
  // becomes sticky when the final staged chunk is advertised as available and
  // remains high until clear() starts a new flow or aborts the current flow.
  protected function void set_recovery_status(
      bit data_avail,
      bit image_activated);
    configuration.vif.recovery_data_avail = data_avail;
    configuration.vif.recovery_image_activated = image_activated;
  endfunction

  // Remove all backing and staged state. Incrementing generation allows the
  // clocked agent process to recognize that an outstanding refill countdown
  // belongs to an obsolete image.
  function void clear();
    int fifo_idx;
    generation++;
    backing_image_q.delete();
    front_fifo_dwords_available = 0;
    image_dwords_consumed = 0;
    total_image_dwords = 0;
    block_size_bytes = 0;
    block_size_dwords = 0;
    final_chunk_staged = 1'b0;
    last_staged_beat_committed = 1'b0;
    underflow_reported = 1'b0;
    if (configuration != null && configuration.vif != null)
      set_recovery_status(1'b0, 1'b0);
    if (bfm != null) begin
      fifo_idx = find_fifo();
      bfm.fifo_address_Q[fifo_idx].fifo_data_Q.delete();
    end
  endfunction

  // Validate the byte-based staging contract before mutating model state.
  // A block is the refill/staging granularity, not the complete image size. The
  // model restricts it to at most 64 bytes and requires it to fit in the finite
  // front FIFO so every non-final refill contains whole blocks.
  protected function bit validate_image(
      input bit [31:0] payload[],
      input int unsigned requested_block_size_bytes);
    if (payload.size() == 0) begin
      `uvm_fatal("RECOVERY_FIFO",
        "Cannot load an empty recovery image")
      return 1'b0;
    end
    if (requested_block_size_bytes < 4 ||
        requested_block_size_bytes > 64) begin
      `uvm_fatal("RECOVERY_FIFO",
        $sformatf("Block size %0d bytes must be in [4:64]",
                  requested_block_size_bytes))
      return 1'b0;
    end
    if ((requested_block_size_bytes &
         (requested_block_size_bytes - 1)) != 0) begin
      `uvm_fatal("RECOVERY_FIFO",
        $sformatf("Block size %0d bytes must be a power of two",
                  requested_block_size_bytes))
      return 1'b0;
    end
    if ((requested_block_size_bytes % 4) != 0) begin
      `uvm_fatal("RECOVERY_FIFO",
        $sformatf("Block size %0d bytes must be DWORD aligned",
                  requested_block_size_bytes))
      return 1'b0;
    end
    if ((requested_block_size_bytes / 4) >
        configuration.depth_dwords) begin
      `uvm_fatal("RECOVERY_FIFO",
        $sformatf(
          "Block size %0d DWORDs exceeds front FIFO depth %0d",
          requested_block_size_bytes / 4,
          configuration.depth_dwords))
      return 1'b0;
    end
    return 1'b1;
  endfunction

  // Load one complete image into backing storage, then expose the first
  // AXI-facing chunk. Final-partial status is derived from remaining image size;
  // no external payload-done control is needed.
  function void load_image(input bit [31:0] payload[],
                           input int unsigned requested_block_size_bytes);
    if (!validate_image(payload, requested_block_size_bytes))
      return;
    clear();
    block_size_bytes = requested_block_size_bytes;
    block_size_dwords = requested_block_size_bytes / 4;
    total_image_dwords = payload.size();
    foreach (payload[i])
      backing_image_q.push_back(payload[i]);
    void'(stage_next_chunk());
  endfunction

  // Transfer backing words into an empty Avery front FIFO. For non-final data,
  // stage the largest whole-block multiple that fits so refills never split a
  // block. The final chunk may be shorter because no later refill must preserve
  // a whole-block boundary.
  function int unsigned stage_next_chunk();
    int fifo_idx;
    int unsigned stage_dwords;
    aaxi_fifo entry;
    bit [31:0] data;

    if (bfm == null)
      `uvm_fatal("RECOVERY_FIFO", "Avery BFM is not bound")
    if (front_fifo_dwords_available != 0)
      `uvm_fatal("RECOVERY_FIFO",
        "Cannot refill a nonempty AXI-facing FIFO")
    if (backing_image_q.size() == 0)
      return 0;

    // Choosing final/non-final status before queue mutation allows both the
    // availability callback and coverage to describe the staged chunk.
    if (backing_image_q.size() <= configuration.depth_dwords) begin
      // All remaining image data fits, so this is the final chunk and may be
      // shorter than block_size_dwords.
      stage_dwords = backing_image_q.size();
      final_chunk_staged = 1'b1;
    end else begin
      stage_dwords =
        (configuration.depth_dwords / block_size_dwords) *
        block_size_dwords;
      final_chunk_staged = 1'b0;
    end
    if (stage_dwords == 0)
      `uvm_fatal("RECOVERY_FIFO",
        "No complete recovery block fits in the AXI-facing FIFO")
    if (stage_dwords > configuration.depth_dwords)
      `uvm_fatal("RECOVERY_FIFO",
        "Recovery refill exceeds AXI-facing FIFO depth")
    if (!final_chunk_staged &&
        (stage_dwords % block_size_dwords) != 0)
      `uvm_fatal("RECOVERY_FIFO",
        "Non-final recovery refill is not a whole block multiple")

    fifo_idx = find_fifo();
    // Keep direct construction of Avery queue entries isolated in this model so
    // sequences and agent control code remain independent of vendor internals.
    repeat (stage_dwords) begin
      data = backing_image_q.pop_front();
      entry = new(configuration.fifo_data_addr,
                  configuration.depth_dwords,
                  aaxi_beat_t'(data));
      for (int byte_idx = 0; byte_idx < 4; byte_idx++)
        entry.byteQ.push_back(data[byte_idx*8 +: 8]);
      bfm.fifo_address_Q[fifo_idx].fifo_data_Q.push_back(entry);
    end
    front_fifo_dwords_available = stage_dwords;
    last_staged_beat_committed = 1'b0;
    set_recovery_status(1'b1, final_chunk_staged);
    return stage_dwords;
  endfunction

  // Called by soc_ifc_recovery_fifo_callback before Avery presents an R beat.
  // The model's occupancy counter is not decremented yet because the manager may
  // stall RREADY. Only the sideband is committed early for the last staged word,
  // ensuring it is low by the eventual final handshake.
  function void note_read_beat_committed();
    if (front_fifo_dwords_available == 0)
      return;
    if (front_fifo_dwords_available == 1) begin
      configuration.vif.recovery_data_avail = 1'b0;
      last_staged_beat_committed = 1'b1;
    end
  endfunction

  // Called by the agent only after RVALID/RREADY. Account the consumed word and
  // return one when the front FIFO drains; the return value is the boundary
  // between storage accounting here and delayed refill scheduling in the agent.
  function bit note_read_beat_handshake();
    if (front_fifo_dwords_available == 0) begin
      if (!underflow_reported)
        `uvm_error("RECOVERY_FIFO",
          "Observed an R handshake while the front FIFO was empty")
      return 1'b0;
    end
    front_fifo_dwords_available--;
    image_dwords_consumed++;
    if (image_dwords_consumed > total_image_dwords)
      `uvm_error("RECOVERY_FIFO",
        "Consumed recovery data exceeded loaded image size")
    if (front_fifo_dwords_available == 0) begin
      if (!last_staged_beat_committed)
        `uvm_error("RECOVERY_FIFO",
          "recovery_data_avail was not deasserted before FIFO empty")
      configuration.vif.recovery_data_avail = 1'b0;
      return 1'b1;
    end
    return 1'b0;
  endfunction

  // Return the total number of DWORDs not yet consumed.
  function int unsigned image_dwords_remaining();
    return front_fifo_dwords_available + backing_image_q.size();
  endfunction

  // Return the number of DWORDs not yet staged into the front FIFO.
  function int unsigned backing_dwords_remaining();
    return backing_image_q.size();
  endfunction

  // Return one when no AXI-visible words remain.
  function bit front_fifo_empty();
    return front_fifo_dwords_available == 0;
  endfunction

  // Return one when the entire recovery image has been consumed.
  function bit image_complete();
    return image_dwords_remaining() == 0;
  endfunction

endclass
