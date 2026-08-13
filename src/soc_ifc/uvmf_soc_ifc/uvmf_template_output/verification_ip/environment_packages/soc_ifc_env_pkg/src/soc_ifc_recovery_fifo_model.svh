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

// Models a complete recovery image behind a finite AXI-facing Avery FIFO.
// The backing queue decouples image size from physical FIFO depth; this object
// manages storage and invariants but performs no clocked refill scheduling.
class soc_ifc_recovery_fifo_model extends uvm_object;

  `uvm_object_utils(soc_ifc_recovery_fifo_model)

  soc_ifc_recovery_fifo_config configuration;
  aaxi_device_class bfm;
  // Backing storage holds all words not yet exposed to AXI. It is intentionally
  // independent of front FIFO depth for test-sized recovery images.
  bit [31:0] backing_image_q[$];
  int unsigned front_fifo_dwords_available;
  int unsigned image_dwords_consumed;
  int unsigned total_image_dwords;
  int unsigned block_size_bytes;
  int unsigned block_size_dwords;
  int unsigned generation;
  bit final_chunk_staged;
  bit last_staged_beat_committed;
  bit underflow_reported;

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

  // Register the finite front FIFO in the Avery BFM.
  function void bind_bfm(aaxi_device_class bfm);
    if (bfm == null)
      `uvm_fatal("RECOVERY_FIFO", "Cannot bind a null Avery BFM")
    this.bfm = bfm;
    bfm.add_fifo(configuration.fifo_data_addr,
                 configuration.depth_dwords);
  endfunction

  // Find the registered front FIFO index in the Avery model.
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

  // Drive recovery_data_avail through the configured virtual interface.
  protected function void set_data_avail(bit value);
    configuration.vif.recovery_data_avail = value;
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
      set_data_avail(1'b0);
    if (bfm != null) begin
      fifo_idx = find_fifo();
      bfm.fifo_address_Q[fifo_idx].fifo_data_Q.delete();
    end
  endfunction

  // Validate the DMA byte-based block contract before mutating model state.
  // Supported recovery blocks are at most one legal 64-byte FIXED AXI burst
  // and must fit in the front FIFO.
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

  // Fill an empty front FIFO with the largest whole-block multiple that fits.
  // Only the final chunk may be shorter than one block because DMA byte_count
  // tells hardware exactly how many final words remain.
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
    // Avery exposes no public preload API. Keep direct queue construction
    // isolated in this model so sequences and agent control code remain
    // independent of vendor internals.
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
    set_data_avail(1'b1);
    return stage_dwords;
  endfunction

  // Called before Avery presents an R beat. If it is the final staged word,
  // lower availability now so the signal is already low when that beat later
  // handshakes.
  function void note_read_beat_committed();
    if (front_fifo_dwords_available == 0)
      return;
    if (front_fifo_dwords_available == 1) begin
      set_data_avail(1'b0);
      last_staged_beat_committed = 1'b1;
    end
  endfunction

  // Called only after RVALID/RREADY. Account the consumed word and return one
  // when the front FIFO drains, which tells the agent to select and schedule
  // the next refill.
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
      set_data_avail(1'b0);
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
