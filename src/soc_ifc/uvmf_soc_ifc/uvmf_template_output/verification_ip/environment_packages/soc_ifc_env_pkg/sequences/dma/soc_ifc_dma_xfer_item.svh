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
//
//----------------------------------------------------------------------
// DESCRIPTION: Constrained-random DMA transfer descriptor.
//
// Captures the randomizable inputs of one AXI DMA transfer (route, size, and
// source/destination addresses) with constraints that keep the transfer legal
// for the bounded TB AXI SRAM and the DMA command-decode rules:
//   - byte_count = num_words*4 is non-zero, 4-byte aligned, and bounded by
//     max_words (a sim-runtime knob, well within DMA_MAX_XFER_SIZE = 1MiB).
//   - src/dst are 4-byte aligned and their [addr, addr+byte_count) ranges fit
//     inside the bounded SRAM window (window_bytes).
//   - For AXI2AXI (both source and destination are live) the two ranges must
//     not overlap.
//
// window_bytes / max_words are plain (non-rand) knobs a test can override.
// NOTE: window_bytes must track the hdl_top DMA SRAM size (caliptra_axi_sram
// AW in hdl_top; AW=18 -> 256KB).
//----------------------------------------------------------------------

class soc_ifc_dma_xfer_item extends uvm_object;

  `uvm_object_utils( soc_ifc_dma_xfer_item )

  // ---- Tunable, non-random geometry knobs ----
  // Bounded SRAM window size in bytes (must match hdl_top i_dma_axi_sram AW).
  int unsigned window_bytes = (1 << 18); // 256KB
  // Upper bound on transfer size (words). Default caps sim runtime while still
  // exceeding the 512B (128-word) internal DMA FIFO to exercise FIFO wrap. Also
  // stays well under the mailbox capacity, so MBOX transfers need no size cap.
  int unsigned max_words    = 160;

  // ---- Randomized transfer fields ----
  rand dma_route_e  route;
  rand int unsigned num_words;
  rand bit [63:0]   src_addr;
  rand bit [63:0]   dst_addr;

  function new(string name = "soc_ifc_dma_xfer_item");
    super.new(name);
  endfunction

  function int unsigned byte_count();
    return num_words * 4;
  endfunction

  // Transfer size: at least one word, bounded by the runtime knob.
  constraint c_num_words { num_words inside {[1:max_words]}; }

  // 4-byte alignment (DMA requires byte_count and addresses aligned to the
  // data-width byte count; DW=32 -> 4 bytes).
  constraint c_align {
    src_addr[1:0] == 2'b0;
    dst_addr[1:0] == 2'b0;
  }

  // Keep each transfer inside the bounded SRAM window. Bound the BASE address
  // directly (rather than "addr + size <= window") because src_addr/dst_addr are
  // 64-bit: "addr + size <= window" can be satisfied by a huge addr whose 64-bit
  // sum WRAPS AROUND to a small value, admitting out-of-range addresses that the
  // DMA rejects as a command-decode error. Bounding addr <= window - size forces
  // the upper address bits to zero and cannot overflow (size << window_bytes).
  constraint c_window_fit {
    src_addr <= window_bytes - (num_words * 4);
    dst_addr <= window_bytes - (num_words * 4);
  }

  // Only AXI2AXI needs disjoint windows: it copies src->dst directly within the
  // SRAM, so overlap would corrupt the in-flight data. MBOX buffers the whole
  // payload in the mailbox, and FIFO routes touch only one address, so neither needs it.
  constraint c_no_overlap {
    (route == XFER_AXI2AXI) ->
      ((src_addr + (num_words * 4) <= dst_addr) ||
       (dst_addr + (num_words * 4) <= src_addr));
  }

  virtual function string convert2string();
    return $sformatf("route=%s num_words=%0d byte_count=%0d src=0x%0h dst=0x%0h",
                     route.name(), num_words, byte_count(), src_addr, dst_addr);
  endfunction

endclass
