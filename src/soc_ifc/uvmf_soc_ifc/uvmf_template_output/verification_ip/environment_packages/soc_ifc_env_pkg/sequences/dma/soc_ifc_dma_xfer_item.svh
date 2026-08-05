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
// Captures one AXI DMA transfer (route, size, src/dst) with constraints that
// keep it legal for the bounded TB AXI SRAM and DMA command-decode rules:
//   - num_words is non-zero and <= max_words; byte_count = num_words*4.
//   - src/dst 4-byte aligned; [addr, addr+byte_count) fits window_bytes.
//   - AXI2AXI src/dst ranges must not overlap.
//
// window_bytes / max_words are non-rand knobs a test can override; pre_randomize
// rejects an oversized max_words so a misconfig fails loudly.
// NOTE: window_bytes must track the hdl_top DMA SRAM size (caliptra_axi_sram
// AW in hdl_top; AW=18 -> 256KB).
//----------------------------------------------------------------------

class soc_ifc_dma_xfer_item extends uvm_object;

  `uvm_object_utils( soc_ifc_dma_xfer_item )

  // ---- Tunable, non-random geometry knobs ----
  // SRAM window size in bytes (must match hdl_top i_dma_axi_sram AW).
  int unsigned window_bytes = (1 << 18); // 256KB
  // Max transfer size in words. Default exceeds the 512B (128-word) DMA FIFO to
  // exercise wrap, yet stays under mailbox capacity, and caps sim runtime.
  int unsigned max_words    = 160;

  // ---- Randomized transfer fields ----
  rand dma_route_e  route;
  rand int unsigned num_words;
  rand bit [63:0]   src_addr;
  rand bit [63:0]   dst_addr;

  function new(string name = "soc_ifc_dma_xfer_item");
    super.new(name);
  endfunction

  // Reject knob overrides the window cannot hold. Compare via window_bytes/4
  // (never max_words*4) so the check cannot overflow in 32-bit unsigned math.
  function void pre_randomize();
    if (max_words == 0 || max_words > (window_bytes / 4))
      `uvm_fatal(get_type_name(),
        $sformatf("Illegal geometry knobs: max_words=%0d must be >0 and <= window_bytes/4=%0d (window_bytes=%0d)",
                  max_words, (window_bytes / 4), window_bytes))
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

  // Keep each transfer inside the SRAM window. Bound the BASE address (not
  // "addr + size <= window"): src/dst are 64-bit, so "addr + size" could wrap
  // to a small value and admit an out-of-range addr. The num_words bound also
  // stops window_bytes - (num_words*4) from underflowing; using window_bytes/4
  // (a constant, floor is safe for non-power-of-2 windows) cannot overflow.
  constraint c_window_fit {
    num_words <= (window_bytes / 4);
    src_addr <= window_bytes - (num_words * 4);
    dst_addr <= window_bytes - (num_words * 4);
  }

  // Only AXI2AXI copies src->dst within the SRAM, so its ranges must be disjoint
  // to avoid corrupting in-flight data. MBOX and FIFO routes do not need this.
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
