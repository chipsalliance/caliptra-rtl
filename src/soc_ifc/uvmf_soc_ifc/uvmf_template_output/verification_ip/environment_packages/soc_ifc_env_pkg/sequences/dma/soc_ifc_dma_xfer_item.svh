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
// One AXI DMA transfer constrained legal for the SRAM window. Relative offsets
// are randomized for backdoor access; src_addr()/dst_addr() derive the absolute
// DMA addresses.
//----------------------------------------------------------------------

class soc_ifc_dma_xfer_item extends uvm_object;

  `uvm_object_utils( soc_ifc_dma_xfer_item )

  // ---- Non-random geometry knobs ----
  bit [63:0]       base_addr;
  longint unsigned window_bytes;
  protected bit    configured;
  // Max transfer size in words. Exceeds the 512B (128-word) DMA FIFO to exercise
  // wrap, stays under mailbox capacity, and caps sim runtime.
  int unsigned     max_words    = 160;

  // ---- Randomized transfer fields (SRAM-relative byte offsets) ----
  rand dma_route_e  route;
  rand int unsigned num_words;
  rand longint unsigned src_offset;
  rand longint unsigned dst_offset;

  // Payload words moved by the transfer. Auto-filled by post_randomize; set
  // directly for a directed transfer.
  bit [31:0] payload[];

  function new(string name = "soc_ifc_dma_xfer_item");
    super.new(name);
    configured = 1'b0;
  endfunction

  virtual function void configure(input bit [63:0]       base_addr,
                                  input longint unsigned window_bytes);
    this.base_addr    = base_addr;
    this.window_bytes = window_bytes;
    configured = 1'b1;
  endfunction

  // Reject a max_words the window cannot hold (compare via window_bytes/4 so the
  // check cannot overflow).
  function void pre_randomize();
    if (!configured)
      `uvm_fatal(get_type_name(), "DMA SRAM geometry must be configured before randomize()")
    if (max_words == 0 || max_words > (window_bytes / 4))
      `uvm_fatal(get_type_name(),
        $sformatf("Illegal geometry knobs: max_words=%0d must be >0 and <= window_bytes/4=%0d (window_bytes=%0d)",
                  max_words, (window_bytes / 4), window_bytes))
  endfunction

  function void post_randomize();
    payload = new[num_words];
    foreach (payload[i]) payload[i] = $urandom();
  endfunction

  function int unsigned byte_count();
    return num_words * 4;
  endfunction

  function bit [63:0] src_addr();
    return base_addr + src_offset;
  endfunction

  function bit [63:0] dst_addr();
    return base_addr + dst_offset;
  endfunction

  // Transfer size: at least one word, bounded by the runtime knob.
  constraint c_num_words { num_words inside {[1:max_words]}; }

  // 4-byte alignment (DMA requires byte_count/addresses aligned to DW bytes).
  constraint c_align {
    src_offset[1:0] == 2'b0;
    dst_offset[1:0] == 2'b0;
  }

  constraint c_window_fit {
    num_words <= (window_bytes / 4);
    src_offset <= (window_bytes - (num_words * 4));
    dst_offset <= (window_bytes - (num_words * 4));
  }

  // AXI2AXI copies src->dst within the SRAM, so its ranges must be disjoint.
  constraint c_no_overlap {
    (route == XFER_AXI2AXI) ->
      ((src_offset + (num_words * 4) <= dst_offset) ||
       (dst_offset + (num_words * 4) <= src_offset));
  }

  virtual function string convert2string();
    return $sformatf("route=%s num_words=%0d byte_count=%0d src_addr=0x%0h src_offset=0x%0h dst_addr=0x%0h dst_offset=0x%0h",
                     route.name(), num_words, byte_count(),
                     src_addr(), src_offset, dst_addr(), dst_offset);
  endfunction

endclass
