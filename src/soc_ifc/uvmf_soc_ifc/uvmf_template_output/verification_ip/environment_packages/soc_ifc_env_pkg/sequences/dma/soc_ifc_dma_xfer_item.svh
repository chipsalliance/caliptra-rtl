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
// are randomized for agent-owned memory access; src_addr()/dst_addr() derive
// the absolute DMA addresses.
//----------------------------------------------------------------------

// Describes one legal DMA transfer independently of the sequence that runs it.
// The item owns universal legality constraints; sequences select scenarios with
// checked randomize() calls and inline constraints.
class soc_ifc_dma_xfer_item extends uvm_object;

  `uvm_object_utils( soc_ifc_dma_xfer_item )

  // ---- Non-random geometry knobs ----
  protected bit [63:0]       base_addr;
  protected longint unsigned window_bytes;
  protected bit    configured;
  // Maximum transfer size in words, supplied by configure().
  protected int unsigned max_words;
  protected bit [63:0] recovery_fifo_addr;

  // ---- Randomized transfer fields (SRAM-relative byte offsets) ----
  rand dma_transfer_mode_e transfer_mode;
  rand int unsigned num_words;
  rand longint unsigned src_offset;
  rand longint unsigned dst_offset;
  rand int unsigned block_size_bytes;

  // Payload words moved by the transfer. post_randomize sizes and fills random
  // payloads; directed sequences may replace the generated data pattern.
  bit [31:0] payload[];

  // Construct an unconfigured transfer item.
  function new(string name = "soc_ifc_dma_xfer_item");
    super.new(name);
    configured = 1'b0;
  endfunction

  // Initialize the non-random geometry used by universal constraints.
  // base/window convert randomized offsets into absolute DMA addresses;
  // max_words bounds runtime; recovery_fifo_addr supplies the fixed source
  // address for recovery mode.
  function void configure(
      input bit [63:0] base_addr,
      input longint unsigned window_bytes,
      input int unsigned max_words,
      input bit [63:0] recovery_fifo_addr = 0);
    // Sanity check: max_words (words) must fit the SRAM window. Compare against
    // window_bytes/4 so the multiply-by-4 cannot overflow.
    if (max_words == 0 || max_words > (window_bytes / 4))
      `uvm_fatal(get_type_name(),
        $sformatf("Illegal geometry: max_words=%0d must be >0 and <= window_bytes/4=%0d (window_bytes=%0d)",
                  max_words, (window_bytes / 4), window_bytes))
    this.base_addr    = base_addr;
    this.window_bytes = window_bytes;
    this.max_words    = max_words;
    this.recovery_fifo_addr = recovery_fifo_addr;
    configured = 1'b1;
  endfunction

  // Fail before solving if a caller forgot configuration or supplied geometry
  // that cannot contain the requested maximum. Compare in words so multiplying
  // max_words by four cannot overflow during the check.
  function void pre_randomize();
    if (!configured)
      `uvm_fatal(get_type_name(), "AXI SRAM geometry must be configured before randomize()")
    if (max_words == 0 || max_words > (window_bytes / 4))
      `uvm_fatal(get_type_name(),
        $sformatf("Illegal geometry knobs: max_words=%0d must be >0 and <= window_bytes/4=%0d (window_bytes=%0d)",
                  max_words, (window_bytes / 4), window_bytes))
  endfunction

  // Size and populate the payload after the transfer geometry is solved.
  function void post_randomize();
    // Payload generation belongs to the item because every successful random
    // transfer needs exactly num_words of data. Directed sequences may overwrite
    // this random pattern after randomize() while preserving array size.
    payload = new[num_words];
    foreach (payload[i]) payload[i] = $urandom();
  endfunction

  // Return the transfer size in bytes.
  function int unsigned byte_count();
    return num_words * 4;
  endfunction

  // Return one when the transfer reads from the recovery FIFO.
  function bit is_recovery_source();
    return transfer_mode == DMA_XFER_AXI_RECOVERY;
  endfunction

  // Return the AXI fixed-burst requirement for the selected source.
  function bit read_is_fixed();
    return is_recovery_source();
  endfunction

  // Return the absolute source address for the selected transfer mode.
  function bit [63:0] src_addr();
    // Recovery is a single fixed FIFO address; memory sources add the randomized
    // byte offset to the configured SRAM base.
    return is_recovery_source() ?
           recovery_fifo_addr : (base_addr + src_offset);
  endfunction

  // Return the absolute destination SRAM address.
  function bit [63:0] dst_addr();
    // All currently supported destination routes that use this helper target
    // the external SRAM window.
    return base_addr + dst_offset;
  endfunction

  // Universal transfer bounds; scenario-specific sizing is constrained inline
  // by the sequence that randomizes this item.
  constraint c_num_words {
    num_words inside {[1:max_words]};
  }

  // Equal mode weights are the reusable default for unconstrained DMA items.
  // A sequence may constrain transfer_mode for a directed scenario without
  // carrying a second distribution.
  constraint c_transfer_mode_distribution {
    transfer_mode dist {
      DMA_XFER_AXI_MEMORY   := 20,
      DMA_XFER_AXI_RECOVERY := 20,
      DMA_XFER_READ_FIFO    := 20,
      DMA_XFER_WRITE_FIFO   := 20,
      DMA_XFER_MAILBOX      := 20
    };
  }

  // 4-byte alignment (DMA requires byte_count/addresses aligned to DW bytes).
  constraint c_align {
    src_offset[1:0] == 2'b0;
    dst_offset[1:0] == 2'b0;
    transfer_mode == DMA_XFER_AXI_RECOVERY ->
      ((dst_offset % block_size_bytes) == 0);
  }

  constraint c_mode {
    transfer_mode == DMA_XFER_AXI_RECOVERY -> {
      block_size_bytes inside {
        4, 8, 16, 32, 64
      };
      recovery_fifo_addr != 0;
    }
    transfer_mode != DMA_XFER_AXI_RECOVERY -> {
      block_size_bytes == 0;
    }
  }

  constraint c_window_fit {
    num_words <= (window_bytes / 4);
    transfer_mode inside {
      DMA_XFER_AXI_MEMORY,
      DMA_XFER_READ_FIFO,
      DMA_XFER_MAILBOX
    } ->
      src_offset <= (window_bytes - (num_words * 4));
    transfer_mode inside {
      DMA_XFER_AXI_MEMORY,
      DMA_XFER_AXI_RECOVERY,
      DMA_XFER_WRITE_FIFO,
      DMA_XFER_MAILBOX
    } ->
      dst_offset <= (window_bytes - (num_words * 4));
    transfer_mode inside {
      DMA_XFER_AXI_RECOVERY,
      DMA_XFER_WRITE_FIFO
    } ->
      src_offset == 0;
    transfer_mode == DMA_XFER_READ_FIFO ->
      dst_offset == 0;
  }

  // AXI2AXI copies src->dst within the SRAM, so its ranges must be disjoint.
  constraint c_no_overlap {
    transfer_mode == DMA_XFER_AXI_MEMORY ->
      ((src_offset + (num_words * 4) <= dst_offset) ||
       (dst_offset + (num_words * 4) <= src_offset));
  }

  // Format the solved transfer for checkpoint and error reporting.
  virtual function string convert2string();
    return $sformatf("transfer_mode=%s read_fixed=%0b block_size_bytes=%0d num_words=%0d byte_count=%0d src_addr=0x%0h src_offset=0x%0h dst_addr=0x%0h dst_offset=0x%0h",
                     transfer_mode.name(), read_is_fixed(), block_size_bytes,
                     num_words, byte_count(),
                     src_addr(), src_offset, dst_addr(), dst_offset);
  endfunction

endclass
