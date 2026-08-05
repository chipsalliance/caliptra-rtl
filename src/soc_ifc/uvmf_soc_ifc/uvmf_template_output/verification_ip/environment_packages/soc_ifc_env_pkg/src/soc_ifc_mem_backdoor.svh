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
// DESCRIPTION: Reusable memory backdoor abstraction for the soc_ifc bench.
//
// Factory base owning memory geometry (path, base, size, word bytes) and access
// validation. Subclasses implement the offset access hooks and validate_path
// for a specific storage layout. Held in the env configuration and configured by
// test_top so sequences use relative offsets with no hierarchy knowledge. No
// mirror is kept: every access hits the actual HDL storage.
//----------------------------------------------------------------------

class soc_ifc_mem_backdoor extends uvm_object;

  `uvm_object_utils( soc_ifc_mem_backdoor )

  // ---- Geometry (set atomically via configure) ----
  protected string           hdl_path;   // HDL root path to the storage array
  protected bit [63:0]       base_addr;  // absolute byte address of offset 0
  protected longint unsigned size_bytes; // window size in bytes
  protected int unsigned     word_bytes; // storage word width in bytes
  protected bit              configured;

  function new(string name = "soc_ifc_mem_backdoor");
    super.new(name);
    configured = 1'b0;
  endfunction

  // Configure all geometry at once and validate it. Any misconfiguration is a
  // fatal (never a silent partial configuration).
  virtual function void configure(input string           path,
                                  input bit [63:0]       base,
                                  input longint unsigned size,
                                  input int unsigned     wbytes);
    hdl_path   = path;
    base_addr  = base;
    size_bytes = size;
    word_bytes = wbytes;
    validate_geometry();
    configured = 1'b1;
  endfunction

  // ---- Read-only geometry accessors ----
  virtual function string           get_hdl_path();   return hdl_path;   endfunction
  virtual function bit [63:0]       get_base_addr();  return base_addr;  endfunction
  virtual function longint unsigned get_size_bytes(); return size_bytes; endfunction
  virtual function int unsigned     get_word_bytes(); return word_bytes; endfunction

  // Validate static geometry. Supports storage words that are a nonzero multiple
  // of four bytes (covers common 32-bit and 64-bit caliptra_sram instances).
  protected virtual function void validate_geometry();
    if (hdl_path == "")
      `uvm_fatal("MEM_BKDR", "configure() called with empty hdl_path")
    if (size_bytes == 0)
      `uvm_fatal("MEM_BKDR", "configure() called with size_bytes==0")
    if (word_bytes == 0 || (word_bytes % 4 != 0))
      `uvm_fatal("MEM_BKDR",
        $sformatf("Unsupported word_bytes=%0d (must be a nonzero multiple of 4)", word_bytes))
    if ((size_bytes % word_bytes) != 0)
      `uvm_fatal("MEM_BKDR",
        $sformatf("size_bytes=%0d is not a multiple of word_bytes=%0d", size_bytes, word_bytes))
  endfunction

  // Validate a relative 32-bit access.
  protected virtual function void check_offset32(input longint unsigned offset);
    if (!configured)
      `uvm_fatal("MEM_BKDR", "32-bit access attempted before configure()")
    if (offset[1:0] != 2'b0)
      `uvm_fatal("MEM_BKDR", $sformatf("Unaligned 32-bit access offset=0x%0h", offset))
    // Subtract from size (never offset+4) so a large offset cannot wrap past the
    // 64-bit range and alias to an in-range value. size_bytes >= 4 is guaranteed
    // by validate_geometry (nonzero multiple of word_bytes).
    if (offset > (size_bytes - 4))
      `uvm_fatal("MEM_BKDR",
        $sformatf("Access offset=%0d past end (size_bytes=%0d)", offset, size_bytes))
    if (((offset % word_bytes) + 4) > word_bytes)
      `uvm_fatal("MEM_BKDR",
        $sformatf("32-bit access at offset=%0d crosses a storage word (word_bytes=%0d)",
                  offset, word_bytes))
  endfunction

  // ---- Public access API: validate, then delegate to the concrete backend ----
  virtual task write32_offset(input longint unsigned offset, input bit [31:0] data);
    check_offset32(offset);
    do_write32_offset(offset, data);
  endtask

  virtual task read32_offset(input longint unsigned offset, output bit [31:0] data);
    check_offset32(offset);
    do_read32_offset(offset, data);
  endtask

  // ---- Backend hooks ----
  // The base is factory-creatable for sibling backend overrides. These defaults
  // fatal if no concrete backend override is installed.
  virtual task do_write32_offset(input longint unsigned offset, input bit [31:0] data);
    `uvm_fatal("MEM_BKDR", "No memory backdoor write backend installed")
  endtask

  virtual task do_read32_offset(input longint unsigned offset, output bit [31:0] data);
    data = '0;
    `uvm_fatal("MEM_BKDR", "No memory backdoor read backend installed")
  endtask

  virtual function void validate_path();
    `uvm_fatal("MEM_BKDR", "No memory backdoor path-validation backend installed")
  endfunction

endclass


//----------------------------------------------------------------------
// Concrete backend for the caliptra_sram byte-array storage:
//   logic [7:0] ram [DEPTH][NUM_BYTES-1:0], indexed [word][byte_lane].
// Maps a relative byte offset to a word index and byte lane.
//----------------------------------------------------------------------

class soc_ifc_caliptra_sram_backdoor extends soc_ifc_mem_backdoor;

  `uvm_object_utils( soc_ifc_caliptra_sram_backdoor )

  function new(string name = "soc_ifc_caliptra_sram_backdoor");
    super.new(name);
  endfunction

  protected function void offset_to_index(input  longint unsigned offset,
                                          output int unsigned     word_idx,
                                          output int unsigned     lane);
    word_idx = int'(offset / word_bytes);
    lane     = int'(offset % word_bytes);
  endfunction

  virtual task do_write32_offset(input longint unsigned offset, input bit [31:0] data);
    string       path;
    int unsigned word_idx;
    int unsigned lane;
    offset_to_index(offset, word_idx, lane);
    for (int b = 0; b < 4; b++) begin
      path = $sformatf("%s[%0d][%0d]", hdl_path, word_idx, lane + b);
      if (!uvm_hdl_deposit(path, data[8*b +: 8]))
        `uvm_fatal("MEM_BKDR", $sformatf("uvm_hdl_deposit failed for %s", path))
    end
  endtask

  virtual task do_read32_offset(input longint unsigned offset, output bit [31:0] data);
    string       path;
    int unsigned word_idx;
    int unsigned lane;
    logic [63:0] val;
    offset_to_index(offset, word_idx, lane);
    data = '0;
    for (int b = 0; b < 4; b++) begin
      path = $sformatf("%s[%0d][%0d]", hdl_path, word_idx, lane + b);
      if (!uvm_hdl_read(path, val))
        `uvm_fatal("MEM_BKDR", $sformatf("uvm_hdl_read failed for %s", path))
      data[8*b +: 8] = val[7:0];
    end
  endtask

  // Check the first and last concrete element paths resolve. This catches a
  // path typo or a geometry mismatch versus the elaborated SRAM before stimulus.
  virtual function void validate_path();
    string           first_path;
    string           last_path;
    longint unsigned last_word;
    if (!configured)
      `uvm_fatal("MEM_BKDR", "validate_path() called before configure()")
    last_word  = (size_bytes / word_bytes) - 1;
    first_path = $sformatf("%s[0][0]", hdl_path);
    last_path  = $sformatf("%s[%0d][%0d]", hdl_path, last_word, word_bytes - 1);
    if (!uvm_hdl_check_path(first_path))
      `uvm_fatal("MEM_BKDR",
        $sformatf("uvm_hdl_check_path failed for %s (SRAM path/geometry mismatch)", first_path))
    if (!uvm_hdl_check_path(last_path))
      `uvm_fatal("MEM_BKDR",
        $sformatf("uvm_hdl_check_path failed for %s (SRAM path/geometry mismatch)", last_path))
  endfunction

endclass
