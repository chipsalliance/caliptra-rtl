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
