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

// Routes typed SRAM items to the agent-owned Avery memory. Every relative DWORD
// offset is checked before conversion to an absolute memory-model address.
class soc_ifc_axi_sram_driver extends uvm_driver #(soc_ifc_axi_sram_item);

  `uvm_component_utils(soc_ifc_axi_sram_driver)

  aaxi_memory memory;
  aaxi_addr_t base_addr;
  aaxi_addr_t limit_addr;
  int unsigned word_bytes;

  // Construct the SRAM item driver.
  function new(string name = "soc_ifc_axi_sram_driver",
               uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Configure the legal SRAM window and memory word width.
  function void configure(input aaxi_addr_t base_addr,
                          input aaxi_addr_t limit_addr,
                          input int unsigned word_bytes);
    if (limit_addr < base_addr)
      `uvm_fatal("AXI_SRAM", "SRAM driver address limit is below base")
    if ((longint'(limit_addr - base_addr) + 1) < 4)
      `uvm_fatal("AXI_SRAM", "SRAM driver window is smaller than one DWORD")
    if (word_bytes == 0 || (word_bytes % 4) != 0)
      `uvm_fatal("AXI_SRAM",
        "SRAM driver word width must be a nonzero DWORD multiple")
    this.base_addr = base_addr;
    this.limit_addr = limit_addr;
    this.word_bytes = word_bytes;
  endfunction

  // Attach the Avery memory model used for direct item accesses.
  function void bind_memory(aaxi_memory memory);
    if (memory == null)
      `uvm_fatal("AXI_SRAM", "Cannot bind a null Avery memory model")
    this.memory = memory;
  endfunction

  // Validate and translate one relative DWORD offset.
  protected function aaxi_addr_t checked_address(
      input longint unsigned offset);
    longint unsigned size_bytes;
    if (memory == null)
      `uvm_fatal("AXI_SRAM", "Avery memory model is not bound")
    size_bytes = longint'(limit_addr - base_addr) + 1;
    if (offset[1:0] != 2'b0)
      `uvm_fatal("AXI_SRAM",
        $sformatf("Unaligned SRAM offset 0x%0h", offset))
    if (offset > (size_bytes - 4))
      `uvm_fatal("AXI_SRAM",
        $sformatf("SRAM offset %0d exceeds window size %0d",
                  offset, size_bytes))
    if (((offset % word_bytes) + 4) > word_bytes)
      `uvm_fatal("AXI_SRAM",
        $sformatf("DWORD at offset %0d crosses a %0d-byte memory word",
                  offset, word_bytes))
    return aaxi_addr_t'(base_addr + offset);
  endfunction

  // Write one DWORD at a checked SRAM-relative offset.
  protected task write32_offset(input longint unsigned offset,
                                input bit [31:0] data);
    memory.mem_set_word(checked_address(offset), data);
  endtask

  // Read one DWORD at a checked SRAM-relative offset.
  protected task read32_offset(input longint unsigned offset,
                               output bit [31:0] data);
    logic [31:0] value;
    memory.mem_get_word(checked_address(offset), value, 1'b1);
    data = value;
  endtask

  // Process SRAM items until the run phase ends.
  virtual task run_phase(uvm_phase phase);
    soc_ifc_axi_sram_item request;
    soc_ifc_axi_sram_item response;
    forever begin
      seq_item_port.get_next_item(request);
      response = soc_ifc_axi_sram_item::type_id::create("response");
      response.set_id_info(request);
      response.operation = request.operation;
      response.offset = request.offset;
      case (request.operation)
        AXI_SRAM_WRITE:
          write32_offset(request.offset, request.data);
        AXI_SRAM_READ:
          read32_offset(request.offset, response.data);
        default:
          `uvm_fatal("AXI_SRAM", "Unsupported SRAM agent operation")
      endcase
      seq_item_port.item_done(response);
    end
  endtask

endclass
