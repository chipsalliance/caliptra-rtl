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

// Implements the non-AXI control path into the external SRAM endpoint. The
// environment binds this driver to the subordinate BFM's aaxi_memory object,
// which is also the backing store used when the DUT reaches the endpoint over
// AXI. Consequently, sequence writes and reads modify and inspect the storage
// used by AXI transactions rather than a duplicate testbench copy.
//
// This component does not drive AXI signals. It serializes typed direct-memory
// requests and protects the vendor memory API with endpoint-relative bounds,
// DWORD alignment, and configured word_bytes boundary checks.
class soc_ifc_axi_sram_driver extends uvm_driver #(soc_ifc_axi_sram_item);

  `uvm_component_utils(soc_ifc_axi_sram_driver)

  aaxi_memory memory;         // Shared subordinate backing store.
  aaxi_addr_t base_addr;      // Start of the routed SRAM window.
  aaxi_addr_t limit_addr;     // Inclusive end of the routed SRAM window.
  int unsigned word_bytes;    // Configured region size for crossing checks.

  // Construct the SRAM item driver.
  function new(string name = "soc_ifc_axi_sram_driver",
               uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Capture geometry before requests can run. These checks mirror the config
  // object's validation because the driver is the final boundary protecting
  // direct vendor-memory calls, including factory-overridden construction.
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

  // Attach the exact memory object used by the SRAM subordinate. Binding is
  // deferred until environment connect_phase, when the fabric's BFM is
  // available for cross-component connection.
  function void bind_memory(aaxi_memory memory);
    if (memory == null)
      `uvm_fatal("AXI_SRAM", "Cannot bind a null Avery memory model")
    this.memory = memory;
  endfunction

  // Validate one byte offset and translate it to Avery's absolute address.
  // The final check enforces the configured rule that a DWORD cannot straddle
  // two word_bytes regions, even when it is legal in the full address window.
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

  // Write one DWORD directly into shared endpoint storage. A sequence can use
  // this path to initialize data before DUT AXI traffic accesses the endpoint.
  protected task write32_offset(input longint unsigned offset,
                                input bit [31:0] data);
    memory.mem_set_word(checked_address(offset), data);
  endtask

  // Read one DWORD directly from shared endpoint storage. The final argument
  // requests Avery's initialized-value checking for the location being read.
  protected task read32_offset(input longint unsigned offset,
                               output bit [31:0] data);
    logic [31:0] value;
    memory.mem_get_word(checked_address(offset), value, 1'b1);
    data = value;
  endtask

  // Process direct-memory commands until run_phase is terminated by UVM. A
  // response is returned for both operations: reads carry data, while writes
  // use it as an explicit "memory update complete" acknowledgement.
  virtual task run_phase(uvm_phase phase);
    soc_ifc_axi_sram_item request;
    soc_ifc_axi_sram_item response;
    forever begin
      seq_item_port.get_next_item(request);
      response = soc_ifc_axi_sram_item::type_id::create("response");
      // Preserve sequence and transaction IDs so a caller with multiple
      // outstanding sequence requests receives the corresponding response.
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
