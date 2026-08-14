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

// Describes the direct, testbench-side SRAM operations supported by the
// external-memory endpoint agent. These are not AXI bus transactions. A virtual
// sequence can use them to initialize or inspect the same storage reached by
// DUT AXI traffic without driving a second AXI manager.
typedef enum int {
  AXI_SRAM_WRITE,
  AXI_SRAM_READ
} soc_ifc_axi_sram_operation_e;

// Carries one direct SRAM DWORD access from soc_ifc_axi_sram_access_sequence to
// soc_ifc_axi_sram_driver. The driver applies offset and alignment checks, then
// accesses the same Avery memory object that services DUT AXI traffic. Read data
// returns in the response item; writes also use a response so the caller cannot
// continue before the shared memory has been updated.
class soc_ifc_axi_sram_item extends uvm_sequence_item;

  `uvm_object_utils(soc_ifc_axi_sram_item)

  soc_ifc_axi_sram_operation_e operation; // Direct-memory operation to perform.
  longint unsigned offset;                // Byte offset from SRAM base_addr.
  bit [31:0] data;                        // Write payload or returned read data.

  // Construct an SRAM item.
  function new(string name = "soc_ifc_axi_sram_item");
    super.new(name);
  endfunction

endclass

// Typed sequencer exposed through soc_ifc_virtual_sequencer. Keeping this path
// typed prevents virtual sequences from reaching into the endpoint driver or
// vendor memory model directly.
typedef uvm_sequencer #(soc_ifc_axi_sram_item)
  soc_ifc_axi_sram_sequencer;
