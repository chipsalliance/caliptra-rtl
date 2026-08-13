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

// One SRAM word operation exchanged between a sequence and the SRAM agent.
// Read data returns in the response item; writes use the same response handshake
// so the calling sequence waits for the memory update to complete.
typedef enum int {
  AXI_SRAM_WRITE,
  AXI_SRAM_READ
} soc_ifc_axi_sram_operation_e;

// Carries one direct SRAM read or write between the access sequence and driver.
class soc_ifc_axi_sram_item extends uvm_sequence_item;

  `uvm_object_utils(soc_ifc_axi_sram_item)

  soc_ifc_axi_sram_operation_e operation;
  longint unsigned offset;
  bit [31:0] data;

  // Construct an SRAM item.
  function new(string name = "soc_ifc_axi_sram_item");
    super.new(name);
  endfunction

endclass

typedef uvm_sequencer #(soc_ifc_axi_sram_item)
  soc_ifc_axi_sram_sequencer;
