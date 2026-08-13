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

// One recovery agent operation. Load requests carry a complete image and
// byte-based DMA block size; query responses report both storage levels.
typedef enum int {
  RECOVERY_FIFO_LOAD_IMAGE,
  RECOVERY_FIFO_CLEAR,
  RECOVERY_FIFO_QUERY
} soc_ifc_recovery_fifo_operation_e;

// Carries one recovery command and its resulting FIFO state.
class soc_ifc_recovery_fifo_item extends uvm_sequence_item;

  `uvm_object_utils(soc_ifc_recovery_fifo_item)

  soc_ifc_recovery_fifo_operation_e operation;
  bit [31:0] payload[];
  int unsigned block_size_bytes;
  int unsigned front_fifo_dwords_available; // Currently visible to AXI.
  int unsigned image_dwords_remaining;      // Front FIFO plus backing image.
  bit recovery_data_avail;
  bit empty;

  // Construct a recovery FIFO item.
  function new(string name = "soc_ifc_recovery_fifo_item");
    super.new(name);
  endfunction

endclass

typedef uvm_sequencer #(soc_ifc_recovery_fifo_item)
  soc_ifc_recovery_fifo_sequencer;
