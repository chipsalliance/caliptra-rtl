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

// Defines the sequence-side control operations for the streaming recovery
// endpoint. These operations configure or inspect the testbench model; they
// are not AXI commands. Loaded data is consumed independently by reads through
// the Avery recovery subordinate.
typedef enum int {
  RECOVERY_FIFO_LOAD_IMAGE,
  RECOVERY_FIFO_CLEAR,
  RECOVERY_FIFO_QUERY
} soc_ifc_recovery_fifo_operation_e;

// Carries one recovery command from a virtual sequence to the recovery driver.
// A load transfers a complete test image plus the model's staging block size.
// A query response distinguishes the finite AXI-visible FIFO from all image
// data still held in either the front FIFO or the backing queue.
class soc_ifc_recovery_fifo_item extends uvm_sequence_item;

  `uvm_object_utils(soc_ifc_recovery_fifo_item)

  soc_ifc_recovery_fifo_operation_e operation; // Model command to execute.
  bit [31:0] payload[];                        // Complete load-image contents.
  int unsigned block_size_bytes;               // Model staging granularity.
  int unsigned front_fifo_dwords_available; // Currently visible to AXI.
  int unsigned image_dwords_remaining;      // Front FIFO plus backing image.
  bit recovery_data_avail;
  bit empty;

  // Construct a recovery FIFO item.
  function new(string name = "soc_ifc_recovery_fifo_item");
    super.new(name);
  endfunction

endclass

// Typed control sequencer exported through soc_ifc_virtual_sequencer. AXI data
// movement remains passive from the sequence's perspective and occurs when an
// AXI manager reads the separately registered Avery FIFO.
typedef uvm_sequencer #(soc_ifc_recovery_fifo_item)
  soc_ifc_recovery_fifo_sequencer;
