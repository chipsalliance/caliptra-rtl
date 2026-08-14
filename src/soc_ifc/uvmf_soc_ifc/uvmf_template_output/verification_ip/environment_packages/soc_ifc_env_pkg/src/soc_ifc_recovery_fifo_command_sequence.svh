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

// Provides the virtual-sequence API for preparing and inspecting streaming
// recovery data. A parent sequence fills these public fields and starts this
// sequence on vsqr.recovery_fifo_sequencer. The driver then updates the
// agent-owned model; actual image consumption occurs separately when the DUT
// reads the recovery subordinate and is observed through its AXI callbacks.
class soc_ifc_recovery_fifo_command_sequence
  extends uvm_sequence #(soc_ifc_recovery_fifo_item);

  `uvm_object_utils(soc_ifc_recovery_fifo_command_sequence)

  soc_ifc_recovery_fifo_operation_e operation;
  bit [31:0] payload[];
  int unsigned block_size_bytes;
  int unsigned front_fifo_dwords_available;
  int unsigned image_dwords_remaining;
  bit recovery_data_avail;
  bit empty;

  // Construct a recovery FIFO command sequence.
  function new(string name = "soc_ifc_recovery_fifo_command_sequence");
    super.new(name);
  endfunction

  // Send one model command and wait for completion. The response is useful for
  // all operations because it establishes ordering with the driver's model
  // update; query operations additionally return externally useful state. This
  // avoids virtual-sequence reads of model internals and keeps Avery-specific
  // storage behind the recovery agent boundary.
  virtual task body();
    soc_ifc_recovery_fifo_item request;
    soc_ifc_recovery_fifo_item response;
    request = soc_ifc_recovery_fifo_item::type_id::create("request");
    start_item(request);
    request.operation = operation;
    request.payload = payload;
    request.block_size_bytes = block_size_bytes;
    if (operation == RECOVERY_FIFO_LOAD_IMAGE)
      `uvm_info("RECOVERY_FIFO_SEQ",
        $sformatf(
          "Loading recovery image with %0d DWORDs and %0d-byte blocks",
          payload.size(), block_size_bytes), UVM_LOW)
    else if (operation == RECOVERY_FIFO_CLEAR)
      `uvm_info("RECOVERY_FIFO_SEQ",
        "Clearing recovery image state", UVM_LOW)
    finish_item(request);
    get_response(response);
    // Publish both storage views because "front FIFO empty" can be true while
    // a larger image still has data waiting for a delayed refill.
    front_fifo_dwords_available =
      response.front_fifo_dwords_available;
    image_dwords_remaining = response.image_dwords_remaining;
    recovery_data_avail = response.recovery_data_avail;
    empty = response.empty;
  endtask

endclass
