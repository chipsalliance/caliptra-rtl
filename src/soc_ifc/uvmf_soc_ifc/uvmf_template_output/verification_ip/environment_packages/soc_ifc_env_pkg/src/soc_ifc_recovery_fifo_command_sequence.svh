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

// Converts one recovery operation into a sequencer/driver exchange. Query
// responses distinguish AXI-visible front-FIFO occupancy from total image data
// remaining across both storage levels.
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

  // Send one recovery command and copy the response state to the sequence.
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
    front_fifo_dwords_available =
      response.front_fifo_dwords_available;
    image_dwords_remaining = response.image_dwords_remaining;
    recovery_data_avail = response.recovery_data_avail;
    empty = response.empty;
  endtask

endclass
