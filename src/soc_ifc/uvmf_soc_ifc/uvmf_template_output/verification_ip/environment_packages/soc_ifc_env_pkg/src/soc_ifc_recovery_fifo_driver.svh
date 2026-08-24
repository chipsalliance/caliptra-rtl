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

// Implements the control plane for the recovery endpoint. Virtual sequences
// send load, clear, and query items through this driver, while AXI read traffic
// reaches the same model through Avery callbacks and the agent's run_phase.
// Routing commands here keeps queue mutation out of virtual sequences and keeps
// those sequences independent of vendor FIFO internals.
class soc_ifc_recovery_fifo_driver
  extends uvm_driver #(soc_ifc_recovery_fifo_item);

  `uvm_component_utils(soc_ifc_recovery_fifo_driver)

  soc_ifc_recovery_fifo_model model;

  // Construct the recovery command driver.
  function new(string name = "soc_ifc_recovery_fifo_driver",
               uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Execute control commands until UVM terminates run_phase. Every request
  // receives a response so callers know the driver completed a load or clear
  // before continuing, and query callers receive the reported model fields.
  virtual task run_phase(uvm_phase phase);
    soc_ifc_recovery_fifo_item request;
    soc_ifc_recovery_fifo_item response;
    forever begin
      seq_item_port.get_next_item(request);
      response = soc_ifc_recovery_fifo_item::type_id::create("response");
      // Preserve request routing metadata for get_response() in the originating
      // command sequence.
      response.set_id_info(request);
      response.operation = request.operation;
      // Keep operation decoding here so the model remains an agent-private
      // implementation detail and query responses return through normal UVM
      // request/response flow.
      case (request.operation)
        RECOVERY_FIFO_LOAD_IMAGE:
          model.load_image(request.payload,
                           request.block_size_bytes);
        RECOVERY_FIFO_CLEAR:
          model.clear();
        RECOVERY_FIFO_QUERY: begin
          response.front_fifo_dwords_available =
            model.front_fifo_dwords_available;
          response.image_dwords_remaining =
            model.image_dwords_remaining();
          response.recovery_data_avail =
            model.configuration.vif.recovery_data_avail;
          response.empty = model.image_complete();
        end
        default:
          `uvm_fatal("RECOVERY_FIFO",
            "Unsupported recovery agent operation")
      endcase
      seq_item_port.item_done(response);
    end
  endtask

endclass
