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

// Converts one virtual-sequence SRAM request into a sequencer/driver exchange.
// The response path is used for reads and writes so agent completion is
// serialized before the calling virtual sequence continues.
class soc_ifc_axi_sram_access_sequence
  extends uvm_sequence #(soc_ifc_axi_sram_item);

  `uvm_object_utils(soc_ifc_axi_sram_access_sequence)

  soc_ifc_axi_sram_operation_e operation;
  longint unsigned offset;
  bit [31:0] data;

  // Construct an SRAM access sequence.
  function new(string name = "soc_ifc_axi_sram_access_sequence");
    super.new(name);
  endfunction

  // Send one SRAM request and return the response data.
  virtual task body();
    soc_ifc_axi_sram_item request;
    soc_ifc_axi_sram_item response;
    request = soc_ifc_axi_sram_item::type_id::create("request");
    start_item(request);
    request.operation = operation;
    request.offset = offset;
    request.data = data;
    finish_item(request);
    get_response(response);
    data = response.data;
  endtask

endclass
