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

// Provides the sequence API for direct access to the external SRAM endpoint.
// It is designed to run on vsqr.axi_sram_sequencer after a parent sequence sets
// operation, offset, and data. The corresponding driver accesses the endpoint's
// shared Avery memory, providing a non-AXI path for initialization or inspection.
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

  // Convert the public sequence fields into one request and wait for the
  // driver response. set_id_info() in the driver associates that response with
  // this request, allowing get_response() to retrieve the matching completion.
  // Copying response.data back into data gives callers one API for both writes
  // and reads; write responses simply preserve completion ordering.
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
