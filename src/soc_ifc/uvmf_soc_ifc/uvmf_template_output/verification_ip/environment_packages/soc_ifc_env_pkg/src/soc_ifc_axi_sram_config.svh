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

// Carries declarative SRAM geometry and response policies.
// Delay objects are intentionally shared with callbacks so runtime setters can
// change future transactions without recreating agent components.
class soc_ifc_axi_sram_config extends uvm_object;

  `uvm_object_utils(soc_ifc_axi_sram_config)

  aaxi_addr_t base_addr;
  aaxi_addr_t limit_addr;
  int unsigned word_bytes;
  soc_ifc_axi_delay_range b_delay;
  soc_ifc_axi_delay_range r_delay;

  // Construct SRAM geometry and mutable response-delay policies.
  function new(string name = "soc_ifc_axi_sram_config");
    super.new(name);
    b_delay = soc_ifc_axi_delay_range::type_id::create("b_delay");
    r_delay = soc_ifc_axi_delay_range::type_id::create("r_delay");
  endfunction

  // Initialize geometry and startup delays before the agent build phase.
  // Runtime tests subsequently modify only the shared delay-range objects.
  function void configure(input aaxi_addr_t base_addr,
                          input aaxi_addr_t limit_addr,
                          input int unsigned word_bytes,
                          input int unsigned b_delay_min,
                          input int unsigned b_delay_max,
                          input int unsigned r_delay_min,
                          input int unsigned r_delay_max);
    if (limit_addr < base_addr)
      `uvm_fatal("AXI_SRAM_CFG", "SRAM address limit is below base")
    if ((longint'(limit_addr - base_addr) + 1) < 4)
      `uvm_fatal("AXI_SRAM_CFG", "SRAM window is smaller than one DWORD")
    if (word_bytes == 0 || (word_bytes % 4) != 0)
      `uvm_fatal("AXI_SRAM_CFG",
        "SRAM word width must be a nonzero DWORD multiple")
    this.base_addr = base_addr;
    this.limit_addr = limit_addr;
    this.word_bytes = word_bytes;
    b_delay.configure(b_delay_min, b_delay_max);
    r_delay.configure(r_delay_min, r_delay_max);
  endfunction

  // Update the B-response delay policy used by future writes.
  function void set_b_response_delay(input int unsigned min_cycles,
                                     input int unsigned max_cycles);
    b_delay.set_range(min_cycles, max_cycles);
  endfunction

  // Update the R-response delay policy used by future reads.
  function void set_r_response_delay(input int unsigned min_cycles,
                                     input int unsigned max_cycles);
    r_delay.set_range(min_cycles, max_cycles);
  endfunction

endclass
