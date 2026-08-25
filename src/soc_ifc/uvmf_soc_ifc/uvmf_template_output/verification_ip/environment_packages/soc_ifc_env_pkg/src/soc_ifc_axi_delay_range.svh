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

// Holds a mutable cycle-delay policy shared by endpoint configuration,
// callbacks, and runtime setters. Equal bounds select a fixed delay; unequal
// bounds select a new constrained value for each callback request.
class soc_ifc_axi_delay_range extends uvm_object;

  `uvm_object_utils(soc_ifc_axi_delay_range)

  int unsigned min_cycles;
  int unsigned max_cycles;
  rand int unsigned selected_cycles;

  constraint selected_cycles_c {
    selected_cycles inside {[min_cycles:max_cycles]};
  }

  // Construct a delay policy.
  function new(string name = "soc_ifc_axi_delay_range");
    super.new(name);
  endfunction

  // Initialize the delay bounds.
  function void configure(input int unsigned min_cycles,
                          input int unsigned max_cycles);
    set_range(min_cycles, max_cycles);
  endfunction

  // Replace the delay bounds after validating their order.
  function void set_range(input int unsigned min_cycles,
                          input int unsigned max_cycles);
    if (min_cycles > max_cycles)
      `uvm_fatal("AXI_DELAY_CFG",
        $sformatf("Delay minimum %0d exceeds maximum %0d",
                  min_cycles, max_cycles))
    this.min_cycles = min_cycles;
    this.max_cycles = max_cycles;
  endfunction

  // Return the fixed value without invoking the solver. For a range, randomize
  // on every call so successive protocol responses vary independently.
  function int unsigned next_delay();
    if (min_cycles == max_cycles)
      return min_cycles;
    if (!randomize())
      `uvm_fatal("AXI_DELAY_CFG",
        $sformatf("Failed to randomize delay in range [%0d:%0d]",
                  min_cycles, max_cycles))
    return selected_cycles;
  endfunction

endclass
