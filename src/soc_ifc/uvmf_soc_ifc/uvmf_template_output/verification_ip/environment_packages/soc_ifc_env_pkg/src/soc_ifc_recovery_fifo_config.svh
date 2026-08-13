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

// Configures the finite AXI-facing FIFO and its response/refill timing.
// `depth_dwords` describes only staged data visible to AXI; complete recovery
// images are held separately by the agent-owned backing queue.
class soc_ifc_recovery_fifo_config extends uvm_object;

  `uvm_object_utils(soc_ifc_recovery_fifo_config)

  virtual soc_ifc_recovery_if vif;
  aaxi_addr_t fifo_data_addr;
  // This depth limits staged AXI data. Supported recovery blocks are separately
  // capped at 64 bytes; complete images are held by the backing queue.
  int unsigned depth_dwords;
  soc_ifc_axi_delay_range r_delay;
  soc_ifc_axi_delay_range refill_delay;

  // Construct recovery FIFO geometry and mutable delay policies.
  function new(string name = "soc_ifc_recovery_fifo_config");
    super.new(name);
    r_delay = soc_ifc_axi_delay_range::type_id::create("r_delay");
    refill_delay =
      soc_ifc_axi_delay_range::type_id::create("refill_delay");
  endfunction

  // Initialize physical front-FIFO geometry and startup timing before the
  // agent is built. The complete image backing queue needs no size setting.
  function void configure(input virtual soc_ifc_recovery_if vif,
                          input aaxi_addr_t fifo_data_addr,
                          input int unsigned depth_dwords,
                          input int unsigned r_delay_min,
                          input int unsigned r_delay_max,
                          input int unsigned refill_delay_min,
                          input int unsigned refill_delay_max);
    if (vif == null)
      `uvm_fatal("RECOVERY_FIFO_CFG", "Recovery virtual interface is null")
    if (depth_dwords == 0)
      `uvm_fatal("RECOVERY_FIFO_CFG", "Recovery FIFO depth must be nonzero")
    this.vif = vif;
    this.fifo_data_addr = fifo_data_addr;
    this.depth_dwords = depth_dwords;
    r_delay.configure(r_delay_min, r_delay_max);
    refill_delay.configure(refill_delay_min, refill_delay_max);
  endfunction

  // Update the R-response delay policy used by future reads.
  function void set_r_response_delay(input int unsigned min_cycles,
                                     input int unsigned max_cycles);
    r_delay.set_range(min_cycles, max_cycles);
  endfunction

  // Update the refill delay selected after the front FIFO drains.
  function void set_refill_delay(input int unsigned min_cycles,
                                 input int unsigned max_cycles);
    refill_delay.set_range(min_cycles, max_cycles);
  endfunction

endclass
