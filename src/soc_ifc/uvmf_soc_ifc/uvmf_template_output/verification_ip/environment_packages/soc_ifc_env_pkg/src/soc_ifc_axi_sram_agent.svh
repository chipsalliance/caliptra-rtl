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

// Owns the SRAM sequencer/driver pair and direct Avery memory binding.
class soc_ifc_axi_sram_agent extends uvm_agent;

  `uvm_component_utils(soc_ifc_axi_sram_agent)

  soc_ifc_axi_sram_config configuration;
  soc_ifc_axi_sram_sequencer sequencer;
  soc_ifc_axi_sram_driver driver;
  soc_ifc_axi_response_delay_callback delay_callback;

  // Construct the SRAM endpoint agent.
  function new(string name = "soc_ifc_axi_sram_agent",
               uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Assign the SRAM geometry and delay policy.
  function void set_config(soc_ifc_axi_sram_config configuration);
    this.configuration = configuration;
  endfunction

  // Construct the active item path and delay callback. The Avery memory object
  // is not available until environment connect_phase.
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (configuration == null)
      `uvm_fatal("AXI_SRAM", "SRAM agent configuration is null")
    sequencer =
      soc_ifc_axi_sram_sequencer::type_id::create("sequencer", this);
    driver = soc_ifc_axi_sram_driver::type_id::create("driver", this);
    driver.configure(configuration.base_addr,
                     configuration.limit_addr,
                     configuration.word_bytes);
    delay_callback =
      soc_ifc_axi_response_delay_callback::type_id::create(
        "delay_callback");
    delay_callback.b_delay = configuration.b_delay;
    delay_callback.r_delay = configuration.r_delay;
  endfunction

  // Connect the standard sequencer/driver request path. Items block until the
  // driver returns item_done(response), guaranteeing preload/readback ordering.
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
  endfunction

  // Attach the driver to the Avery SRAM subordinate. The memory object services
  // both direct agent operations and later DUT AXI accesses.
  function void bind_bfm(aaxi_device_class bfm);
    if (bfm == null)
      `uvm_fatal("AXI_SRAM", "Cannot bind a null Avery SRAM BFM")
    if (bfm.mem_obj == null)
      bfm.mem_obj = new("soc_ifc_external_memory");
    driver.bind_memory(bfm.mem_obj);
    `uvm_info("AXI_SRAM",
      $sformatf("Bound SRAM endpoint at [0x%0h:0x%0h]",
                configuration.base_addr,
                configuration.limit_addr), UVM_LOW)
  endfunction

endclass
