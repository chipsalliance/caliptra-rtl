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

// Provides the typed coordination point for environment-level virtual
// sequences. The handles alias sequencers owned by agent components; this
// component does not construct, wrap, drive, or take ownership of them.
class soc_ifc_virtual_sequencer
  extends uvmf_virtual_sequencer_base #(
    .CONFIG_T(soc_ifc_env_configuration)
  );

  `uvm_component_utils(soc_ifc_virtual_sequencer)

  aaxi_sequencer soc_axi_sequencer;
  soc_ifc_axi_sram_sequencer axi_sram_sequencer;
  soc_ifc_recovery_fifo_sequencer recovery_fifo_sequencer;

  // Construct the virtual coordination point.
  function new(string name = "soc_ifc_virtual_sequencer",
               uvm_component parent = null);
    super.new(name, parent);
  endfunction

endclass
