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

//------------------------------------------------------------------------------
//
// CLASS: soc_ifc_reg_cov_subscriber
//
// This class provides an analysis export for receiving transactions from a
// connected analysis export. Making such a connection "subscribes" this
// component to any transactions emitted by the connected analysis port.
//
// This extended class provides a coverage subscriber that receives uvm_reg_item
// objects exported from the uvm_reg_predictor and calls the sample_values 
// function for the associated register.
//------------------------------------------------------------------------------

class soc_ifc_reg_cov_subscriber #(
  type CONFIG_T,
  type T=uvm_reg_item,
  type BASE_T = uvm_subscriber #(T)
  )
 extends BASE_T;

  typedef soc_ifc_reg_cov_subscriber #( CONFIG_T, T, BASE_T) this_type;

  // Factory registration of this class
  `uvm_component_param_utils( this_type )

  CONFIG_T configuration;

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  
 virtual function void write(T t);
    uvm_object obj;
    uvm_reg axs_reg;
    obj = t.element;
    if (t.element_kind == UVM_REG)
        $cast(axs_reg,obj);
    else
        `uvm_fatal("SOC_IFC_REG_COV_SUB", "Bad object type in received item")
    `uvm_info("SOC_IFC_REG_COV_SUB", $sformatf("Received reg item accessing reg %s for coverage sampling", axs_reg.get_full_name()), UVM_FULL)
    axs_reg.sample_values();
 endfunction

endclass
