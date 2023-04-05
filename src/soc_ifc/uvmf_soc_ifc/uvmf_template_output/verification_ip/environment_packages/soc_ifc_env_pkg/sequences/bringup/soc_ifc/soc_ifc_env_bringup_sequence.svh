//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: Bringup sequence for the SOC_IFC environment
//              (essentially just a cold-reset sequence)
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_bringup_sequence extends soc_ifc_env_reset_sequence_base;


  `uvm_object_utils( soc_ifc_env_bringup_sequence )

  typedef soc_ifc_ctrl_poweron_sequence soc_ifc_ctrl_agent_poweron_sequence_t;

  constraint always_set_uds_c { this.fuses_to_set.uds == 1'b1; }
  constraint always_set_fe_c  { this.fuses_to_set.field_entropy == 1'b1; }

  function new(string name = "" );
    uvm_object obj;
    super.new(name);
    obj = soc_ifc_ctrl_agent_poweron_sequence_t::get_type().create_object("soc_ifc_ctrl_agent_poweron_seq");
    if (!$cast(soc_ifc_ctrl_seq,obj))
        `uvm_fatal("SOC_IFC_BRINGUP", "Failed to cast object as poweron sequence!")
  endfunction

endclass
