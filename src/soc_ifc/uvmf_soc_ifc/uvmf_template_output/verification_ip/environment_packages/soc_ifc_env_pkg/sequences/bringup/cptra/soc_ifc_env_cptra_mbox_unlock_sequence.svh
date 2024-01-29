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
// DESCRIPTION: Sequence to initialize Caliptra SOC_IFC interrupts
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_cptra_mbox_unlock_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


  `uvm_object_utils( soc_ifc_env_cptra_mbox_unlock_sequence );


  uvm_status_e reg_sts;

  function new(string name = "" );
    super.new(name);

  endfunction

  virtual task body();

    uvm_reg_data_t data;
    int sts_rsp_count = 0;
    reg_model = configuration.soc_ifc_rm;

    if (cptra_status_agent_rsp_seq == null)
        `uvm_fatal("CPTRA_MBOX_UNLOCK", "SOC_IFC ENV caliptra mailbox unlock sequence expected a handle to the cptra status agent responder sequence (from bench-level sequence) but got null!")
    fork
        forever begin
            @(cptra_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    // Write to mbox_unlock
    data = uvm_reg_data_t'(1) << reg_model.mbox_csr_rm.mbox_unlock.unlock.get_lsb_pos();
    reg_model.mbox_csr_rm.mbox_unlock.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("CPTRA_MBOX_UNLOCK", $sformatf("Register access failed (%s)", "mbox_unlock"))

  endtask

endclass
