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
// DESCRIPTION: As part of soc_ifc environment bringup, initialize
//              valid_users by writing to 
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_pauser_init_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


  `uvm_object_utils( soc_ifc_env_pauser_init_sequence )


  // pragma uvmf custom class_item_additional begin
  caliptra_apb_user apb_user_obj;

  rand bit [apb5_master_0_params::PAUSER_WIDTH-1:0] mbox_valid_users [5] = '{default: '1};

  constraint unique_valid_pauser_c { unique {mbox_valid_users}; }
  // pragma uvmf custom class_item_additional end

  function new(string name = "" );
    super.new(name);

    // Setup a User object to override PAUSER
    apb_user_obj = new();

  endfunction


  //==========================================
  // Name:        pre_body
  // Description: Setup tasks to:
  //               - get a reg model handle
  //               - check for a valid responder handle
  //==========================================
  virtual task pre_body();
    super.pre_body();
    reg_model = configuration.soc_ifc_rm;
    if (soc_ifc_status_agent_rsp_seq == null)
        `uvm_fatal("SOC_IFC_PAUSER_INIT", "SOC_IFC ENV bringup sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")
    apb_user_obj.set_addr_user(reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[0].PAUSER.get_reset("HARD")); // FIXME use param?
  endtask


  //==========================================
  // Name:        body
  // Description: Run the main functionality
  //==========================================
  virtual task body();

    int sts_rsp_count = 0;
    byte ii;
    uvm_status_e sts;

    fork
        forever begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    `uvm_info("SOC_IFC_PAUSER_INIT", "Configuring valid users in soc_ifc", UVM_MEDIUM)
    for (ii=0; ii < $size(reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER); ii++) begin: VALID_USER_LOOP
        reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[ii].write(sts, mbox_valid_users[ii], UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
        if (sts != UVM_IS_OK) `uvm_error("SOC_IFC_PAUSER_INIT", $sformatf("Failed when writing to CPTRA_MBOX_VALID_PAUSER index %0d", ii))
    end
    `uvm_info("SOC_IFC_PAUSER_INIT", "Locking valid users in soc_ifc", UVM_MEDIUM)
    for (ii=0; ii < $size(reg_model.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK); ii++) begin: USER_LOCK_LOOP
        if (reg_model.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[ii].LOCK.get_mirrored_value())
            `uvm_warning("SOC_IFC_PAUSER_INIT", "Found CPTRA_MBOX_PAUSER_LOCK that is already set while running PAUSER init sequence!")
        else begin
            reg_model.soc_ifc_reg_rm.CPTRA_MBOX_PAUSER_LOCK[ii].write(sts, `UVM_REG_DATA_WIDTH'(1), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
            if (sts != UVM_IS_OK) `uvm_error("SOC_IFC_PAUSER_INIT", $sformatf("Failed when writing to CPTRA_MBOX_PAUSER_LOCK index %0d", ii))
        end
    end
    `uvm_info("SOC_IFC_PAUSER_INIT", "Completed VALID PAUSER setup and lock", UVM_MEDIUM)
    `uvm_info("SOC_IFC_PAUSER_INIT", $sformatf("Valid PAUSER: %p", mbox_valid_users), UVM_MEDIUM)

  endtask

endclass
