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
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_bringup_sequence #(
      type CONFIG_T
      ) extends soc_ifc_env_sequence_base #(.CONFIG_T(CONFIG_T));


  `uvm_object_param_utils( soc_ifc_env_bringup_sequence #(
                           CONFIG_T
                           ) );

    typedef soc_ifc_ctrl_poweron_sequence soc_ifc_ctrl_agent_poweron_sequence_t;
    soc_ifc_ctrl_agent_poweron_sequence_t soc_ifc_ctrl_agent_poweron_seq;

    typedef soc_ifc_status_responder_sequence  soc_ifc_status_agent_responder_seq_t;
    soc_ifc_status_agent_responder_seq_t soc_ifc_status_agent_rsp_seq;





  // pragma uvmf custom class_item_additional begin
  rand uvm_reg_data_t uds_seed_rand      [12];
  rand uvm_reg_data_t field_entropy_rand [32];
  // pragma uvmf custom class_item_additional end

  function new(string name = "" );
    super.new(name);
    soc_ifc_ctrl_agent_poweron_seq = soc_ifc_ctrl_agent_poweron_sequence_t::type_id::create("soc_ifc_ctrl_agent_poweron_seq");
    assert(this.randomize()) else `uvm_error("SOC_IFC_BRINGUP", "Failed to randomize CTRL poweron sequence");


  endfunction

  virtual task body();

    int sts_rsp_count = 0;
    bit fuse_ready = 1'b0;
    uvm_status_e sts;
    reg_model = configuration.soc_ifc_rm;

    if (soc_ifc_status_agent_rsp_seq == null)
        `uvm_error("SOC_IFC_BRINGUP", "SOC_IFC ENV bringup sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")
    fork
        forever begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    // Apply power, deassert resets to poweron the SOC_IFC
    if ( configuration.soc_ifc_ctrl_agent_config.sequencer != null )
        soc_ifc_ctrl_agent_poweron_seq.start(configuration.soc_ifc_ctrl_agent_config.sequencer);

    // Download Fuses when ready
    wait(sts_rsp_count > 0);
    `uvm_info("SOC_IFC_BRINGUP", "Received response from status agent", UVM_MEDIUM)
    if (sts_rsp_count > 1)
        `uvm_error("SOC_IFC_BRINGUP", "Missed response activity during power on sequence")
    fuse_ready = soc_ifc_status_agent_rsp_seq.rsp.ready_for_fuses;
    sts_rsp_count--;
    if (!fuse_ready)
        `uvm_error("SOC_IFC_BRINGUP", "Unexpected status transition while waiting for Mailbox readiness for fuses")
    else
        `uvm_info("SOC_IFC_BRINGUP", "Fuse ready, initiating fuse download", UVM_LOW)

    // Write UDS
    `uvm_info("SOC_IFC_BRINGUP", "Writing obfuscated UDS to fuse bank", UVM_LOW)
    for (int ii = 0; ii < $size(reg_model.soc_ifc_reg_rm.uds_seed); ii++) begin
        reg_model.soc_ifc_reg_rm.uds_seed[ii].write(sts, uds_seed_rand[ii], UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        assert(sts == UVM_IS_OK) else `uvm_error("SOC_IFC_BRINGUP", $sformatf("Failed when writing to uds_seed index %d", ii))
    end

    // Write FE
    `uvm_info("SOC_IFC_BRINGUP", "Writing obfuscated Field Entropy to fuse bank", UVM_LOW)
    for (int ii = 0; ii < $size(reg_model.soc_ifc_reg_rm.field_entropy); ii++) begin
        reg_model.soc_ifc_reg_rm.field_entropy[ii].write(sts, field_entropy_rand[ii], UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        assert(sts == UVM_IS_OK) else `uvm_error("SOC_IFC_BRINGUP", $sformatf("Failed when writing to field_entropy index %d", ii))
    end

    // Set Fuse Done
    reg_model.soc_ifc_reg_rm.fuse_done.write(sts, `UVM_REG_DATA_WIDTH'(1), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    `uvm_info("SOC_IFC_BRINGUP", $sformatf("Fuse download completed, status: %p", sts), UVM_MEDIUM)


  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

