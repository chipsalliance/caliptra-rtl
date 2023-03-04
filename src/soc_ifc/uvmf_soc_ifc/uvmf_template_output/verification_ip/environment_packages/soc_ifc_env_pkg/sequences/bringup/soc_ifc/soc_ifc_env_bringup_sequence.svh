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
class soc_ifc_env_bringup_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


  `uvm_object_utils( soc_ifc_env_bringup_sequence )

    typedef soc_ifc_ctrl_poweron_sequence soc_ifc_ctrl_agent_poweron_sequence_t;
    soc_ifc_ctrl_agent_poweron_sequence_t soc_ifc_ctrl_agent_poweron_seq;





  // pragma uvmf custom class_item_additional begin
  rand uvm_reg_data_t uds_seed_rand      [12];
  rand uvm_reg_data_t field_entropy_rand [32];
  rand struct packed {
    bit uds;
    bit field_entropy;
  } fuses_to_set;

  constraint always_set_uds_c { this.fuses_to_set.uds == 1'b1; }
  constraint always_set_fe_c  { this.fuses_to_set.field_entropy == 1'b1; }
  // pragma uvmf custom class_item_additional end

  function new(string name = "" );
    super.new(name);
    soc_ifc_ctrl_agent_poweron_seq = soc_ifc_ctrl_agent_poweron_sequence_t::type_id::create("soc_ifc_ctrl_agent_poweron_seq");

  endfunction

  virtual task body();

    int sts_rsp_count = 0;
    bit fuse_ready = 1'b0;
    bit set_bootfsm_breakpoint;
    uvm_status_e sts;
    reg_model = configuration.soc_ifc_rm;

    if (soc_ifc_status_agent_rsp_seq == null)
        `uvm_fatal("SOC_IFC_BRINGUP", "SOC_IFC ENV bringup sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")
    fork
        forever begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    // Apply power, deassert resets to poweron the SOC_IFC
    if ( configuration.soc_ifc_ctrl_agent_config.sequencer != null )
        soc_ifc_ctrl_agent_poweron_seq.start(configuration.soc_ifc_ctrl_agent_config.sequencer);
    else
        `uvm_error("SOC_IFC_BRINGUP", "soc_ifc_ctrl_agent_config.sequencer is null!")
    set_bootfsm_breakpoint = soc_ifc_ctrl_agent_poweron_seq.set_bootfsm_breakpoint;

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
    if (this.fuses_to_set.uds) begin
        `uvm_info("SOC_IFC_BRINGUP", "Writing obfuscated UDS to fuse bank", UVM_LOW)
        for (int ii = 0; ii < $size(reg_model.soc_ifc_reg_rm.fuse_uds_seed); ii++) begin
            reg_model.soc_ifc_reg_rm.fuse_uds_seed[ii].write(sts, uds_seed_rand[ii], UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
            assert(sts == UVM_IS_OK) else `uvm_error("SOC_IFC_BRINGUP", $sformatf("Failed when writing to fuse_uds_seed index %d", ii))
        end
    end

    // Write FE
    if (this.fuses_to_set.field_entropy) begin
        `uvm_info("SOC_IFC_BRINGUP", "Writing obfuscated Field Entropy to fuse bank", UVM_LOW)
        for (int ii = 0; ii < $size(reg_model.soc_ifc_reg_rm.fuse_field_entropy); ii++) begin
            reg_model.soc_ifc_reg_rm.fuse_field_entropy[ii].write(sts, field_entropy_rand[ii], UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
            assert(sts == UVM_IS_OK) else `uvm_error("SOC_IFC_BRINGUP", $sformatf("Failed when writing to field_entropy index %d", ii))
        end
    end

    // Set Fuse Done
    reg_model.soc_ifc_reg_rm.CPTRA_FUSE_WR_DONE.write(sts, `UVM_REG_DATA_WIDTH'(1), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    `uvm_info("SOC_IFC_BRINGUP", $sformatf("Fuse download completed, status: %p", sts), UVM_MEDIUM)

    // If set_bootfsm_breakpoint is randomized to 1, we need to release bootfsm by writing GO
    if (set_bootfsm_breakpoint) begin
        `uvm_info("SOC_IFC_BRINGUP", "BootFSM Breakpoint is set, writing GO", UVM_MEDIUM)
        reg_model.soc_ifc_reg_rm.CPTRA_BOOTFSM_GO.write(sts, `UVM_REG_DATA_WIDTH'(1), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        `uvm_info("SOC_IFC_BRINGUP", $sformatf("Write to BootFSM GO completed, status: %p", sts), UVM_MEDIUM)
    end
    else begin
        `uvm_info("SOC_IFC_BRINGUP", "BootFSM Breakpoint not set, bringup sequence complete", UVM_MEDIUM)
    end


  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

