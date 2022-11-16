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
      ) extends uvmf_virtual_sequence_base #(.CONFIG_T(CONFIG_T));


  `uvm_object_param_utils( soc_ifc_env_bringup_sequence #(
                           CONFIG_T
                           ) );

  // Handle to the environments register model
// This handle needs to be set before use.
  soc_ifc_reg_model_top  reg_model;

// This soc_ifc_env_bringup_sequence contains a handle to a soc_ifc_env_configuration object
// named configuration.  This configuration variable contains a handle to each
// sequencer within each agent within this environment and any sub-environments.
// The configuration object handle is automatically assigned in the pre_body in the
// base class of this sequence.  The configuration handle is retrieved from the
// virtual sequencer that this sequence is started on.
// Available sequencer handles within the environment configuration:

  // Initiator agent sequencers in soc_ifc_environment:
    // configuration.soc_ifc_ctrl_agent_config.sequencer

  // Responder agent sequencers in soc_ifc_environment:
    // configuration.soc_ifc_status_agent_config.sequencer


    typedef soc_ifc_ctrl_poweron_sequence soc_ifc_ctrl_agent_poweron_sequence_t;
    soc_ifc_ctrl_agent_poweron_sequence_t soc_ifc_ctrl_agent_poweron_seq;

    typedef soc_ifc_status_responder_sequence soc_ifc_status_agent_responder_sequence_t;
    soc_ifc_status_agent_responder_sequence_t soc_ifc_status_agent_rsp_seq;





  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  function new(string name = "" );
    super.new(name);
    soc_ifc_ctrl_agent_poweron_seq = soc_ifc_ctrl_agent_poweron_sequence_t::type_id::create("soc_ifc_ctrl_agent_poweron_seq");
//    soc_ifc_status_agent_rsp_seq   = soc_ifc_status_agent_responder_sequence_t::type_id::create("soc_ifc_status_agent_rsp_seq");


  endfunction

  virtual task body();

    int sts_rsp_count = 0;
    bit sts_uc_rst_asserted = 1'b1;
    bit fuse_ready = 1'b0;
    uvm_status_e sts;
    reg_model = configuration.soc_ifc_rm;

//    if ( configuration.soc_ifc_status_agent_config.sequencer != null )
//        soc_ifc_status_agent_rsp_seq.start(configuration.soc_ifc_status_agent_config.sequencer);
    if (soc_ifc_status_agent_rsp_seq == null)
        `uvm_error("SOC_IFC_BRINGUP", "SOC_IFC ENV bringup sequence expected a handle to the status agent responder sequence (from soc_ifc_rand_test_sequence) but got null!")
    fork
        forever begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none
    // Apply power, deassert resets to poweron the SOC_IFC
    if ( configuration.soc_ifc_ctrl_agent_config.sequencer != null )
        soc_ifc_ctrl_agent_poweron_seq.start(configuration.soc_ifc_ctrl_agent_config.sequencer);
       //repeat (25) soc_ifc_ctrl_agent_poweron_seq.start(configuration.soc_ifc_ctrl_agent_config.sequencer);

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

    // TODO set fuses
    // Set Fuse Done
    reg_model.soc_ifc_reg_rm.fuse_done.write(sts, `UVM_REG_DATA_WIDTH'(1), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    `uvm_info("SOC_IFC_BRINGUP", $sformatf("Fuse download completed, status: %p", sts), UVM_MEDIUM)

    // Wait for system reset to be deasserted by SOC_IFC
    while(sts_uc_rst_asserted) begin
        wait(sts_rsp_count > 0);
        `uvm_info("SOC_IFC_BRINGUP", "Parsing a status interface response", UVM_MEDIUM)
        if (sts_rsp_count > 1) `uvm_error("SOC_IFC_BRINGUP", "Unexpected response activity during power on sequence")
        if (!soc_ifc_status_agent_rsp_seq.rsp.uc_rst_asserted) begin
            sts_uc_rst_asserted = 1'b0;
            sts_rsp_count--;
        end
    end
    `uvm_info("SOC_IFC_BRINGUP", "Mailbox completed poweron and observed reset deassertion to system", UVM_LOW)


  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

