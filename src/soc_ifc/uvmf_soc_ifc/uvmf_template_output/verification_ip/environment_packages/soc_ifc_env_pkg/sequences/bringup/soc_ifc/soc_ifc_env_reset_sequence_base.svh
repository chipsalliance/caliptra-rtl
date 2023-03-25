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
// DESCRIPTION: Issue a reset in the soc_ifc environment
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_reset_sequence_base extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


  `uvm_object_utils( soc_ifc_env_reset_sequence_base )

    typedef soc_ifc_ctrl_reset_sequence_base soc_ifc_ctrl_sequence_t;
    soc_ifc_ctrl_sequence_t soc_ifc_ctrl_seq;


  typedef struct packed {
      bit set_bootfsm_breakpoint;
  } ctrl_reset_seq_context_t;

  rand uvm_reg_data_t uds_seed_rand      [12];
  rand uvm_reg_data_t field_entropy_rand [32];
  rand struct packed {
    bit uds;
    bit field_entropy;
  } fuses_to_set;


  //==========================================
  // Name:        new
  // Description: Constructor
  //==========================================
  function new(string name = "" );
    super.new(name);
    soc_ifc_ctrl_seq = soc_ifc_ctrl_sequence_t::type_id::create("soc_ifc_ctrl_seq");
  endfunction


  //==========================================
  // Name:        run_ctrl_reset_seq
  // Description: Run low-level soc_ifc_ctrl sequence to actually do the reset
  //==========================================
  virtual task run_ctrl_reset_seq(output ctrl_reset_seq_context_t ctx);
    if ( configuration.soc_ifc_ctrl_agent_config.sequencer != null )
        soc_ifc_ctrl_seq.start(configuration.soc_ifc_ctrl_agent_config.sequencer);
    else
        `uvm_error("SOC_IFC_RST", "soc_ifc_ctrl_agent_config.sequencer is null!")
    ctx.set_bootfsm_breakpoint = soc_ifc_ctrl_seq.set_bootfsm_breakpoint;
  endtask


  //==========================================
  // Name:        download_fuses
  // Description: Task to re-set the fuses after reset deasserts
  //              This is more of a bringup task than an integral part of reset
  //==========================================
  virtual task download_fuses();
    uvm_status_e sts;
    bit fuse_ready = 1'b0;
    int sts_rsp_count = 0;

    fork
        forever begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    wait(sts_rsp_count > 0);
    `uvm_info("SOC_IFC_RST", "Received response from status agent", UVM_MEDIUM)
    if (sts_rsp_count > 1)
        `uvm_error("SOC_IFC_RST", "Missed response activity during reset sequence")
    fuse_ready = soc_ifc_status_agent_rsp_seq.rsp.ready_for_fuses;
    sts_rsp_count--;
    if (!fuse_ready)
        `uvm_error("SOC_IFC_RST", "Unexpected status transition while waiting for Mailbox readiness for fuses")
    else
        `uvm_info("SOC_IFC_RST", "Fuse ready, initiating fuse download", UVM_LOW)

    // Write UDS
    if (this.fuses_to_set.uds) begin
        `uvm_info("SOC_IFC_RST", "Writing obfuscated UDS to fuse bank", UVM_LOW)
        for (int ii = 0; ii < $size(reg_model.soc_ifc_reg_rm.fuse_uds_seed); ii++) begin
            reg_model.soc_ifc_reg_rm.fuse_uds_seed[ii].write(sts, uds_seed_rand[ii], UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
            if (sts != UVM_IS_OK) `uvm_error("SOC_IFC_RST", $sformatf("Failed when writing to fuse_uds_seed index %d", ii))
        end
    end

    // Write FE
    if (this.fuses_to_set.field_entropy) begin
        `uvm_info("SOC_IFC_RST", "Writing obfuscated Field Entropy to fuse bank", UVM_LOW)
        for (int ii = 0; ii < $size(reg_model.soc_ifc_reg_rm.fuse_field_entropy); ii++) begin
            reg_model.soc_ifc_reg_rm.fuse_field_entropy[ii].write(sts, field_entropy_rand[ii], UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
            if (sts != UVM_IS_OK) `uvm_error("SOC_IFC_RST", $sformatf("Failed when writing to field_entropy index %d", ii))
        end
    end

    // Set Fuse Done
    reg_model.soc_ifc_reg_rm.CPTRA_FUSE_WR_DONE.write(sts, `UVM_REG_DATA_WIDTH'(1), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
    `uvm_info("SOC_IFC_RST", $sformatf("Fuse download completed, status: %p", sts), UVM_MEDIUM)
  endtask


  //==========================================
  // Name:        configure_breakpoint
  // Description: Check if breakpoint was set on bringup - if so, need to
  //              set the "GO" bit to allow boot fsm to proceed
  //==========================================
  virtual task configure_breakpoint(input ctrl_reset_seq_context_t ctrl_rst_ctx);
    uvm_status_e sts;
    // If set_bootfsm_breakpoint is randomized to 1, we need to release bootfsm by writing GO
    if (ctrl_rst_ctx.set_bootfsm_breakpoint) begin
        `uvm_info("SOC_IFC_RST", "BootFSM Breakpoint is set, writing GO", UVM_MEDIUM)
        reg_model.soc_ifc_reg_rm.CPTRA_BOOTFSM_GO.write(sts, `UVM_REG_DATA_WIDTH'(1), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this);
        `uvm_info("SOC_IFC_RST", $sformatf("Write to BootFSM GO completed, status: %p", sts), UVM_MEDIUM)
    end
    else begin
        `uvm_info("SOC_IFC_RST", "BootFSM Breakpoint not set, reset sequence complete", UVM_MEDIUM)
    end

  endtask


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
        `uvm_fatal("SOC_IFC_RST", "SOC_IFC ENV reset sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")
  endtask


  //==========================================
  // Name:        body
  // Description: Run the main functionality
  //==========================================
  virtual task body();

    ctrl_reset_seq_context_t ctrl_rst_ctx;

    // Run ctrl seq
    run_ctrl_reset_seq(ctrl_rst_ctx);

    // Reset the PAUSER override in the reg adapter so the first APB transfer
    // after a reset uses default PAUSER (but can be overridden later)
    configuration.apb_reg_adapter_h.pauser_override = configuration.soc_ifc_rm.soc_ifc_reg_rm.CPTRA_VALID_PAUSER[0].PAUSER.get_reset();

    // Download Fuses when ready
    download_fuses();

    // Breakpoint configuration
    configure_breakpoint(ctrl_rst_ctx);

  endtask

endclass

