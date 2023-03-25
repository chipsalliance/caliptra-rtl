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

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: Mailbox/Reset sequence provides a command flow
//              that executes a mailbox command and injects a reset randomly
//              during the operation.
//              This is facilitated by running the mailbox flow
//              and reset in a fork.
//              After the reset completes, system may be restored to operational
//              capability (so this sequence can be interleaved with other
//              sequences in the rand test).
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_rst_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


  `uvm_object_utils( soc_ifc_env_mbox_rst_sequence )

  soc_ifc_env_mbox_sequence_base_t      soc_ifc_env_mbox_seq;
  soc_ifc_env_reset_sequence_base_t     soc_ifc_env_rst_seq;

  extern virtual function      create_seqs();
  extern virtual function void connect_extra_soc_ifc_resp_seqs();
  extern virtual function      randomize_seqs();
  extern virtual task          start_seqs();
  extern virtual task          run_restore_seqs();

  function new(string name = "" );
    super.new(name);
    create_seqs();
  endfunction

  virtual task body();

    int sts_rsp_count = 0;
    uvm_status_e sts;
    reg_model = configuration.soc_ifc_rm;

    // Response sequences catch 'status' transactions
    if (soc_ifc_status_agent_rsp_seq == null) begin
        `uvm_fatal("SOC_IFC_MBOX", "SOC_IFC ENV mailbox sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")
    end
    else begin
        soc_ifc_env_mbox_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_status_agent_rsp_seq;
        soc_ifc_env_rst_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_status_agent_rsp_seq;
        connect_extra_soc_ifc_resp_seqs();
    end

    fork
        forever begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    // Initiate the mailbox command sender and receiver sequences
    randomize_seqs();
    start_seqs();

    // TODO after reset, redo bringup (i.e. FW download, etc)
    run_restore_seqs();

    `uvm_info("SOC_IFC_MBOX", "Mailbox reset sequence done", UVM_LOW)

  endtask

endclass

function soc_ifc_env_mbox_rst_sequence::create_seqs();
    soc_ifc_env_mbox_seq          = soc_ifc_env_mbox_sequence_base_t::type_id::create("soc_ifc_env_mbox_seq");
    soc_ifc_env_rst_seq           = soc_ifc_env_reset_sequence_base_t::type_id::create("soc_ifc_env_rst_seq");
endfunction

function void soc_ifc_env_mbox_rst_sequence::connect_extra_soc_ifc_resp_seqs();
endfunction

function soc_ifc_env_mbox_rst_sequence::randomize_seqs();
    if(!soc_ifc_env_mbox_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX", $sformatf("soc_ifc_env_mbox_sequence_base::body() - %s randomization failed", soc_ifc_env_mbox_seq.get_type_name()));
    if(!soc_ifc_env_rst_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX", $sformatf("soc_ifc_env_mbox_sequence_base::body() - %s randomization failed", soc_ifc_env_rst_seq.get_type_name()));
endfunction

task soc_ifc_env_mbox_rst_sequence::start_seqs();
    int delay_clks; // Delay prior to system reset
    if (!std::randomize(delay_clks) with {delay_clks < 4*soc_ifc_env_mbox_seq.mbox_op_rand.dlen;}) begin
        `uvm_fatal("SOC_IFC_MBOX", $sformatf("soc_ifc_env_mbox_rst_sequence::body() - %s randomization failed", "delay_clks"));
    end
    fork
        begin
            soc_ifc_env_mbox_seq.start(configuration.vsqr);
        end
        begin
            configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(delay_clks);
            fork
                begin
                    `uvm_info("SOC_IFC_MBOX", "Starting rst sequence", UVM_HIGH)
                    soc_ifc_env_rst_seq.start(configuration.vsqr);
                end
                begin
                    `uvm_info("SOC_IFC_MBOX", "Killing mbox sequence", UVM_HIGH)
                    soc_ifc_env_mbox_seq.kill();
                    `uvm_info("SOC_IFC_MBOX", "Done: killing mbox sequence", UVM_HIGH)
                end
            join
        end
    join
endtask

task soc_ifc_env_mbox_rst_sequence::run_restore_seqs();
    // If the reset type is firmware or cold, this could reload the FW
endtask
