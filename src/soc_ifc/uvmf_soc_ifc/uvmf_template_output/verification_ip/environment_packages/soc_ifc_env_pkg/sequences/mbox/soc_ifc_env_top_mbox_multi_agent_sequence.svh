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
// DESCRIPTION: Sequence to initiate (and respond) to mailbox command
//              "TOP" sequence because it invokes lower level env sequences
//              to facilitate the uC/SoC sides of mailbox command handling
//              and this sequence defines the whole mailbox flow.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_top_mbox_multi_agent_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


  `uvm_object_utils( soc_ifc_env_top_mbox_multi_agent_sequence )

  soc_ifc_env_mbox_rand_multi_agent_sequence_t soc_ifc_env_mbox_seq;
  soc_ifc_env_cptra_mbox_handler_sequence_t    soc_ifc_env_cptra_multi_agent_handler_seq[];



  extern virtual function      create_and_randomize_seqs();
  extern virtual task          start_seqs();

  function new(string name = "" );
    super.new(name);
    create_and_randomize_seqs();
  endfunction

  virtual task body();

    int ii;
    int sts_rsp_count = 0;
    uvm_status_e sts;
    reg_model = configuration.soc_ifc_rm;

    // Response sequences catch 'status' transactions
    if (soc_ifc_status_agent_rsp_seq == null) begin
        `uvm_fatal("SOC_IFC_MBOX_TOP", "SOC_IFC ENV top mailbox sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")
    end
    else begin
        soc_ifc_env_mbox_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_status_agent_rsp_seq;
    end
    if (cptra_status_agent_rsp_seq == null) begin
        `uvm_fatal("SOC_IFC_MBOX_TOP", "SOC_IFC ENV top mailbox sequence expected a handle to the cptra status agent responder sequence (from bench-level sequence) but got null!")
    end
    else begin
        for (ii=0; ii<soc_ifc_env_cptra_multi_agent_handler_seq.size(); ii++) begin
            soc_ifc_env_cptra_multi_agent_handler_seq[ii].cptra_status_agent_rsp_seq = cptra_status_agent_rsp_seq;
        end
    end

    fork
        forever begin
            @(cptra_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
        forever begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    // Initiate the mailbox command sender and receiver sequences
    start_seqs();

    `uvm_info("SOC_IFC_MBOX_TOP", "Top mailbox sequence done", UVM_LOW)

  endtask

endclass

// pragma uvmf custom external begin
function soc_ifc_env_top_mbox_multi_agent_sequence::create_and_randomize_seqs();
    int ii;

    soc_ifc_env_mbox_seq          = soc_ifc_env_mbox_rand_multi_agent_sequence_t::type_id::create("soc_ifc_env_mbox_seq");
    if(!soc_ifc_env_mbox_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_multi_agent_sequence::body() - %s randomization failed", soc_ifc_env_mbox_seq.get_type_name()));
    soc_ifc_env_cptra_multi_agent_handler_seq = new[soc_ifc_env_mbox_seq.agents];
    for (ii=0; ii<soc_ifc_env_cptra_multi_agent_handler_seq.size(); ii++) begin
        soc_ifc_env_cptra_multi_agent_handler_seq[ii] = soc_ifc_env_cptra_mbox_handler_sequence_t::type_id::create($sformatf("soc_ifc_env_cptra_multi_agent_handler_seq[%0d]", ii));
        if(!soc_ifc_env_cptra_multi_agent_handler_seq[ii].randomize())
            `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_multi_agent_sequence::body() - %s randomization failed", soc_ifc_env_cptra_multi_agent_handler_seq[ii].get_type_name()));
    end
endfunction

task soc_ifc_env_top_mbox_multi_agent_sequence::start_seqs();
    int ii;
    fork
        soc_ifc_env_mbox_seq.start(configuration.vsqr);
        for (ii=0; ii < soc_ifc_env_cptra_multi_agent_handler_seq.size(); ii++) begin
            soc_ifc_env_cptra_multi_agent_handler_seq[ii].start(configuration.vsqr);
        end
    join
endtask
// pragma uvmf custom external end

