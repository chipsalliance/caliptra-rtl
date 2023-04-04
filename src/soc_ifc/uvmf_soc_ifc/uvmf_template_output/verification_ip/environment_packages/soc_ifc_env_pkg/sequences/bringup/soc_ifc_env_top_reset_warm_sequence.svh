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
// DESCRIPTION: Sequence to initiate (and respond) to warm reset of soc_ifc.
//              "TOP" sequence because it invokes lower level env sequences
//              to facilitate the uC/SoC sides of reset initiation and bringup.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_top_reset_warm_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


  `uvm_object_utils( soc_ifc_env_top_reset_warm_sequence )

  rand soc_ifc_env_reset_warm_sequence_t     soc_ifc_env_rst_seq;
  rand soc_ifc_env_cptra_rst_wait_sequence_t soc_ifc_env_cptra_rst_wait_seq;



  // pragma uvmf custom class_item_additional begin
  extern virtual function      create_seqs();
  extern virtual function void connect_extra_soc_ifc_resp_seqs();
  extern virtual function void connect_extra_cptra_resp_seqs();
  extern virtual function      randomize_seqs();
  extern virtual task          start_seqs();

  // pragma uvmf custom class_item_additional end

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
        `uvm_fatal("SOC_IFC_WARM_RST_TOP", "SOC_IFC ENV top warm reset sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")
    end
    else begin
        soc_ifc_env_rst_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_status_agent_rsp_seq;
        connect_extra_soc_ifc_resp_seqs();
    end
    if (cptra_status_agent_rsp_seq == null) begin
        `uvm_fatal("SOC_IFC_WARM_RST_TOP", "SOC_IFC ENV top mailbox sequence expected a handle to the cptra status agent responder sequence (from bench-level sequence) but got null!")
    end
    else begin
        soc_ifc_env_cptra_rst_wait_seq.cptra_status_agent_rsp_seq = cptra_status_agent_rsp_seq;
        connect_extra_cptra_resp_seqs();
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
    randomize_seqs();
    start_seqs();

    `uvm_info("SOC_IFC_WARM_RST_TOP", "Top mailbox sequence done", UVM_LOW)

  endtask

endclass

// pragma uvmf custom external begin
function soc_ifc_env_top_reset_warm_sequence::create_seqs();
    soc_ifc_env_rst_seq            = soc_ifc_env_reset_warm_sequence_t::type_id::create("soc_ifc_env_rst_seq");
    soc_ifc_env_cptra_rst_wait_seq = soc_ifc_env_cptra_rst_wait_sequence_t::type_id::create("soc_ifc_env_cptra_rst_wait_seq");
endfunction

function void soc_ifc_env_top_reset_warm_sequence::connect_extra_soc_ifc_resp_seqs();
endfunction

function void soc_ifc_env_top_reset_warm_sequence::connect_extra_cptra_resp_seqs();
endfunction

function soc_ifc_env_top_reset_warm_sequence::randomize_seqs();
    if(!soc_ifc_env_rst_seq.randomize())
        `uvm_fatal("SOC_IFC_WARM_RST_TOP", $sformatf("soc_ifc_env_top_reset_warm_sequence::body() - %s randomization failed", soc_ifc_env_rst_seq.get_type_name()));
    if(!soc_ifc_env_cptra_rst_wait_seq.randomize())
        `uvm_fatal("SOC_IFC_WARM_RST_TOP", $sformatf("soc_ifc_env_top_reset_warm_sequence::body() - %s randomization failed", soc_ifc_env_cptra_rst_wait_seq.get_type_name()));
    soc_ifc_env_cptra_rst_wait_seq.wait_for_noncore_rst_assert   = 1'b1;
    soc_ifc_env_cptra_rst_wait_seq.wait_for_core_rst_assert      = 1'b0;
    soc_ifc_env_cptra_rst_wait_seq.wait_for_noncore_rst_deassert = 1'b0;
    soc_ifc_env_cptra_rst_wait_seq.wait_for_core_rst_deassert    = 1'b1;
endfunction

task soc_ifc_env_top_reset_warm_sequence::start_seqs();
    fork
        soc_ifc_env_rst_seq.start(configuration.vsqr);
        soc_ifc_env_cptra_rst_wait_seq.start(configuration.vsqr);
    join
endtask
// pragma uvmf custom external end

