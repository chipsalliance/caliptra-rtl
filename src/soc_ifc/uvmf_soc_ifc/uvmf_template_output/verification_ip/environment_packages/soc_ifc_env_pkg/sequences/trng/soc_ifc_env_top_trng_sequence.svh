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
//
//----------------------------------------------------------------------
//
// DESCRIPTION: This sequence is used to initiate and respond to a TRNG 
//              request from an external source. 
//              "TOP" sequence because it invokes lower level env sequences
//              and it defines the whole TRNQ request/response flow. 
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_top_trng_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));

  `uvm_object_utils(soc_ifc_env_top_trng_sequence)

  soc_ifc_env_cptra_trng_data_req_sequence_t  soc_ifc_env_cptra_trng_data_req_seq;
  soc_ifc_env_trng_write_data_sequence_t soc_ifc_env_trng_write_data_seq;

  extern virtual function       create_seqs();
  extern virtual function void  connect_extra_soc_ifc_resp_seqs();
  extern virtual function void  connect_extra_cptra_resp_seqs();
  extern virtual function       randomize_seqs();
  extern virtual task           start_seqs();

  // pragma uvmf custom class_item_additional end

  function new(string name = "" );
    super.new(name);
    create_seqs();

  endfunction

  virtual task body();
    int sts_rsp_count;
    reg_model = configuration.soc_ifc_rm;

    if (soc_ifc_status_agent_rsp_seq == null) begin
        `uvm_fatal("SOC_IFC_TRNG_TOP", "SOC_IFC ENV top TRNG sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")
    end
    else begin
      soc_ifc_env_trng_write_data_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_status_agent_rsp_seq;
      connect_extra_soc_ifc_resp_seqs();
    end
    if (cptra_status_agent_rsp_seq == null) begin
        `uvm_fatal("SOC_IFC_TRNG_TOP", "SOC_IFC ENV top TRNG sequence expected a handle to the cptra status agent responder sequence (from bench-level sequence) but got null!")
    end
    else begin
      soc_ifc_env_cptra_trng_data_req_seq.cptra_status_agent_rsp_seq = cptra_status_agent_rsp_seq;
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

    // Initiate TRNG request and SOC responses
    randomize_seqs();
    start_seqs();

    `uvm_info("SOC_IFC_TRNG_TOP", "Top TRNG sequence done", UVM_LOW);
  endtask

endclass

function soc_ifc_env_top_trng_sequence::create_seqs();
  soc_ifc_env_cptra_trng_data_req_seq = soc_ifc_env_cptra_trng_data_req_sequence_t::type_id::create("soc_ifc_env_cptra_trng_data_req_seq");
  soc_ifc_env_trng_write_data_seq = soc_ifc_env_trng_write_data_sequence_t::type_id::create("soc_ifc_env_trng_write_data_seq");
endfunction

function void soc_ifc_env_top_trng_sequence::connect_extra_soc_ifc_resp_seqs();
endfunction

function void soc_ifc_env_top_trng_sequence::connect_extra_cptra_resp_seqs();
endfunction

function soc_ifc_env_top_trng_sequence::randomize_seqs();
  if (!soc_ifc_env_cptra_trng_data_req_seq.randomize())
    `uvm_fatal("SOC_IFC_TRNG_TOP", $sformatf("soc_if_env_top_trng_sequence::body() - %s randomization failed", soc_ifc_env_cptra_trng_data_req_seq.get_type_name()));
  if (!soc_ifc_env_trng_write_data_seq.randomize())
    `uvm_fatal("SOC_IFC_TRNG_TOP", $sformatf("soc_if_env_top_trng_sequence::body() - %s randomization failed", soc_ifc_env_trng_write_data_seq.get_type_name()));
endfunction

  
task soc_ifc_env_top_trng_sequence::start_seqs();
  fork
    begin
      `uvm_info("SOC_IFC_TRNG_TOP", "Starting soc_ifc_env_cptra_trng_req_seq", UVM_HIGH)
      soc_ifc_env_cptra_trng_data_req_seq.start(configuration.vsqr);
    end
    begin
      `uvm_info("SOC_IFC_TRNG_TOP", "Starting soc_ifc_env_rng_write_data_seq", UVM_HIGH)
      soc_ifc_env_trng_write_data_seq.start(configuration.vsqr);
    end
  join
endtask


