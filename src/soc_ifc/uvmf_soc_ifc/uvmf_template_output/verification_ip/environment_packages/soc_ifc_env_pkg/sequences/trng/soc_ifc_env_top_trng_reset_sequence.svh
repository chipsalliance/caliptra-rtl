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
//              A warm reset is issused after the TRNG request is initiated.  
//              "TOP" sequence because it invokes lower level env sequences
//              and it defines the whole TRNQ request/response flow. 
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_top_trng_reset_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));

  `uvm_object_utils(soc_ifc_env_top_trng_reset_sequence)

  soc_ifc_env_cptra_trng_data_req_sequence_t  soc_ifc_env_cptra_trng_data_req_seq;
  soc_ifc_env_trng_write_data_sequence_t soc_ifc_env_trng_write_data_seq;
  soc_ifc_env_reset_warm_sequence_t     soc_ifc_env_warm_rst_seq;
  soc_ifc_env_cptra_rst_wait_sequence_t soc_ifc_env_cptra_rst_wait_seq;

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

function soc_ifc_env_top_trng_reset_sequence::create_seqs();
  soc_ifc_env_warm_rst_seq             = soc_ifc_env_reset_warm_sequence_t::type_id::create("soc_ifc_env_warm_rst_seq");
  soc_ifc_env_cptra_rst_wait_seq  = soc_ifc_env_cptra_rst_wait_sequence_t::type_id::create("soc_ifc_env_cptra_rst_wait_seq");
  soc_ifc_env_cptra_trng_data_req_seq = soc_ifc_env_cptra_trng_data_req_sequence_t::type_id::create("soc_ifc_env_cptra_trng_data_req_seq");
  soc_ifc_env_trng_write_data_seq = soc_ifc_env_trng_write_data_sequence_t::type_id::create("soc_ifc_env_trng_write_data_seq");
endfunction

function void soc_ifc_env_top_trng_reset_sequence::connect_extra_soc_ifc_resp_seqs();
  soc_ifc_env_warm_rst_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_status_agent_rsp_seq;
endfunction

function void soc_ifc_env_top_trng_reset_sequence::connect_extra_cptra_resp_seqs();
  soc_ifc_env_cptra_rst_wait_seq.cptra_status_agent_rsp_seq = cptra_status_agent_rsp_seq;
endfunction

function soc_ifc_env_top_trng_reset_sequence::randomize_seqs();
  if (!soc_ifc_env_cptra_trng_data_req_seq.randomize())
    `uvm_fatal("SOC_IFC_TRNG_TOP", $sformatf("soc_if_env_top_trng_reset_sequence::body() - %s randomization failed", soc_ifc_env_cptra_trng_data_req_seq.get_type_name()));
  if (!soc_ifc_env_trng_write_data_seq.randomize())
    `uvm_fatal("SOC_IFC_TRNG_TOP", $sformatf("soc_if_env_top_trng_reset_sequence::body() - %s randomization failed", soc_ifc_env_trng_write_data_seq.get_type_name()));
  if(!soc_ifc_env_warm_rst_seq.randomize())                               
        `uvm_fatal("SOC_IFC_TRNG_TOP", $sformatf("soc_ifc_env_top_trng_reset_sequence::body() - %s randomization failed", soc_ifc_env_warm_rst_seq.get_type_name()));
    //if(!soc_ifc_env_cptra_handler_seq.randomize())
    //    `uvm_fatal("SOC_IFC_TRNG_TOP", $sformatf("soc_ifc_env_top_trng_reset_sequence::body() - %s randomization failed", soc_ifc_env_cptra_handler_seq.get_type_name()));
    soc_ifc_env_cptra_rst_wait_seq.wait_for_noncore_rst_assert   = 1'b1;
    soc_ifc_env_cptra_rst_wait_seq.wait_for_core_rst_assert      = 1'b0;
    soc_ifc_env_cptra_rst_wait_seq.wait_for_noncore_rst_deassert = 1'b0;
    soc_ifc_env_cptra_rst_wait_seq.wait_for_core_rst_deassert    = 1'b1;
endfunction

  
task soc_ifc_env_top_trng_reset_sequence::start_seqs();
  int delay_clks; // Delay prior to system reset
  /*if (!std::randomize(delay_clks) with {delay_clks < 10;}) begin // FIXME - need to randomize this to be less than the time it takes for SoC to respond with TRNG data
    `uvm_fatal("SOC_IFC_TRNG_TOP", $sformatf("soc_ifc_env_top_trng_reset_sequence::body() - %s randomization failed", "delay_clks"));
  end
  else begin
    `uvm_info("SOC_IFC_TRNG_TOP", $sformatf("soc_ifc_env_top_trng_reset_sequence::body() - %s randomized with %d clocks", "delay_clks", delay_clks), UVM_HIGH)
  end*/
  delay_clks = $urandom_range(2, 12);
  //delay_clks = 2;
  fork
    begin
      `uvm_info("SOC_IFC_TRNG_TOP", "Starting soc_ifc_env_cptra_trng_data_req_seq", UVM_HIGH)
      soc_ifc_env_cptra_trng_data_req_seq.start(configuration.vsqr);
    end
    begin
      `uvm_info("SOC_IFC_TRNG_TOP", "Starting soc_ifc_env_cptra_trng_data_write_seq", UVM_HIGH)
      soc_ifc_env_trng_write_data_seq.start(configuration.vsqr);
    end
    begin
      `uvm_info("SOC_IFC_TRNG_TOP", $sformatf("Starting wait for num clocks %d", delay_clks), UVM_HIGH)
      configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(delay_clks);
      `uvm_info("SOC_IFC_TRNG_TOP", $sformatf("Done wait for num clocks %d", delay_clks), UVM_HIGH)
      fork
        begin
          `uvm_info("SOC_IFC_TRNG_TOP", "Starting rst sequence", UVM_HIGH)
          soc_ifc_env_warm_rst_seq.start(configuration.vsqr);
        end
        begin
          `uvm_info("SOC_IFC_TRNG_TOP", "Killing trng_data_write_sequence handler", UVM_HIGH)
          soc_ifc_env_trng_write_data_seq.kill();
          `uvm_info("SOC_IFC_TRNG_TOP", "Done: killing trng_data_write_sequence handler", UVM_HIGH)
        end
        // FIXME - should probably not rely on this - instead, any subsequent sequence
        //         should check for ready_for_runtime to be set, and the cptra_handler should set it.
        begin
          soc_ifc_env_cptra_rst_wait_seq.start(configuration.vsqr);
          `uvm_info("SOC_IFC_TRNG_TOP", "Done: rst wait sequence", UVM_HIGH)
        end
      join
      `uvm_info("SOC_IFC_TRNG_TOP", "Starting soc_ifc_env_cptra_trng_data_write_seq after reset", UVM_HIGH)
      soc_ifc_env_trng_write_data_seq.start(configuration.vsqr);
    end
  join
endtask


