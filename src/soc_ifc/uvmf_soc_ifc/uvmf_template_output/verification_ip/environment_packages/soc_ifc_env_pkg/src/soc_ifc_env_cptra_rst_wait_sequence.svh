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
// DESCRIPTION: Sequence to wait for Caliptra noncore reset to deassert
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_cptra_rst_wait_sequence #(
      type CONFIG_T
      ) extends soc_ifc_env_sequence_base #(.CONFIG_T(CONFIG_T));


  `uvm_object_param_utils( soc_ifc_env_cptra_rst_wait_sequence #(
                           CONFIG_T
                           ) );

    typedef cptra_status_responder_sequence  cptra_status_agent_responder_seq_t;
    cptra_status_agent_responder_seq_t cptra_status_agent_rsp_seq;





  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  function new(string name = "" );
    super.new(name);


  endfunction

  virtual task body();

    int sts_rsp_count = 0;
    bit noncore_rst_asserted = 1;
    reg_model = configuration.soc_ifc_rm;

    if (cptra_status_agent_rsp_seq == null)
        `uvm_error("CPTRA_RESET_WAIT", "SOC_IFC ENV caliptra reset wait sequence expected a handle to the cptra status agent responder sequence (from bench-level sequence) but got null!")
    fork
        forever begin
            @(cptra_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    // Poll new responses to detect reset deassertion
    while (noncore_rst_asserted) begin
        wait(sts_rsp_count > 0);
        `uvm_info("CPTRA_RESET_WAIT", "Received response from status agent", UVM_MEDIUM)
        if (sts_rsp_count > 1)
            `uvm_error("CPTRA_RESET_WAIT", "Did not expect to receive multiple status response transactions")
        noncore_rst_asserted = cptra_status_agent_rsp_seq.rsp.noncore_rst_asserted;
        sts_rsp_count--;
        if (noncore_rst_asserted)
            `uvm_error("CPTRA_RESET_WAIT", "Unexpected status transition, with noncore reset asserted, while waiting for noncore reset to deassert")
        else
            `uvm_info("CPTRA_RESET_WAIT", "Detected Caliptra noncore reset deassertion", UVM_LOW)
    end


  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

