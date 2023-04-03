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
class soc_ifc_env_cptra_rst_wait_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


  `uvm_object_utils( soc_ifc_env_cptra_rst_wait_sequence );






  // pragma uvmf custom class_item_additional begin
  bit wait_for_noncore_rst_assert   = 1'b0;
  bit wait_for_core_rst_assert      = 1'b0;
  bit wait_for_noncore_rst_deassert = 1'b1; // Default is to only do this
  bit wait_for_core_rst_deassert    = 1'b0;
  // pragma uvmf custom class_item_additional end

  function new(string name = "" );
    super.new(name);

  endfunction

  virtual task body();

    int sts_rsp_count = 0;
    bit noncore_rst_asserted = wait_for_noncore_rst_assert ? 1'b0 : wait_for_noncore_rst_deassert;
    bit core_rst_asserted    = wait_for_core_rst_assert    ? 1'b0 : wait_for_core_rst_deassert;
    reg_model = configuration.soc_ifc_rm;

    if ((wait_for_noncore_rst_assert   && wait_for_core_rst_assert  ) ||
        (wait_for_noncore_rst_deassert && wait_for_core_rst_deassert)   )
        `uvm_fatal("CPTRA_RESET_WAIT", "Invalid use-case: cannot intermix multiple wait-for-assert or multiple wait-for-deassert invocations")

    if (cptra_status_agent_rsp_seq == null)
        `uvm_fatal("CPTRA_RESET_WAIT", "SOC_IFC ENV caliptra reset wait sequence expected a handle to the cptra status agent responder sequence (from bench-level sequence) but got null!")
    fork
        forever begin
            @(cptra_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    // Poll new responses to detect reset assertion
    while (wait_for_noncore_rst_assert && !noncore_rst_asserted) begin
        wait(sts_rsp_count > 0);
        `uvm_info("CPTRA_RESET_WAIT", "Received response from status agent", UVM_MEDIUM)
        if (sts_rsp_count > 1)
            `uvm_error("CPTRA_RESET_WAIT", "Did not expect to receive multiple status response transactions")
        noncore_rst_asserted = cptra_status_agent_rsp_seq.rsp.noncore_rst_asserted;
        core_rst_asserted = cptra_status_agent_rsp_seq.rsp.uc_rst_asserted;
        sts_rsp_count--;
        if (!noncore_rst_asserted || !core_rst_asserted)
            `uvm_error("CPTRA_RESET_WAIT", "Unexpected status transition, with noncore/core resets deasserted, while waiting for noncore reset to assert")
        else
            `uvm_info("CPTRA_RESET_WAIT", "Detected Caliptra noncore reset assertion", UVM_LOW)
    end
    while (wait_for_core_rst_assert && !core_rst_asserted) begin
        wait(sts_rsp_count > 0);
        `uvm_info("CPTRA_RESET_WAIT", "Received response from status agent", UVM_MEDIUM)
        if (sts_rsp_count > 1)
            `uvm_error("CPTRA_RESET_WAIT", "Did not expect to receive multiple status response transactions")
        noncore_rst_asserted = cptra_status_agent_rsp_seq.rsp.noncore_rst_asserted;
        core_rst_asserted = cptra_status_agent_rsp_seq.rsp.uc_rst_asserted;
        sts_rsp_count--;
        if (!core_rst_asserted)
            `uvm_error("CPTRA_RESET_WAIT", "Unexpected status transition, with core reset deasserted, while waiting for core reset to assert")
        else
            `uvm_info("CPTRA_RESET_WAIT", "Detected Caliptra core reset assertion", UVM_LOW)
    end

    // Poll new responses to detect reset deassertion
    while (wait_for_noncore_rst_deassert && noncore_rst_asserted) begin
        wait(sts_rsp_count > 0);
        `uvm_info("CPTRA_RESET_WAIT", "Received response from status agent", UVM_MEDIUM)
        if (sts_rsp_count > 1)
            `uvm_error("CPTRA_RESET_WAIT", "Did not expect to receive multiple status response transactions")
        noncore_rst_asserted = cptra_status_agent_rsp_seq.rsp.noncore_rst_asserted;
        sts_rsp_count--;
        if (noncore_rst_asserted)
            `uvm_info("CPTRA_RESET_WAIT", "Detected status transition, with noncore reset asserted, while waiting for noncore reset to deassert", UVM_MEDIUM)
        else
            `uvm_info("CPTRA_RESET_WAIT", "Detected Caliptra noncore reset deassertion", UVM_LOW)
    end
    while (wait_for_core_rst_deassert && core_rst_asserted) begin
        wait(sts_rsp_count > 0);
        `uvm_info("CPTRA_RESET_WAIT", "Received response from status agent", UVM_MEDIUM)
        if (sts_rsp_count > 1)
            `uvm_error("CPTRA_RESET_WAIT", "Did not expect to receive multiple status response transactions")
        sts_rsp_count--;
        noncore_rst_asserted = cptra_status_agent_rsp_seq.rsp.noncore_rst_asserted;
        core_rst_asserted = cptra_status_agent_rsp_seq.rsp.uc_rst_asserted;
        // If noncore_rst asserted since entering this sequence, noncore_rst
        // will deassert before (or simultaneous to) core_rst deassertion
        if (wait_for_noncore_rst_assert && noncore_rst_asserted && !core_rst_asserted)
            `uvm_error("CPTRA_RESET_WAIT", "Unexpected status transition, with noncore reset asserted, after detecting core reset deassertion")
        else if (core_rst_asserted)
            `uvm_info("CPTRA_RESET_WAIT", "Caliptra core reset is still asserted, continuing to poll...", UVM_MEDIUM)
        else
            `uvm_info("CPTRA_RESET_WAIT", "Detected Caliptra core reset deassertion", UVM_LOW)
    end


  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

