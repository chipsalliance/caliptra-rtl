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
// DESCRIPTION: This file contains the top level sequence used in register_test.
// It uses the UVM built in register test.  Specific UVM built-in tests can be
// selected in the body task.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class register_test_sequence extends soc_ifc_bench_sequence_base;

  `uvm_object_utils( register_test_sequence );

  uvm_reg_mem_built_in_seq uvm_register_test_seq;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  function new(string name = "" );
    super.new(name);
  endfunction

  // ****************************************************************************
  virtual task body();
    uvm_register_test_seq = new("uvm_register_test_seq");

    // Reset the DUT
    fork
      // pragma uvmf custom register_test_reset begin
      // UVMF_CHANGE_ME 
      // Select the desired wait_for_reset or provide custom mechanism.
      // fork-join for this code block may be unnecessary based on your situation.
      soc_ifc_ctrl_agent_config.wait_for_reset();
      cptra_ctrl_agent_config.wait_for_reset();
      soc_ifc_status_agent_config.wait_for_reset();
      cptra_status_agent_config.wait_for_reset();
      mbox_sram_agent_config.wait_for_reset();
      // pragma uvmf custom register_test_reset end
    join

      // pragma uvmf custom register_test_setup begin
      // UVMF_CHANGE_ME perform potentially necessary operations before running the sequence.
      // pragma uvmf custom register_test_setup end

    // Reset the register model
    reg_model.reset();
    // Identify the register model to test
    uvm_register_test_seq.model = reg_model;
    // Perform the register test
    // Disable particular tests in sequence by commenting options below
    uvm_register_test_seq.tests = {
    // pragma uvmf custom register_test_operation begin
                                   UVM_DO_REG_HW_RESET      |
                                   UVM_DO_REG_BIT_BASH      |
                                   UVM_DO_REG_ACCESS        |
                                   UVM_DO_MEM_ACCESS        |
                                   UVM_DO_SHARED_ACCESS     |
                                   UVM_DO_MEM_WALK          |
                                   UVM_DO_ALL_REG_MEM_TESTS 
    // pragma uvmf custom register_test_operation end
                                  };

    uvm_register_test_seq.start(null);

  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

