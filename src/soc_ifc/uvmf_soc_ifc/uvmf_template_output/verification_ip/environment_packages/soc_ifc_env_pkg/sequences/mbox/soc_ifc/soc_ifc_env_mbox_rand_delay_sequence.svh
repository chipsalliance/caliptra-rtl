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
// DESCRIPTION: Extended from mbox_base sequence to provide additional
//              functionality in a test that sends small mailbox commands.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_rand_delay_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_rand_delay_sequence )


  // Constrain command to undefined opcode
  constraint mbox_cmd_undef_c { !(mbox_op_rand.cmd.cmd_s inside {defined_cmds}); }

  // Force delays to be injected at every step
  constraint rand_delay_en_c { rand_delay_en == 1'b1; };

  extern virtual task do_rand_delay(input bit do_delay_randomize=1, input delay_scale_e scale=DLY_SMALL);

  //==========================================
  // Function:    new
  // Description: Constructor
  //==========================================
  function new(string name = "" );
    super.new(name);
    // Disable this constraint to allow wider coverage on
    // delay types in delay sequences
    this.delay_scale_c.constraint_mode(0);
  endfunction

endclass

//==========================================
// Function:    do_rand_delay
// Description: Use the class variable "rand_delay"
//              to inject random stalls between various stages
//              of the sequence.
//              If do_delay_randomize is set to 1, the value
//              of rand_delay is re-randomized (according to
//              class constraints), otherwise the previous value
//              is used.
// ---------
//              This sequence extends functionality of this task to also
//              re-randomize the _scales_ that are used throughout the sequence
//              to give even wider delay coverage.
//==========================================
task soc_ifc_env_mbox_rand_delay_sequence::do_rand_delay(input bit do_delay_randomize=1, input delay_scale_e scale=DLY_SMALL);
    super.do_rand_delay(do_delay_randomize, scale);
    if (do_delay_randomize) begin
        if (!this.randomize(poll_delay, step_delay, data_delay))
            `uvm_error("MBOX_SEQ", $sformatf("Failed to randomize delay scales"))
        else
            `uvm_info("MBOX_SEQ", $sformatf("Generated new delay scales: poll [%p] step [%p] data [%p]", poll_delay, step_delay, data_delay), UVM_DEBUG)
    end
endtask
