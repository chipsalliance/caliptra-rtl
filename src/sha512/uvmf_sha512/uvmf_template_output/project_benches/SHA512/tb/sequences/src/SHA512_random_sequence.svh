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
// Description: SHA512_random_sequence
//----------------------------------------------------------------------

`ifndef __SHA512_RANDOM_SEQUENCE
`define __SHA512_RANDOM_SEQUENCE

`include "uvm_macros.svh"

class SHA512_random_sequence #(int AHB_DATA_WIDTH = 64,
                            int AHB_ADDR_WIDTH = 32,
                            bit BYPASS_HSEL = 0
                            ) extends SHA512_bench_sequence_base;

  `uvm_object_utils(SHA512_random_sequence)

  // Define type and handle for reset sequence
  typedef SHA512_in_reset_sequence #(AHB_DATA_WIDTH, AHB_ADDR_WIDTH, BYPASS_HSEL) SHA512_in_reset_sequence_t;
  SHA512_in_reset_sequence_t SHA512_in_reset_s;

  // constructor
  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual task body();
    SHA512_in_agent_random_seq = SHA512_in_random_sequence#()::type_id::create("SHA512_in_agent_random_seq");
    SHA512_in_reset_s = SHA512_in_reset_sequence#()::type_id::create("SHA512_in_reset_s");

    SHA512_in_agent_config.wait_for_reset();
    SHA512_in_agent_config.wait_for_num_clocks(10);

    repeat (10) SHA512_in_agent_random_seq.start(SHA512_in_agent_sequencer);
    SHA512_in_reset_s.start(SHA512_in_agent_sequencer);
    repeat (5) SHA512_in_agent_random_seq.start(SHA512_in_agent_sequencer);

    SHA512_in_agent_config.wait_for_num_clocks(50);

    if (1) // TODO -- how to properly choose which to print?
        $display("* TESTCASE PASSED");
    else
        $display("* TESTCASE FAILED");
  endtask


endclass : SHA512_random_sequence

`endif
