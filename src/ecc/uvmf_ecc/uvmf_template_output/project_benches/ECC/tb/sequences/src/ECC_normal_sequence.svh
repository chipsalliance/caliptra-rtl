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

`ifndef __ECC_NORMAL_SEQUENCE
`define __ECCC_NORMAL_SEQUENCE

`include "uvm_macros.svh"

class ECC_normal_sequence #(int AHB_DATA_WIDTH = 64,
                            int AHB_ADDR_WIDTH = 32
                            ) extends ECC_bench_sequence_base;

  `uvm_object_utils(ECC_normal_sequence) 

  // Define type and handle for reset sequence
  typedef ECC_in_normal_sequence #(AHB_DATA_WIDTH, AHB_ADDR_WIDTH) ECC_in_normal_sequence_t;
  ECC_in_normal_sequence_t ECC_in_normal_s;
  
  // constructor
  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual task body();
    //ECC_in_agent_random_seq = ECC_in_random_sequence#()::type_id::create("ECC_in_agent_random_seq");
    ECC_in_normal_s = ECC_in_normal_sequence#()::type_id::create("ECC_in_normal_s");

    fork
      ECC_in_agent_config.wait_for_reset();
      ECC_out_agent_config.wait_for_reset();
    join

    //repeat (10) ECC_in_agent_random_seq.start(ECC_in_agent_sequencer);
    repeat (10) ECC_in_normal_s.start(ECC_in_agent_sequencer);
    //repeat (5) ECC_in_agent_random_seq.start(ECC_in_agent_sequencer);

    fork
      ECC_in_agent_config.wait_for_num_clocks(50);    
      ECC_out_agent_config.wait_for_num_clocks(50);
    join

    if (1) // TODO -- how to properly choose which to print?
        $display("* TESTCASE PASSED");
    else
        $display("* TESTCASE FAILED");
  endtask


endclass : ECC_normal_sequence

`endif
