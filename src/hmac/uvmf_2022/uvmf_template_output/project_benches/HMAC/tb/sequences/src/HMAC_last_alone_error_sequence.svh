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

`ifndef __HMAC_LAST_ALONE_ERROR_SEQUENCE
`define __HMAC_LAST_ALONE_ERROR_SEQUENCE

`include "uvm_macros.svh"

class HMAC_last_alone_error_sequence #(int AHB_DATA_WIDTH = 64,
                                       int AHB_ADDR_WIDTH = 32,
                                       bit BYPASS_HSEL = 0
                                       ) extends HMAC_bench_sequence_base;

  `uvm_object_utils(HMAC_last_alone_error_sequence)

  // Define type and handle for the in-agent last-alone-error sequence
  typedef HMAC_in_last_alone_error_sequence #(AHB_DATA_WIDTH, AHB_ADDR_WIDTH, BYPASS_HSEL) HMAC_in_last_alone_error_sequence_t;
  HMAC_in_last_alone_error_sequence_t HMAC_in_last_alone_error_s;

  // constructor
  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual task body();
    HMAC_in_last_alone_error_s = HMAC_in_last_alone_error_sequence#()::type_id::create("HMAC_in_last_alone_error_s");

    HMAC_in_agent_config.wait_for_reset();
    HMAC_in_agent_config.wait_for_num_clocks(10);

    HMAC_in_last_alone_error_s.start(HMAC_in_agent_sequencer);

    HMAC_in_agent_config.wait_for_num_clocks(50);

    if (1) // TODO -- how to properly choose which to print?
        $display("* TESTCASE PASSED");
    else
        $display("* TESTCASE FAILED");
  endtask


endclass : HMAC_last_alone_error_sequence

`endif
