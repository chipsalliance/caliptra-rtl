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
// Description: HMAC_last_alone_error_test
//   Directed test that exercises the LAST-alone CTRL write so the
//   hmac.last_alone_error path raises error2_sts and the
//   last_alone_ignored covergroup bin gets hit.
//----------------------------------------------------------------------

`ifndef __HMAC_LAST_ALONE_ERROR_TEST
`define __HMAC_LAST_ALONE_ERROR_TEST

`include "uvm_macros.svh"

class HMAC_last_alone_error_test extends test_top;

  `uvm_component_utils(HMAC_last_alone_error_test)

  // constructor
  function new(string name = "", uvm_component parent = null );
    super.new(name, parent);
  endfunction : new


  virtual function void build_phase(uvm_phase phase );
    // UVM Factory override. Override HMAC_bench_sequence_base with HMAC_last_alone_error_sequence
    HMAC_bench_sequence_base::type_id::set_type_override(HMAC_last_alone_error_sequence #(64,32,0)::get_type());
    super.build_phase(phase);
  endfunction : build_phase

endclass : HMAC_last_alone_error_test

`endif
