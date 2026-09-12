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
// Description: ECC_otf_reset_test
//----------------------------------------------------------------------

`ifndef __ECC_OTF_RESET_TEST
`define __ECC_OTF_RESET_TEST

`include "uvm_macros.svh"

class ECC_otf_reset_test extends test_top;

  `uvm_component_utils(ECC_otf_reset_test) 
  
  // constructor
  function new(string name = "", uvm_component parent = null );
    super.new(name, parent);
    // Insert Constructor Code Here
  endfunction : new


  virtual function void build_phase(uvm_phase phase );
    // UVM Factory override. Override ECC_bench_sequence_base with ECC_otf_reset_sequence
    ECC_bench_sequence_base::type_id::set_type_override(ECC_otf_reset_sequence #(64,32)::get_type());
    super.build_phase(phase);
  endfunction : build_phase

endclass : ECC_otf_reset_test

`endif
