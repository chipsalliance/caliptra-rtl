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
// PACKAGE: This file defines all of the files contained in the
//    interface package that will run on the host simulator.
//
// CONTAINS:
//    - <ss_mode_status_typedefs_hdl>
//    - <ss_mode_status_typedefs.svh>
//    - <ss_mode_status_transaction.svh>

//    - <ss_mode_status_configuration.svh>
//    - <ss_mode_status_driver.svh>
//    - <ss_mode_status_monitor.svh>

//    - <ss_mode_status_transaction_coverage.svh>
//    - <ss_mode_status_sequence_base.svh>
//    - <ss_mode_status_random_sequence.svh>

//    - <ss_mode_status_responder_sequence.svh>
//    - <ss_mode_status2reg_adapter.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package ss_mode_status_pkg;
  
   import uvm_pkg::*;
   import uvmf_base_pkg_hdl::*;
   import uvmf_base_pkg::*;
   import ss_mode_status_pkg_hdl::*;

   `include "uvm_macros.svh"

   // pragma uvmf custom package_imports_additional begin 
   // pragma uvmf custom package_imports_additional end
   `include "src/ss_mode_status_macros.svh"

   export ss_mode_status_pkg_hdl::*;
   
 

   // Parameters defined as HVL parameters

   `include "src/ss_mode_status_typedefs.svh"
   `include "src/ss_mode_status_transaction.svh"

   `include "src/ss_mode_status_configuration.svh"
   `include "src/ss_mode_status_driver.svh"
   `include "src/ss_mode_status_monitor.svh"

   `include "src/ss_mode_status_transaction_coverage.svh"
   `include "src/ss_mode_status_sequence_base.svh"
   `include "src/ss_mode_status_random_sequence.svh"

   `include "src/ss_mode_status_responder_sequence.svh"
   `include "src/ss_mode_status2reg_adapter.svh"

   `include "src/ss_mode_status_agent.svh"

   // pragma uvmf custom package_item_additional begin
   // UVMF_CHANGE_ME : When adding new interface sequences to the src directory
   //    be sure to add the sequence file here so that it will be
   //    compiled as part of the interface package.  Be sure to place
   //    the new sequence after any base sequences of the new sequence.
   typedef ss_mode_status_sequence_base       ss_mode_status_agent_seq_base_t;
   typedef ss_mode_status_random_sequence     ss_mode_status_agent_rand_seq_t;
   typedef ss_mode_status_responder_sequence  ss_mode_status_agent_responder_seq_t;
   // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

