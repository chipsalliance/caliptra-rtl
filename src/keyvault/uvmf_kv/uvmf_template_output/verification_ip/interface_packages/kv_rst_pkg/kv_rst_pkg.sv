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
//    - <kv_rst_typedefs_hdl>
//    - <kv_rst_typedefs.svh>
//    - <kv_rst_transaction.svh>

//    - <kv_rst_configuration.svh>
//    - <kv_rst_driver.svh>
//    - <kv_rst_monitor.svh>

//    - <kv_rst_transaction_coverage.svh>
//    - <kv_rst_sequence_base.svh>
//    - <kv_rst_random_sequence.svh>

//    - <kv_rst_responder_sequence.svh>
//    - <kv_rst2reg_adapter.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package kv_rst_pkg;
  
   import uvm_pkg::*;
   import uvmf_base_pkg_hdl::*;
   import uvmf_base_pkg::*;
   import kv_rst_pkg_hdl::*;

   `include "uvm_macros.svh"

   // pragma uvmf custom package_imports_additional begin 
   // pragma uvmf custom package_imports_additional end
   `include "src/kv_rst_macros.svh"

   export kv_rst_pkg_hdl::*;
   
 

   // Parameters defined as HVL parameters

   `include "src/kv_rst_typedefs.svh"
   `include "src/kv_rst_transaction.svh"

   `include "src/kv_rst_configuration.svh"
   `include "src/kv_rst_driver.svh"
   `include "src/kv_rst_monitor.svh"

   `include "src/kv_rst_transaction_coverage.svh"
   `include "src/kv_rst_sequence_base.svh"
   `include "src/kv_rst_random_sequence.svh"

   `include "src/kv_rst_responder_sequence.svh"
   `include "src/kv_rst2reg_adapter.svh"
   `include "src/kv_rst_poweron_sequence.svh"
   `include "src/kv_rst_warm_rst_sequence.svh"
   `include "src/kv_rst_cold_rst_sequence.svh"
   `include "src/kv_rst_core_rst_sequence.svh"
   `include "src/kv_rst_debug_sequence.svh"
   `include "src/kv_rst_debug_on_sequence.svh"
   `include "src/kv_rst_debug_off_sequence.svh"

   `include "src/kv_rst_agent.svh"

   // pragma uvmf custom package_item_additional begin
   // UVMF_CHANGE_ME : When adding new interface sequences to the src directory
   //    be sure to add the sequence file here so that it will be
   //    compiled as part of the interface package.  Be sure to place
   //    the new sequence after any base sequences of the new sequence.
   // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

