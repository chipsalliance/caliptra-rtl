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
//    - <pv_rst_typedefs_hdl>
//    - <pv_rst_typedefs.svh>
//    - <pv_rst_transaction.svh>

//    - <pv_rst_configuration.svh>
//    - <pv_rst_driver.svh>
//    - <pv_rst_monitor.svh>

//    - <pv_rst_transaction_coverage.svh>
//    - <pv_rst_sequence_base.svh>
//    - <pv_rst_random_sequence.svh>

//    - <pv_rst_responder_sequence.svh>
//    - <pv_rst2reg_adapter.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package pv_rst_pkg;
  
   import uvm_pkg::*;
   import uvmf_base_pkg_hdl::*;
   import uvmf_base_pkg::*;
   import pv_rst_pkg_hdl::*;

   `include "uvm_macros.svh"

   // pragma uvmf custom package_imports_additional begin 
   // pragma uvmf custom package_imports_additional end
   `include "src/pv_rst_macros.svh"

   export pv_rst_pkg_hdl::*;
   
 

   // Parameters defined as HVL parameters

   `include "src/pv_rst_typedefs.svh"
   `include "src/pv_rst_transaction.svh"

   `include "src/pv_rst_configuration.svh"
   `include "src/pv_rst_driver.svh"
   `include "src/pv_rst_monitor.svh"

   `include "src/pv_rst_transaction_coverage.svh"
   `include "src/pv_rst_sequence_base.svh"
   `include "src/pv_rst_random_sequence.svh"
   `include "src/pv_rst_cold_rst_sequence.svh"
   `include "src/pv_rst_warm_rst_sequence.svh"
   `include "src/pv_rst_poweron_sequence.svh"

   `include "src/pv_rst_responder_sequence.svh"
   `include "src/pv_rst2reg_adapter.svh"

   `include "src/pv_rst_agent.svh"

   // pragma uvmf custom package_item_additional begin
   // UVMF_CHANGE_ME : When adding new interface sequences to the src directory
   //    be sure to add the sequence file here so that it will be
   //    compiled as part of the interface package.  Be sure to place
   //    the new sequence after any base sequences of the new sequence.
   // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

