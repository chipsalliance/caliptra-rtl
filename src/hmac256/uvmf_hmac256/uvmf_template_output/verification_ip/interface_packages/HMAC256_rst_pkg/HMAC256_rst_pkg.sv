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
//    - <hmac256_rst_typedefs_hdl>
//    - <HMAC256_rst_typedefs.svh>
//    - <HMAC256_rst_transaction.svh>

//    - <HMAC256_rst_configuration.svh>
//    - <HMAC256_rst_driver.svh>
//    - <HMAC256_rst_monitor.svh>

//    - <hmac256_rst_transaction_coverage.svh>
//    - <HMAC256_rst_sequence_base.svh>
//    - <HMAC256_rst_random_sequence.svh>

//    - <HMAC256_rst_responder_sequence.svh>
//    - <HMAC256_rst2reg_adapter.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package HMAC256_rst_pkg;
  
   import uvm_pkg::*;
   import uvmf_base_pkg_hdl::*;
   import uvmf_base_pkg::*;
   import HMAC256_rst_pkg_hdl::*;

   `include "uvm_macros.svh"

   // pragma uvmf custom package_imports_additional begin 
   // pragma uvmf custom package_imports_additional end
   `include "src/HMAC256_rst_macros.svh"

   export HMAC256_rst_pkg_hdl::*;
   
 

   // Parameters defined as HVL parameters

   `include "src/HMAC256_rst_typedefs.svh"
   `include "src/HMAC256_rst_transaction.svh"

   `include "src/HMAC256_rst_configuration.svh"
   `include "src/HMAC256_rst_driver.svh"
   `include "src/HMAC256_rst_monitor.svh"

   `include "src/HMAC256_rst_transaction_coverage.svh"
   `include "src/HMAC256_rst_sequence_base.svh"
   `include "src/HMAC256_rst_random_sequence.svh"

   `include "src/HMAC256_rst_responder_sequence.svh"
   `include "src/HMAC256_rst2reg_adapter.svh"

   `include "src/HMAC256_rst_agent.svh"

   // pragma uvmf custom package_item_additional begin
   // UVMF_CHANGE_ME : When adding new interface sequences to the src directory
   //    be sure to add the sequence file here so that it will be
   //    compiled as part of the interface package.  Be sure to place
   //    the new sequence after any base sequences of the new sequence.
   // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

