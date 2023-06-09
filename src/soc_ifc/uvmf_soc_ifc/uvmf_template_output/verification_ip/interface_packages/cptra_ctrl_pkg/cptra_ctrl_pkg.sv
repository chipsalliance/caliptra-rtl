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
//    - <cptra_ctrl_typedefs_hdl>
//    - <cptra_ctrl_typedefs.svh>
//    - <cptra_ctrl_transaction.svh>

//    - <cptra_ctrl_configuration.svh>
//    - <cptra_ctrl_driver.svh>
//    - <cptra_ctrl_monitor.svh>

//    - <cptra_ctrl_transaction_coverage.svh>
//    - <cptra_ctrl_sequence_base.svh>
//    - <cptra_ctrl_random_sequence.svh>

//    - <cptra_ctrl_responder_sequence.svh>
//    - <cptra_ctrl2reg_adapter.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package cptra_ctrl_pkg;
  
   import uvm_pkg::*;
   import uvmf_base_pkg_hdl::*;
   import uvmf_base_pkg::*;
   import cptra_ctrl_pkg_hdl::*;

   `include "uvm_macros.svh"

   // pragma uvmf custom package_imports_additional begin 
   import soc_ifc_pkg::*;
   // pragma uvmf custom package_imports_additional end
   `include "src/cptra_ctrl_macros.svh"

   export cptra_ctrl_pkg_hdl::*;
   
 

   // Parameters defined as HVL parameters

   `include "src/cptra_ctrl_typedefs.svh"
   `include "src/cptra_ctrl_transaction.svh"

   `include "src/cptra_ctrl_configuration.svh"
   `include "src/cptra_ctrl_driver.svh"
   `include "src/cptra_ctrl_monitor.svh"

   `include "src/cptra_ctrl_transaction_coverage.svh"
   `include "src/cptra_ctrl_sequence_base.svh"
   `include "src/cptra_ctrl_random_sequence.svh"

   `include "src/cptra_ctrl_responder_sequence.svh"
   `include "src/cptra_ctrl2reg_adapter.svh"

   `include "src/cptra_ctrl_agent.svh"

   // pragma uvmf custom package_item_additional begin
   // UVMF_CHANGE_ME : When adding new interface sequences to the src directory
   //    be sure to add the sequence file here so that it will be
   //    compiled as part of the interface package.  Be sure to place
   //    the new sequence after any base sequences of the new sequence.
   // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

