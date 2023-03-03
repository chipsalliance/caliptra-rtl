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
//    - <soc_ifc_status_typedefs_hdl>
//    - <soc_ifc_status_typedefs.svh>
//    - <soc_ifc_status_transaction.svh>

//    - <soc_ifc_status_configuration.svh>
//    - <soc_ifc_status_driver.svh>
//    - <soc_ifc_status_monitor.svh>

//    - <soc_ifc_status_transaction_coverage.svh>
//    - <soc_ifc_status_sequence_base.svh>
//    - <soc_ifc_status_random_sequence.svh>

//    - <soc_ifc_status_responder_sequence.svh>
//    - <soc_ifc_status2reg_adapter.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package soc_ifc_status_pkg;
  
   import uvm_pkg::*;
   import uvmf_base_pkg_hdl::*;
   import uvmf_base_pkg::*;
   import soc_ifc_status_pkg_hdl::*;

   `include "uvm_macros.svh"

   // pragma uvmf custom package_imports_additional begin 
   // pragma uvmf custom package_imports_additional end
   `include "src/soc_ifc_status_macros.svh"

   export soc_ifc_status_pkg_hdl::*;
   
 

   // Parameters defined as HVL parameters

   `include "src/soc_ifc_status_typedefs.svh"
   `include "src/soc_ifc_status_transaction.svh"

   `include "src/soc_ifc_status_configuration.svh"
   `include "src/soc_ifc_status_driver.svh"
   `include "src/soc_ifc_status_monitor.svh"

   `include "src/soc_ifc_status_transaction_coverage.svh"
   `include "src/soc_ifc_status_sequence_base.svh"
   `include "src/soc_ifc_status_random_sequence.svh"

   `include "src/soc_ifc_status_responder_sequence.svh"
   `include "src/soc_ifc_status2reg_adapter.svh"

   `include "src/soc_ifc_status_agent.svh"

   // pragma uvmf custom package_item_additional begin
   // UVMF_CHANGE_ME : When adding new interface sequences to the src directory
   //    be sure to add the sequence file here so that it will be
   //    compiled as part of the interface package.  Be sure to place
   //    the new sequence after any base sequences of the new sequence.
   typedef soc_ifc_status_sequence_base       soc_ifc_status_agent_seq_base_t;
   typedef soc_ifc_status_random_sequence     soc_ifc_status_agent_rand_seq_t;
   typedef soc_ifc_status_responder_sequence  soc_ifc_status_agent_responder_seq_t;
   // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

