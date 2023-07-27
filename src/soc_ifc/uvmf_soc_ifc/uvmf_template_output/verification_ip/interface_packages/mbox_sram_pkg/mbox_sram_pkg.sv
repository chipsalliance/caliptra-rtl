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
//    - <mbox_sram_typedefs_hdl>
//    - <mbox_sram_typedefs.svh>
//    - <mbox_sram_transaction.svh>

//    - <mbox_sram_configuration.svh>
//    - <mbox_sram_driver.svh>
//    - <mbox_sram_monitor.svh>

//    - <mbox_sram_transaction_coverage.svh>
//    - <mbox_sram_sequence_base.svh>
//    - <mbox_sram_random_sequence.svh>

//    - <mbox_sram_responder_sequence.svh>
//    - <mbox_sram2reg_adapter.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package mbox_sram_pkg;
  
   import uvm_pkg::*;
   import uvmf_base_pkg_hdl::*;
   import uvmf_base_pkg::*;
   import mbox_sram_pkg_hdl::*;

   `include "uvm_macros.svh"

   // pragma uvmf custom package_imports_additional begin 
   import soc_ifc_pkg::*;
   // pragma uvmf custom package_imports_additional end
   `include "src/mbox_sram_macros.svh"

   export mbox_sram_pkg_hdl::*;
   
 

   // Parameters defined as HVL parameters

   `include "src/mbox_sram_typedefs.svh"
   `include "src/mbox_sram_transaction.svh"

   `include "src/mbox_sram_configuration.svh"
   `include "src/mbox_sram_driver.svh"
   `include "src/mbox_sram_monitor.svh"

   `include "src/mbox_sram_transaction_coverage.svh"
   `include "src/mbox_sram_sequence_base.svh"
   `include "src/mbox_sram_random_sequence.svh"

   `include "src/mbox_sram_responder_sequence.svh"
   `include "src/mbox_sram2reg_adapter.svh"

   `include "src/mbox_sram_agent.svh"

   // pragma uvmf custom package_item_additional begin
   // UVMF_CHANGE_ME : When adding new interface sequences to the src directory
   //    be sure to add the sequence file here so that it will be
   //    compiled as part of the interface package.  Be sure to place
   //    the new sequence after any base sequences of the new sequence.
   typedef mbox_sram_responder_sequence mbox_sram_agent_responder_seq_t;
   // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

