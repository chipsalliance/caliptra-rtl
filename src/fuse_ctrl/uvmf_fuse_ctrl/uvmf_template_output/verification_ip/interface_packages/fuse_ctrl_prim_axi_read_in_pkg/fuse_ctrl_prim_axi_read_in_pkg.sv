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
//    - <fuse_ctrl_prim_axi_read_in_typedefs_hdl>
//    - <fuse_ctrl_prim_axi_read_in_typedefs.svh>
//    - <fuse_ctrl_prim_axi_read_in_transaction.svh>

//    - <fuse_ctrl_prim_axi_read_in_configuration.svh>
//    - <fuse_ctrl_prim_axi_read_in_driver.svh>
//    - <fuse_ctrl_prim_axi_read_in_monitor.svh>

//    - <fuse_ctrl_prim_axi_read_in_transaction_coverage.svh>
//    - <fuse_ctrl_prim_axi_read_in_sequence_base.svh>
//    - <fuse_ctrl_prim_axi_read_in_random_sequence.svh>

//    - <fuse_ctrl_prim_axi_read_in_responder_sequence.svh>
//    - <fuse_ctrl_prim_axi_read_in2reg_adapter.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package fuse_ctrl_prim_axi_read_in_pkg;
  
   import uvm_pkg::*;
   import uvmf_base_pkg_hdl::*;
   import uvmf_base_pkg::*;
   import fuse_ctrl_prim_axi_read_in_pkg_hdl::*;

   `include "uvm_macros.svh"

   // pragma uvmf custom package_imports_additional begin 
   // pragma uvmf custom package_imports_additional end
   `include "src/fuse_ctrl_prim_axi_read_in_macros.svh"

   export fuse_ctrl_prim_axi_read_in_pkg_hdl::*;
   
 

   // Parameters defined as HVL parameters

   `include "src/fuse_ctrl_prim_axi_read_in_typedefs.svh"
   `include "src/fuse_ctrl_prim_axi_read_in_transaction.svh"

   `include "src/fuse_ctrl_prim_axi_read_in_configuration.svh"
   `include "src/fuse_ctrl_prim_axi_read_in_driver.svh"
   `include "src/fuse_ctrl_prim_axi_read_in_monitor.svh"

   `include "src/fuse_ctrl_prim_axi_read_in_transaction_coverage.svh"
   `include "src/fuse_ctrl_prim_axi_read_in_sequence_base.svh"
   `include "src/fuse_ctrl_prim_axi_read_in_random_sequence.svh"

   `include "src/fuse_ctrl_prim_axi_read_in_responder_sequence.svh"
   `include "src/fuse_ctrl_prim_axi_read_in2reg_adapter.svh"

   `include "src/fuse_ctrl_prim_axi_read_in_agent.svh"

   // pragma uvmf custom package_item_additional begin
   // UVMF_CHANGE_ME : When adding new interface sequences to the src directory
   //    be sure to add the sequence file here so that it will be
   //    compiled as part of the interface package.  Be sure to place
   //    the new sequence after any base sequences of the new sequence.
   // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

