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
// DESCRIPTION: This package contains all tests currently written for
//     the simulation project.  Once compiled, any test can be selected
//     from the vsim command line using +UVM_TESTNAME=yourTestNameHere
//
// CONTAINS:
//     -<test_top>
//     -<example_derived_test>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

package fuse_ctrl_tests_pkg;

   import uvm_pkg::*;
   import uvmf_base_pkg::*;
   import fuse_ctrl_parameters_pkg::*;
   import fuse_ctrl_env_pkg::*;
   import fuse_ctrl_sequences_pkg::*;
   import fuse_ctrl_rst_in_pkg::*;
   import fuse_ctrl_rst_in_pkg_hdl::*;
   import fuse_ctrl_rst_out_pkg::*;
   import fuse_ctrl_rst_out_pkg_hdl::*;
   import fuse_ctrl_core_axi_write_in_pkg::*;
   import fuse_ctrl_core_axi_write_in_pkg_hdl::*;
   import fuse_ctrl_core_axi_write_out_pkg::*;
   import fuse_ctrl_core_axi_write_out_pkg_hdl::*;
   import fuse_ctrl_prim_axi_write_in_pkg::*;
   import fuse_ctrl_prim_axi_write_in_pkg_hdl::*;
   import fuse_ctrl_prim_axi_write_out_pkg::*;
   import fuse_ctrl_prim_axi_write_out_pkg_hdl::*;
   import fuse_ctrl_core_axi_read_in_pkg::*;
   import fuse_ctrl_core_axi_read_in_pkg_hdl::*;
   import fuse_ctrl_core_axi_read_out_pkg::*;
   import fuse_ctrl_core_axi_read_out_pkg_hdl::*;
   import fuse_ctrl_prim_axi_read_in_pkg::*;
   import fuse_ctrl_prim_axi_read_in_pkg_hdl::*;
   import fuse_ctrl_prim_axi_read_out_pkg::*;
   import fuse_ctrl_prim_axi_read_out_pkg_hdl::*;
   import fuse_ctrl_secreg_axi_read_in_pkg::*;
   import fuse_ctrl_secreg_axi_read_in_pkg_hdl::*;
   import fuse_ctrl_secreg_axi_read_out_pkg::*;
   import fuse_ctrl_secreg_axi_read_out_pkg_hdl::*;
   import fuse_ctrl_lc_otp_in_pkg::*;
   import fuse_ctrl_lc_otp_in_pkg_hdl::*;
   import fuse_ctrl_lc_otp_out_pkg::*;
   import fuse_ctrl_lc_otp_out_pkg_hdl::*;
   import fuse_ctrl_in_pkg::*;
   import fuse_ctrl_in_pkg_hdl::*;
   import fuse_ctrl_out_pkg::*;
   import fuse_ctrl_out_pkg_hdl::*;


   `include "uvm_macros.svh"

  // pragma uvmf custom package_imports_additional begin 
  // pragma uvmf custom package_imports_additional end

   `include "src/test_top.svh"
   `include "src/register_test.svh"
   `include "src/example_derived_test.svh"

  // pragma uvmf custom package_item_additional begin
  // UVMF_CHANGE_ME : When adding new tests to the src directory
  //    be sure to add the test file here so that it will be
  //    compiled as part of the test package.  Be sure to place
  //    the new test after any base tests of the new test.
  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

