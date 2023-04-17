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

package soc_ifc_tests_pkg;

   import uvm_pkg::*;
   import uvmf_base_pkg::*;
   import soc_ifc_parameters_pkg::*;
   import soc_ifc_env_pkg::*;
   import soc_ifc_sequences_pkg::*;
   import soc_ifc_ctrl_pkg::*;
   import soc_ifc_ctrl_pkg_hdl::*;
   import cptra_ctrl_pkg::*;
   import cptra_ctrl_pkg_hdl::*;
   import soc_ifc_status_pkg::*;
   import soc_ifc_status_pkg_hdl::*;
   import cptra_status_pkg::*;
   import cptra_status_pkg_hdl::*;
   import qvip_ahb_lite_slave_pkg::*;
   import qvip_apb5_slave_pkg::*;
   import QUESTA_MVC::*;
   import qvip_utils_pkg::*;
   import mvc_pkg::*;
   import mgc_ahb_v2_0_pkg::*;
   import mgc_apb3_v1_0_pkg::*;


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
   `include "src/soc_ifc_rand_test.svh"
   `include "src/soc_ifc_cmdline_test.svh"
   `include "src/soc_ifc_trng_test.svh"
  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

