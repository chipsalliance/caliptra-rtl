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

package HMAC256_tests_pkg;

   import uvm_pkg::*;
   import uvmf_base_pkg::*;
   import HMAC256_parameters_pkg::*;
   import HMAC256_env_pkg::*;
   import HMAC256_sequences_pkg::*;
   import HMAC256_rst_pkg::*;
   import HMAC256_rst_pkg_hdl::*;
   import qvip_ahb_lite_slave_pkg::*;
   import QUESTA_MVC::*;
   import qvip_utils_pkg::*;
   import mvc_pkg::*;
   import mgc_ahb_v2_0_pkg::*;


   `include "uvm_macros.svh"

  // pragma uvmf custom package_imports_additional begin 
  // pragma uvmf custom package_imports_additional end

   `include "src/test_top.svh"
   `include "src/register_test.svh"
   `include "src/example_derived_test.svh"

  // pragma uvmf custom package_item_additional begin
  `include "src/HMAC256_random_test.svh"
  `include "src/HMAC256_otf_reset_test.svh"
  `include "src/HMAC256_invalid_cmd_error_test.svh"
  `include "src/HMAC256_save_restore_test.svh"
  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

