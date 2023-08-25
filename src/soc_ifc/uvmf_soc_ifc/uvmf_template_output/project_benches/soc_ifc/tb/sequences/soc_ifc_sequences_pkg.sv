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
// DESCRIPTION: This package includes all high level sequence classes used 
//     in the environment.  These include utility sequences and top
//     level sequences.
//
// CONTAINS:
//     -<soc_ifc_sequence_base>
//     -<example_derived_test_sequence>
//
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
//

package soc_ifc_sequences_pkg;
  import uvm_pkg::*;
  import uvmf_base_pkg::*;
  import mvc_pkg::*;
  import mgc_ahb_v2_0_pkg::*;
  import mgc_apb3_v1_0_pkg::*;
  import soc_ifc_ctrl_pkg::*;
  import soc_ifc_ctrl_pkg_hdl::*;
  import cptra_ctrl_pkg::*;
  import cptra_ctrl_pkg_hdl::*;
  import soc_ifc_status_pkg::*;
  import soc_ifc_status_pkg_hdl::*;
  import cptra_status_pkg::*;
  import cptra_status_pkg_hdl::*;
  import mbox_sram_pkg::*;
  import mbox_sram_pkg_hdl::*;
  import soc_ifc_parameters_pkg::*;
  import soc_ifc_env_pkg::*;
  import qvip_ahb_lite_slave_params_pkg::*;
  import qvip_apb5_slave_params_pkg::*;
  import soc_ifc_reg_model_top_pkg::*;
  `include "uvm_macros.svh"

  // pragma uvmf custom package_imports_additional begin
  // pragma uvmf custom package_imports_additional end

  `include "src/soc_ifc_bench_sequence_base.svh"
  `include "src/register_test_sequence.svh"
  `include "src/example_derived_test_sequence.svh"

  // pragma uvmf custom package_item_additional begin
  // UVMF_CHANGE_ME : When adding new sequences to the src directory
  //    be sure to add the sequence file here so that it will be
  //    compiled as part of the sequence package.  Be sure to place
  //    the new sequence after any base sequences of the new sequence.
  `include "src/soc_ifc_rand_test_sequence.svh"
  `include "src/soc_ifc_cmdline_test_sequence.svh"
  `include "src/soc_ifc_trng_test_sequence.svh"
  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

