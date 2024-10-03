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
//    environment package that will run on the host simulator.
//
// CONTAINS:
//     - <fuse_ctrl_configuration.svh>
//     - <fuse_ctrl_environment.svh>
//     - <fuse_ctrl_env_sequence_base.svh>
//     - <fuse_ctrl_predictor.svh>
//     - <fuse_ctrl_scoreboard.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package fuse_ctrl_env_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import uvmf_base_pkg::*;
  import fuse_ctrl_rst_pkg::*;
  import fuse_ctrl_rst_pkg_hdl::*;
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
 
  `uvm_analysis_imp_decl(_fuse_ctrl_rst_agent_ae)
  `uvm_analysis_imp_decl(_fuse_ctrl_core_axi_write_agent_ae)
  `uvm_analysis_imp_decl(_fuse_ctrl_prim_axi_write_agent_ae)
  `uvm_analysis_imp_decl(_fuse_ctrl_core_axi_read_agent_ae)
  `uvm_analysis_imp_decl(_fuse_ctrl_prim_axi_read_agent_ae)
  `uvm_analysis_imp_decl(_fuse_ctrl_secreg_axi_read_agent_ae)
  `uvm_analysis_imp_decl(_fuse_ctrl_lc_otp_if_agent_ae)
  `uvm_analysis_imp_decl(_expected_analysis_export)
  `uvm_analysis_imp_decl(_actual_analysis_export)

  // pragma uvmf custom package_imports_additional begin
  // pragma uvmf custom package_imports_additional end

  // Parameters defined as HVL parameters

  `include "src/fuse_ctrl_env_typedefs.svh"
  `include "src/fuse_ctrl_env_configuration.svh"
  `include "src/fuse_ctrl_predictor.svh"
  `include "src/fuse_ctrl_scoreboard.svh"
  `include "src/fuse_ctrl_environment.svh"
  `include "src/fuse_ctrl_env_sequence_base.svh"

  // pragma uvmf custom package_item_additional begin
  // UVMF_CHANGE_ME : When adding new environment level sequences to the src directory
  //    be sure to add the sequence file here so that it will be
  //    compiled as part of the environment package.  Be sure to place
  //    the new sequence after any base sequence of the new sequence.
  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

