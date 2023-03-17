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
//     - <pv_configuration.svh>
//     - <pv_environment.svh>
//     - <pv_env_sequence_base.svh>
//     - <pv_predictor.svh>
//     - <pv_scoreboard.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package pv_env_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import uvmf_base_pkg::*;
  import mvc_pkg::*;
  import mgc_ahb_v2_0_pkg::*;
  import rw_txn_pkg::*;
  import pv_rst_pkg::*;
  import pv_rst_pkg_hdl::*;
  import pv_write_pkg::*;
  import pv_write_pkg_hdl::*;
  import pv_read_pkg::*;
  import pv_read_pkg_hdl::*;
  import pv_reg_model_top_pkg::*;
  import qvip_ahb_lite_slave_pkg::*;
  import qvip_ahb_lite_slave_params_pkg::*;
  import pv_defines_pkg::*;
 
  `uvm_analysis_imp_decl(_pv_rst_agent_ae)
  `uvm_analysis_imp_decl(_pv_sha512_write_agent_ae)
  `uvm_analysis_imp_decl(_pv_sha512_block_read_agent_ae)
  `uvm_analysis_imp_decl(_ahb_slave_0_ae)
  `uvm_analysis_imp_decl(_expected_sha512_write_analysis_export)
  `uvm_analysis_imp_decl(_actual_sha512_write_analysis_export)
  `uvm_analysis_imp_decl(_expected_sha512_block_read_analysis_export)
  `uvm_analysis_imp_decl(_actual_sha512_block_read_analysis_export)
  `uvm_analysis_imp_decl(_expected_ahb_analysis_export)
  `uvm_analysis_imp_decl(_actual_ahb_analysis_export)

  // pragma uvmf custom package_imports_additional begin
  // pragma uvmf custom package_imports_additional end

  // Parameters defined as HVL parameters

  `include "src/pv_env_typedefs.svh"
  `include "src/pv_env_configuration.svh"
  `include "src/pv_predictor.svh"
  `include "src/pv_reg_predictor.svh"
  `include "src/pv_ahb_reg_predictor.svh"
  `include "src/pv_scoreboard.svh"
  `include "src/pv_environment.svh"
  `include "src/pv_env_sequence_base.svh"
  `include "src/pv_pcr_wr_rd_basic_sequence.svh"
  `include "src/pv_wr_rd_cold_rst_sequence.svh"
  `include "src/pv_wr_rd_lock_cold_rst_sequence.svh"
  `include "src/pv_wr_rd_lock_warm_rst_sequence.svh"
  `include "src/pv_wr_rd_lock_sequence.svh"
  `include "src/pv_wr_rd_ahb_sequence.svh"
  `include "src/pv_wr_rd_rst_sequence.svh"
  `include "src/pv_wr_rd_sequence.svh"

  // pragma uvmf custom package_item_additional begin
  // UVMF_CHANGE_ME : When adding new environment level sequences to the src directory
  //    be sure to add the sequence file here so that it will be
  //    compiled as part of the environment package.  Be sure to place
  //    the new sequence after any base sequence of the new sequence.
  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

