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
//     - <kv_configuration.svh>
//     - <kv_environment.svh>
//     - <kv_env_sequence_base.svh>
//     - <kv_predictor.svh>
//     - <kv_scoreboard.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package kv_env_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import uvmf_base_pkg::*;
  import mvc_pkg::*;
  import mgc_ahb_v2_0_pkg::*;
  import rw_txn_pkg::*;
  import kv_rst_pkg::*;
  import kv_rst_pkg_hdl::*;
  import kv_write_pkg::*;
  import kv_write_pkg_hdl::*;
  import kv_read_pkg::*;
  import kv_read_pkg_hdl::*;
  import kv_reg_model_top_pkg::*;
  import qvip_ahb_lite_slave_pkg::*;
  import qvip_ahb_lite_slave_params_pkg::*;
  import kv_defines_pkg::*;
 
  `uvm_analysis_imp_decl(_kv_rst_agent_ae)
  `uvm_analysis_imp_decl(_kv_hmac_write_agent_ae)
  `uvm_analysis_imp_decl(_kv_sha512_write_agent_ae)
  `uvm_analysis_imp_decl(_kv_ecc_write_agent_ae)
  `uvm_analysis_imp_decl(_kv_doe_write_agent_ae)
  `uvm_analysis_imp_decl(_kv_hmac_key_read_agent_ae)
  `uvm_analysis_imp_decl(_kv_hmac_block_read_agent_ae)
  `uvm_analysis_imp_decl(_kv_sha512_block_read_agent_ae)
  `uvm_analysis_imp_decl(_kv_ecc_privkey_read_agent_ae)
  `uvm_analysis_imp_decl(_kv_ecc_seed_read_agent_ae)
  `uvm_analysis_imp_decl(_ahb_slave_0_ae)
  // `uvm_analysis_imp_decl(_expected_analysis_export)
  // `uvm_analysis_imp_decl(_actual_analysis_export)
  `uvm_analysis_imp_decl(_expected_hmac_write_analysis_export)
  `uvm_analysis_imp_decl(_actual_hmac_write_analysis_export)

  `uvm_analysis_imp_decl(_expected_sha512_write_analysis_export)
  `uvm_analysis_imp_decl(_actual_sha512_write_analysis_export)

  `uvm_analysis_imp_decl(_expected_ecc_write_analysis_export)
  `uvm_analysis_imp_decl(_actual_ecc_write_analysis_export)

  `uvm_analysis_imp_decl(_expected_doe_write_analysis_export)
  `uvm_analysis_imp_decl(_actual_doe_write_analysis_export)

  `uvm_analysis_imp_decl(_expected_hmac_key_read_analysis_export)
  `uvm_analysis_imp_decl(_actual_hmac_key_read_analysis_export)

  `uvm_analysis_imp_decl(_expected_hmac_block_read_analysis_export)
  `uvm_analysis_imp_decl(_actual_hmac_block_read_analysis_export)

  `uvm_analysis_imp_decl(_expected_sha512_block_read_analysis_export)
  `uvm_analysis_imp_decl(_actual_sha512_block_read_analysis_export)

  `uvm_analysis_imp_decl(_expected_ecc_privkey_read_analysis_export)
  `uvm_analysis_imp_decl(_actual_ecc_privkey_read_analysis_export)

  `uvm_analysis_imp_decl(_expected_ecc_seed_read_analysis_export)
  `uvm_analysis_imp_decl(_actual_ecc_seed_read_analysis_export)

  `uvm_analysis_imp_decl(_expected_ahb_analysis_export)
  `uvm_analysis_imp_decl(_actual_ahb_analysis_export)

  // pragma uvmf custom package_imports_additional begin
  // pragma uvmf custom package_imports_additional end

  // Parameters defined as HVL parameters

  `include "src/kv_env_typedefs.svh"
  `include "src/kv_env_configuration.svh"
  `include "src/kv_predictor.svh"
  `include "src/kv_reg_predictor.svh"
  `include "src/kv_scoreboard.svh"
  `include "src/kv_environment.svh"
  `include "src/kv_env_sequence_base.svh"
  `include "src/kv_ahb_sequence.svh"
  `include "src/kv_wr_rd_sequence.svh"
  `include "src/kv_wr_rd_rst_sequence.svh"
  `include "src/kv_wr_rd_cold_rst_sequence.svh"
  `include "src/kv_key_wr_rd_basic_sequence.svh"
  `include "src/kv_wr_rd_lock_sequence.svh"
  `include "src/kv_wr_rd_lock_warm_rst_sequence.svh"
  `include "src/kv_wr_rd_lock_cold_rst_sequence.svh"
  `include "src/kv_wr_rd_lock_core_rst_sequence.svh"
  `include "src/kv_wr_rd_debug_sequence.svh"
  `include "src/kv_env_debug_on_sequence.svh"
  `include "src/kv_env_debug_off_sequence.svh"
  `include "src/kv_wr_rd_debug_lock_sequence.svh"
  `include "src/kv_wr_rd_debug_lock_clear_rst_sequence.svh"
  `include "src/kv_wr_rd_debug_warm_rst_sequence.svh"
  `include "src/kv_wr_rd_debug_cold_rst_sequence.svh"
  `include "src/kv_wr_rd_debug_core_rst_sequence.svh"

  // pragma uvmf custom package_item_additional begin
  // UVMF_CHANGE_ME : When adding new environment level sequences to the src directory
  //    be sure to add the sequence file here so that it will be
  //    compiled as part of the environment package.  Be sure to place
  //    the new sequence after any base sequence of the new sequence.
  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

