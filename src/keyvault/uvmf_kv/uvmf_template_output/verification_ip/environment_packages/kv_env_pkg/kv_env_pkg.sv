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
 
  `uvm_analysis_imp_decl(_kv_rst_agent_ae)
  `uvm_analysis_imp_decl(_kv_hmac_write_agent_ae)
  `uvm_analysis_imp_decl(_kv_sha512_write_agent_ae)
  `uvm_analysis_imp_decl(_kv_ecc_write_agent_ae)
  `uvm_analysis_imp_decl(_kv_doe_write_agent_ae)
  `uvm_analysis_imp_decl(_kv_hmac_key_read_agent_ae)
  `uvm_analysis_imp_decl(_kv_hmac_block_read_agent_ae)
  `uvm_analysis_imp_decl(_kv_hmac_sha512_read_agent_ae)
  `uvm_analysis_imp_decl(_kv_hmac_ecc_privkey_read_agent_ae)
  `uvm_analysis_imp_decl(_kv_ecc_seed_read_agent_ae)
  `uvm_analysis_imp_decl(_kv_ecc_msg_read_agent_ae)
  `uvm_analysis_imp_decl(_ahb_slave_0_ae)

  // pragma uvmf custom package_imports_additional begin
  // pragma uvmf custom package_imports_additional end

  // Parameters defined as HVL parameters

  `include "src/kv_env_typedefs.svh"
  `include "src/kv_env_configuration.svh"
  `include "src/kv_predictor.svh"
  `include "src/kv_environment.svh"
  `include "src/kv_env_sequence_base.svh"

  // pragma uvmf custom package_item_additional begin
  // UVMF_CHANGE_ME : When adding new environment level sequences to the src directory
  //    be sure to add the sequence file here so that it will be
  //    compiled as part of the environment package.  Be sure to place
  //    the new sequence after any base sequence of the new sequence.
  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

