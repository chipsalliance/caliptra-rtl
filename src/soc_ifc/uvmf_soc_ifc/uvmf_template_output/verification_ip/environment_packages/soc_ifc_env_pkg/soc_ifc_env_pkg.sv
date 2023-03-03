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
//     - <soc_ifc_configuration.svh>
//     - <soc_ifc_environment.svh>
//     - <soc_ifc_env_sequence_base.svh>
//     - <soc_ifc_predictor.svh>
//     - <soc_ifc_scoreboard.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package soc_ifc_env_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import uvmf_base_pkg::*;
  import mvc_pkg::*;
  import mgc_ahb_v2_0_pkg::*;
  import mgc_apb3_v1_0_pkg::*;
  import rw_txn_pkg::*;
  import soc_ifc_ctrl_pkg::*;
  import soc_ifc_ctrl_pkg_hdl::*;
  import cptra_ctrl_pkg::*;
  import cptra_ctrl_pkg_hdl::*;
  import soc_ifc_status_pkg::*;
  import soc_ifc_status_pkg_hdl::*;
  import cptra_status_pkg::*;
  import cptra_status_pkg_hdl::*;
  import soc_ifc_reg_model_top_pkg::*;
  import qvip_ahb_lite_slave_pkg::*;
  import qvip_ahb_lite_slave_params_pkg::*;
  import qvip_apb5_slave_pkg::*;
  import qvip_apb5_slave_params_pkg::*;
 
  `uvm_analysis_imp_decl(_soc_ifc_ctrl_agent_ae)
  `uvm_analysis_imp_decl(_cptra_ctrl_agent_ae)
  `uvm_analysis_imp_decl(_ahb_slave_0_ae)
  `uvm_analysis_imp_decl(_apb5_slave_0_ae)
  `uvm_analysis_imp_decl(_expected_analysis_export)
  `uvm_analysis_imp_decl(_expected_cptra_analysis_export)
  `uvm_analysis_imp_decl(_actual_analysis_export)
  `uvm_analysis_imp_decl(_actual_cptra_analysis_export)
  `uvm_analysis_imp_decl(_expected_ahb_analysis_export)
  `uvm_analysis_imp_decl(_expected_apb_analysis_export)
  `uvm_analysis_imp_decl(_actual_ahb_analysis_export)
  `uvm_analysis_imp_decl(_actual_apb_analysis_export)

  // pragma uvmf custom package_imports_additional begin
  import soc_ifc_pkg::*;
  // pragma uvmf custom package_imports_additional end

  // Parameters defined as HVL parameters

  `include "src/soc_ifc_env_typedefs.svh"
  `include "src/soc_ifc_env_configuration.svh"
  `include "src/soc_ifc_predictor.svh"
  `include "src/soc_ifc_scoreboard.svh"
  `include "src/soc_ifc_environment.svh"
  `include "src/soc_ifc_env_sequence_base.svh"

  // pragma uvmf custom package_item_additional begin
  typedef soc_ifc_env_configuration  soc_ifc_env_configuration_t;
  // UVMF_CHANGE_ME : When adding new environment level sequences to the src directory
  //    be sure to add the sequence file here so that it will be
  //    compiled as part of the environment package.  Be sure to place
  //    the new sequence after any base sequence of the new sequence.
  // TODO: Also declare the 'typedef'

  ///////////////////// Base Sequence - do not run /////////////////////
  typedef soc_ifc_env_sequence_base #( .CONFIG_T(soc_ifc_env_configuration_t)) soc_ifc_env_sequence_base_t;

  ///////////////////// Sequences usable from Caliptra_top /////////////////////
  `include "sequences/bringup/soc_ifc/soc_ifc_env_bringup_sequence.svh"
  typedef soc_ifc_env_bringup_sequence soc_ifc_env_bringup_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/bringup/soc_ifc/soc_ifc_env_pauser_init_sequence.svh"
  typedef soc_ifc_env_pauser_init_sequence soc_ifc_env_pauser_init_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/soc_ifc/soc_ifc_env_mbox_sequence_base.svh"
  typedef soc_ifc_env_mbox_sequence_base soc_ifc_env_mbox_sequence_base_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/soc_ifc/soc_ifc_env_mbox_rand_fw_sequence.svh"
  typedef soc_ifc_env_mbox_rand_fw_sequence soc_ifc_env_mbox_rand_fw_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/soc_ifc/soc_ifc_env_mbox_rand_small_sequence.svh"
  typedef soc_ifc_env_mbox_rand_small_sequence soc_ifc_env_mbox_rand_small_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/soc_ifc/soc_ifc_env_mbox_rand_medium_sequence.svh"
  typedef soc_ifc_env_mbox_rand_medium_sequence soc_ifc_env_mbox_rand_medium_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/soc_ifc/soc_ifc_env_mbox_rand_large_sequence.svh"
  typedef soc_ifc_env_mbox_rand_large_sequence soc_ifc_env_mbox_rand_large_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/soc_ifc/soc_ifc_env_mbox_rand_medium_interference_sequence.svh"
  typedef soc_ifc_env_mbox_rand_medium_interference_sequence soc_ifc_env_mbox_rand_medium_interference_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/soc_ifc/soc_ifc_env_mbox_rand_pauser_sequence.svh"
  typedef soc_ifc_env_mbox_rand_pauser_sequence soc_ifc_env_mbox_rand_pauser_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/soc_ifc/soc_ifc_env_mbox_rand_pauser_medium_sequence.svh"
  typedef soc_ifc_env_mbox_rand_pauser_medium_sequence soc_ifc_env_mbox_rand_pauser_medium_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */

  ///////////////////// Sequences usable from soc_ifc bench only /////////////////////
  // These sequences include stimulus for the internal/caliptra-side of the
  // soc_ifc, which is done by the uC in caliptra_top bench
  `include "sequences/bringup/cptra/soc_ifc_env_cptra_rst_wait_sequence.svh"
  typedef soc_ifc_env_cptra_rst_wait_sequence soc_ifc_env_cptra_rst_wait_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/cptra/soc_ifc_env_cptra_mbox_handler_sequence.svh"
  typedef soc_ifc_env_cptra_mbox_handler_sequence soc_ifc_env_cptra_mbox_handler_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/cptra/soc_ifc_env_cptra_mbox_interference_handler_sequence.svh"
  typedef soc_ifc_env_cptra_mbox_interference_handler_sequence soc_ifc_env_cptra_mbox_interference_handler_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/soc_ifc_env_top_mbox_sequence_base.svh"
  typedef soc_ifc_env_top_mbox_sequence_base soc_ifc_env_top_mbox_sequence_base_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/soc_ifc_env_top_mbox_rand_small_sequence.svh"
  typedef soc_ifc_env_top_mbox_rand_small_sequence soc_ifc_env_top_mbox_rand_small_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/soc_ifc_env_top_mbox_contention_sequence.svh"
  typedef soc_ifc_env_top_mbox_contention_sequence soc_ifc_env_top_mbox_contention_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */
  `include "sequences/mbox/soc_ifc_env_top_mbox_rand_pauser_sequence.svh"
  typedef soc_ifc_env_top_mbox_rand_pauser_sequence soc_ifc_env_top_mbox_rand_pauser_sequence_t;
  /* TODO: If desired in top-level rand sequence, add this to the rand_seq_idx enum/avail_env_seqs_c constraint */

  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

