//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// PACKAGE: This file defines all of the files contained in the
//    environment package that will run on the host simulator.
//
// CONTAINS:
//     - <SHA512_configuration.svh>
//     - <SHA512_environment.svh>
//     - <SHA512_env_sequence_base.svh>
//     - <SHA512_predictor.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package SHA512_env_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import uvmf_base_pkg::*;
  import SHA512_in_pkg::*;
  import SHA512_in_pkg_hdl::*;
  import SHA512_out_pkg::*;
  import SHA512_out_pkg_hdl::*;
 
  `uvm_analysis_imp_decl(_SHA512_in_agent_ae)

  // pragma uvmf custom package_imports_additional begin
  // pragma uvmf custom package_imports_additional end

  // Parameters defined as HVL parameters

  `include "src/SHA512_env_typedefs.svh"
  `include "src/SHA512_env_configuration.svh"
  `include "src/SHA512_predictor.svh"
  `include "src/SHA512_environment.svh"
  `include "src/SHA512_env_sequence_base.svh"

  // pragma uvmf custom package_item_additional begin
  // UVMF_CHANGE_ME : When adding new environment level sequences to the src directory
  //    be sure to add the sequence file here so that it will be
  //    compiled as part of the environment package.  Be sure to place
  //    the new sequence after any base sequence of the new sequence.
  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

