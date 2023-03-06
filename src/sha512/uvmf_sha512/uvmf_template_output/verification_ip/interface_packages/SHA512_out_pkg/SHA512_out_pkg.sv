//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// PACKAGE: This file defines all of the files contained in the
//    interface package that will run on the host simulator.
//
// CONTAINS:
//    - <SHA512_out_typedefs_hdl>
//    - <SHA512_out_typedefs.svh>
//    - <SHA512_out_transaction.svh>

//    - <SHA512_out_configuration.svh>
//    - <SHA512_out_driver.svh>
//    - <SHA512_out_monitor.svh>

//    - <SHA512_out_transaction_coverage.svh>
//    - <SHA512_out_sequence_base.svh>
//    - <SHA512_out_random_sequence.svh>

//    - <SHA512_out_responder_sequence.svh>
//    - <SHA512_out2reg_adapter.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package SHA512_out_pkg;
  
   import uvm_pkg::*;
   import uvmf_base_pkg_hdl::*;
   import uvmf_base_pkg::*;
   import SHA512_out_pkg_hdl::*;

   `include "uvm_macros.svh"

   // pragma uvmf custom package_imports_additional begin 
   // pragma uvmf custom package_imports_additional end
   `include "src/SHA512_out_macros.svh"

   export SHA512_out_pkg_hdl::*;
   
 

   // Parameters defined as HVL parameters

   `include "src/SHA512_out_typedefs.svh"
   `include "src/SHA512_out_transaction.svh"

   `include "src/SHA512_out_configuration.svh"
   `include "src/SHA512_out_driver.svh"
   `include "src/SHA512_out_monitor.svh"

   `include "src/SHA512_out_transaction_coverage.svh"
   `include "src/SHA512_out_sequence_base.svh"
   `include "src/SHA512_out_random_sequence.svh"

   `include "src/SHA512_out_responder_sequence.svh"
   `include "src/SHA512_out2reg_adapter.svh"

   `include "src/SHA512_out_agent.svh"

   // pragma uvmf custom package_item_additional begin
   // UVMF_CHANGE_ME : When adding new interface sequences to the src directory
   //    be sure to add the sequence file here so that it will be
   //    compiled as part of the interface package.  Be sure to place
   //    the new sequence after any base sequences of the new sequence.
   // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

