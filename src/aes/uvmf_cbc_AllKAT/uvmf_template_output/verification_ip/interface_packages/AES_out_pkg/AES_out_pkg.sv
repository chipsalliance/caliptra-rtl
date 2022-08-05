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
//    - <AES_out_typedefs_hdl>
//    - <AES_out_typedefs.svh>
//    - <AES_out_transaction.svh>

//    - <AES_out_configuration.svh>
//    - <AES_out_driver.svh>
//    - <AES_out_monitor.svh>

//    - <AES_out_transaction_coverage.svh>
//    - <AES_out_sequence_base.svh>
//    - <AES_out_random_sequence.svh>

//    - <AES_out_responder_sequence.svh>
//    - <AES_out2reg_adapter.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package AES_out_pkg;
  
   import uvm_pkg::*;
   import uvmf_base_pkg_hdl::*;
   import uvmf_base_pkg::*;
   import AES_out_pkg_hdl::*;

   `include "uvm_macros.svh"

   // pragma uvmf custom package_imports_additional begin 
   // pragma uvmf custom package_imports_additional end
   `include "src/AES_out_macros.svh"

   export AES_out_pkg_hdl::*;
   
 

   // Parameters defined as HVL parameters

   `include "src/AES_out_typedefs.svh"
   `include "src/AES_out_transaction.svh"

   `include "src/AES_out_configuration.svh"
   `include "src/AES_out_driver.svh"
   `include "src/AES_out_monitor.svh"

   `include "src/AES_out_transaction_coverage.svh"
   `include "src/AES_out_sequence_base.svh"
   `include "src/AES_out_random_sequence.svh"

   `include "src/AES_out_responder_sequence.svh"
   `include "src/AES_out2reg_adapter.svh"

   `include "src/AES_out_agent.svh"

   // pragma uvmf custom package_item_additional begin
   // UVMF_CHANGE_ME : When adding new interface sequences to the src directory
   //    be sure to add the sequence file here so that it will be
   //    compiled as part of the interface package.  Be sure to place
   //    the new sequence after any base sequences of the new sequence.
   // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

