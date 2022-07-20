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
//    - <AES_in_typedefs_hdl>
//    - <AES_in_typedefs.svh>
//    - <AES_in_transaction.svh>

//    - <AES_in_configuration.svh>
//    - <AES_in_driver.svh>
//    - <AES_in_monitor.svh>

//    - <AES_in_transaction_coverage.svh>
//    - <AES_in_sequence_base.svh>
//    - <AES_in_random_sequence.svh>

//    - <AES_in_responder_sequence.svh>
//    - <AES_in2reg_adapter.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package AES_in_pkg;
  
   import uvm_pkg::*;
   import uvmf_base_pkg_hdl::*;
   import uvmf_base_pkg::*;
   import AES_in_pkg_hdl::*;

   `include "uvm_macros.svh"

   // pragma uvmf custom package_imports_additional begin 
   // pragma uvmf custom package_imports_additional end
   `include "src/AES_in_macros.svh"

   export AES_in_pkg_hdl::*;
   
 

   // Parameters defined as HVL parameters

   `include "src/AES_in_typedefs.svh"
   `include "src/AES_in_transaction.svh"

   `include "src/AES_in_configuration.svh"
   `include "src/AES_in_driver.svh"
   `include "src/AES_in_monitor.svh"

   `include "src/AES_in_transaction_coverage.svh"
   `include "src/AES_in_sequence_base.svh"
   `include "src/AES_in_random_sequence.svh"
   `include "src/AES_in_reset_sequence.svh"

   `include "src/AES_in_responder_sequence.svh"
   `include "src/AES_in2reg_adapter.svh"

   `include "src/AES_in_agent.svh"

   // pragma uvmf custom package_item_additional begin
   // UVMF_CHANGE_ME : When adding new interface sequences to the src directory
   //    be sure to add the sequence file here so that it will be
   //    compiled as part of the interface package.  Be sure to place
   //    the new sequence after any base sequences of the new sequence.
   // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

