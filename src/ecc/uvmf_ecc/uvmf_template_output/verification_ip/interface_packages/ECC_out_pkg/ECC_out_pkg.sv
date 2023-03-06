//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
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
//    - <ECC_out_typedefs_hdl>
//    - <ECC_out_typedefs.svh>
//    - <ECC_out_transaction.svh>

//    - <ECC_out_configuration.svh>
//    - <ECC_out_driver.svh>
//    - <ECC_out_monitor.svh>

//    - <ECC_out_transaction_coverage.svh>
//    - <ECC_out_sequence_base.svh>
//    - <ECC_out_random_sequence.svh>

//    - <ECC_out_responder_sequence.svh>
//    - <ECC_out2reg_adapter.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package ECC_out_pkg;
  
   import uvm_pkg::*;
   import uvmf_base_pkg_hdl::*;
   import uvmf_base_pkg::*;
   import ECC_out_pkg_hdl::*;

   `include "uvm_macros.svh"

   // pragma uvmf custom package_imports_additional begin 
   // pragma uvmf custom package_imports_additional end
   `include "src/ECC_out_macros.svh"

   export ECC_out_pkg_hdl::*;
   
 

   // Parameters defined as HVL parameters

   `include "src/ECC_out_typedefs.svh"
   `include "src/ECC_out_transaction.svh"

   `include "src/ECC_out_configuration.svh"
   `include "src/ECC_out_driver.svh"
   `include "src/ECC_out_monitor.svh"

   `include "src/ECC_out_transaction_coverage.svh"
   `include "src/ECC_out_sequence_base.svh"
   `include "src/ECC_out_random_sequence.svh"

   `include "src/ECC_out_responder_sequence.svh"
   `include "src/ECC_out2reg_adapter.svh"

   `include "src/ECC_out_agent.svh"

   // pragma uvmf custom package_item_additional begin
   // UVMF_CHANGE_ME : When adding new interface sequences to the src directory
   //    be sure to add the sequence file here so that it will be
   //    compiled as part of the interface package.  Be sure to place
   //    the new sequence after any base sequences of the new sequence.
   // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

