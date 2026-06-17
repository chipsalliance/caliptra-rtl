// ==============================================================================
// =====            Mentor Graphics UK Ltd                                  =====
// =====            Rivergate, London Road, Newbury BERKS RG14 2QB          =====
// ==============================================================================
//! @file
//  Project                : HMAC_2019_4
//  Unit                   : HMAC_last_alone_error_test
//! @brief  Directed test that exercises the LAST-alone CTRL write so the
//!         hmac.last_alone_error path raises error2_sts and the
//!         last_alone_ignored covergroup bin gets hit.
//-------------------------------------------------------------------------------
//-------------------------------------------------------------------------------
// ==============================================================================
// This unpublished work contains proprietary information.
// All right reserved. Supplied in confidence and must not be copied, used or disclosed
// for any purpose without express written permission.
// 2019 @ Copyright Mentor Graphics UK Ltd
// ==============================================================================


`ifndef __HMAC_LAST_ALONE_ERROR_TEST
`define __HMAC_LAST_ALONE_ERROR_TEST

`include "uvm_macros.svh"

class HMAC_last_alone_error_test extends test_top;

  `uvm_component_utils(HMAC_last_alone_error_test)

  // constructor
  function new(string name = "", uvm_component parent = null );
    super.new(name, parent);
  endfunction : new


  virtual function void build_phase(uvm_phase phase );
    // UVM Factory override. Override HMAC_bench_sequence_base with HMAC_last_alone_error_sequence
    HMAC_bench_sequence_base::type_id::set_type_override(HMAC_last_alone_error_sequence #(64,32,0)::get_type());
    super.build_phase(phase);
  endfunction : build_phase

endclass : HMAC_last_alone_error_test

`endif
