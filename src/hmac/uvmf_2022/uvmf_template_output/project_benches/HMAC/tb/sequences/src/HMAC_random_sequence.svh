// ==============================================================================
// =====            Mentor Graphics UK Ltd                                  =====
// =====            Rivergate, London Road, Newbury BERKS RG14 2QB          =====
// ==============================================================================
// ==============================================================================
// This unpublished work contains proprietary information.
// All right reserved. Supplied in confidence and must not be copied, used or disclosed 
// for any purpose without express written permission.
// 2019 @ Copyright Mentor Graphics UK Ltd
// ==============================================================================


`ifndef __HMAC_RANDOM_SEQUENCE
`define __HMAC_RANDOM_SEQUENCE

`include "uvm_macros.svh"

class HMAC_random_sequence #(int AHB_DATA_WIDTH = 32,
                            int AHB_ADDR_WIDTH = 32,
                            bit BYPASS_HSEL = 0
                            ) extends HMAC_bench_sequence_base;

  `uvm_object_utils(HMAC_random_sequence) 

  // Define type and handle for reset sequence
  typedef HMAC_in_reset_sequence #(AHB_DATA_WIDTH, AHB_ADDR_WIDTH, BYPASS_HSEL) HMAC_in_reset_sequence_t;
  HMAC_in_reset_sequence_t HMAC_in_reset_s;
  
  // constructor
  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual task body();
    HMAC_in_agent_random_seq = HMAC_in_random_sequence#()::type_id::create("HMAC_in_agent_random_seq");
    HMAC_in_reset_s = HMAC_in_reset_sequence#()::type_id::create("HMAC_in_reset_s");
    
    HMAC_in_agent_config.wait_for_reset();
    HMAC_in_agent_config.wait_for_num_clocks(10);

    repeat (10) HMAC_in_agent_random_seq.start(HMAC_in_agent_sequencer);
    HMAC_in_reset_s.start(HMAC_in_agent_sequencer);
    repeat (5) HMAC_in_agent_random_seq.start(HMAC_in_agent_sequencer);

    HMAC_in_agent_config.wait_for_num_clocks(50);    
    
    if (1) // TODO -- how to properly choose which to print?
        $display("* TESTCASE PASSED");
    else
        $display("* TESTCASE FAILED");
  endtask


endclass : HMAC_random_sequence

`endif
