// ==============================================================================
// =====            Mentor Graphics UK Ltd                                  =====
// =====            Rivergate, London Road, Newbury BERKS RG14 2QB          =====
// ==============================================================================
//! @file
//  Project                : AES_2019_4
//  Unit                   : AES_random_sequence
//! @brief  Add Class Description Here... 
//-------------------------------------------------------------------------------
//  Created by             : graemej
//  Creation Date          : 2019/09/10
//-------------------------------------------------------------------------------
// Revision History:
//  URL of HEAD            : $HeadURL$
//  Revision of last commit: $Rev$  
//  Author of last commit  : $Author$
//  Date of last commit    : $Date$  
//
// ==============================================================================
// This unpublished work contains proprietary information.
// All right reserved. Supplied in confidence and must not be copied, used or disclosed 
// for any purpose without express written permission.
// 2019 @ Copyright Mentor Graphics UK Ltd
// ==============================================================================


`ifndef __AES_RANDOM_SEQUENCE
`define __AES_RANDOM_SEQUENCE

`include "uvm_macros.svh"

class AES_random_sequence #(int AHB_DATA_WIDTH = 32,
                            int AHB_ADDR_WIDTH = 32,
                            bit BYPASS_HSEL = 0
                            ) extends AES_bench_sequence_base;

  `uvm_object_utils(AES_random_sequence) 

  // Define type and handle for reset sequence
  typedef AES_in_reset_sequence #(AHB_DATA_WIDTH, AHB_ADDR_WIDTH, BYPASS_HSEL) AES_in_reset_sequence_t;
  AES_in_reset_sequence_t AES_in_reset_s;
  
  // constructor
  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual task body();
    AES_in_agent_random_seq = AES_in_random_sequence#()::type_id::create("AES_in_agent_random_seq");
    AES_in_reset_s = AES_in_reset_sequence#()::type_id::create("AES_in_reset_s");
    
    AES_in_agent_config.wait_for_reset();
    AES_in_agent_config.wait_for_num_clocks(10);

    repeat (10) AES_in_agent_random_seq.start(AES_in_agent_sequencer);
    AES_in_reset_s.start(AES_in_agent_sequencer);
    repeat (5) AES_in_agent_random_seq.start(AES_in_agent_sequencer);

    AES_in_agent_config.wait_for_num_clocks(50);    
    
    if (1) // TODO -- how to properly choose which to print?
        $display("* TESTCASE PASSED");
    else
        $display("* TESTCASE FAILED");
  endtask


endclass : AES_random_sequence

`endif
