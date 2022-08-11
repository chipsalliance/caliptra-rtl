// ==============================================================================
// =====            Mentor Graphics UK Ltd                                  =====
// =====            Rivergate, London Road, Newbury BERKS RG14 2QB          =====
// ==============================================================================
//! @file
//  Project                : SHA512_2019_4
//  Unit                   : SHA512_random_sequence
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


`ifndef __SHA512_RANDOM_SEQUENCE
`define __SHA512_RANDOM_SEQUENCE

`include "uvm_macros.svh"

class SHA512_random_sequence #(int AHB_DATA_WIDTH = 32,
                            int AHB_ADDR_WIDTH = 32,
                            bit BYPASS_HSEL = 0
                            ) extends SHA512_bench_sequence_base;

  `uvm_object_utils(SHA512_random_sequence) 

  // Define type and handle for reset sequence
  typedef SHA512_in_reset_sequence #(AHB_DATA_WIDTH, AHB_ADDR_WIDTH, BYPASS_HSEL) SHA512_in_reset_sequence_t;
  SHA512_in_reset_sequence_t SHA512_in_reset_s;
  
  // constructor
  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual task body();
    SHA512_in_agent_random_seq = SHA512_in_random_sequence#()::type_id::create("SHA512_in_agent_random_seq");
    SHA512_in_reset_s = SHA512_in_reset_sequence#()::type_id::create("SHA512_in_reset_s");
    
    SHA512_in_agent_config.wait_for_reset();
    SHA512_in_agent_config.wait_for_num_clocks(10);

    repeat (10) SHA512_in_agent_random_seq.start(SHA512_in_agent_sequencer);
    SHA512_in_reset_s.start(SHA512_in_agent_sequencer);
    repeat (5) SHA512_in_agent_random_seq.start(SHA512_in_agent_sequencer);

    SHA512_in_agent_config.wait_for_num_clocks(50);    
    
  endtask


endclass : SHA512_random_sequence

`endif
