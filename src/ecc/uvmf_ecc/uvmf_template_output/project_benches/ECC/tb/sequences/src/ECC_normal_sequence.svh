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


`ifndef __ECC_NORMAL_SEQUENCE
`define __ECCC_NORMAL_SEQUENCE

`include "uvm_macros.svh"

class ECC_normal_sequence #(int AHB_DATA_WIDTH = 64,
                            int AHB_ADDR_WIDTH = 32
                            ) extends ECC_bench_sequence_base;

  `uvm_object_utils(ECC_normal_sequence) 

  // Define type and handle for reset sequence
  typedef ECC_in_normal_sequence #(AHB_DATA_WIDTH, AHB_ADDR_WIDTH) ECC_in_normal_sequence_t;
  ECC_in_normal_sequence_t ECC_in_normal_s;
  
  // constructor
  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual task body();
    int iterations = 10;
    uvm_report_server report_server;
    if ($value$plusargs("ECC_TEST_ITERATIONS=%d", iterations) && (iterations <= 0))
      `uvm_fatal("ECC_TEST_ITERATIONS", "ECC_TEST_ITERATIONS must be positive")
    //ECC_in_agent_random_seq = ECC_in_random_sequence#()::type_id::create("ECC_in_agent_random_seq");
    ECC_in_normal_s = ECC_in_normal_sequence#()::type_id::create("ECC_in_normal_s");

    fork
      ECC_in_agent_config.wait_for_reset();
      ECC_out_agent_config.wait_for_reset();
    join

    //repeat (10) ECC_in_agent_random_seq.start(ECC_in_agent_sequencer);
    repeat (iterations) ECC_in_normal_s.start(ECC_in_agent_sequencer);
    //repeat (5) ECC_in_agent_random_seq.start(ECC_in_agent_sequencer);

    fork
      ECC_in_agent_config.wait_for_num_clocks(50);    
      ECC_out_agent_config.wait_for_num_clocks(50);
    join

    report_server = uvm_report_server::get_server();
    if ((report_server.get_severity_count(UVM_ERROR) == 0) &&
        (report_server.get_severity_count(UVM_FATAL) == 0))
        $display("* TESTCASE PASSED");
    else
        $display("* TESTCASE FAILED");
  endtask


endclass : ECC_normal_sequence

`endif
